// SPDX-FileCopyrightText: 2026 Fabian Januszewski, Abhijit (the Langlandscape team)
// SPDX-License-Identifier: LGPL-3.0-only WITH LicenseRef-CUDA-exception

// Langlandscape JL extension (WP HJ-6-min): the Brandt free-block reader and the reads on it.  See JlFreeBlockRead.h.
#include "JlFreeBlockRead.h"

#include <algorithm>
#include <cctype>
#include <chrono>
#include <cstdio>
#include <filesystem>
#include <fstream>
#include <numeric>
#include <sstream>
#include <stdexcept>
#include <utility>

#include "../../Integral/Descent/IsoTreeCarrierZ.h"
#include "../../../ModArithmetic/EngineCheck.h"

namespace hacs_jl {
namespace {

namespace loc = heckez::local;
namespace mx = integral_descent::modexport;

// ---- a minimal JSON reader (ConsoleCore's ServeJson is compiled only with OC_BUILD_NOTEBOOK=ON, so it is not linkable here) ----------
struct J {
    enum Kind { Null, Bool, Num, Str, Arr, Obj } kind = Null;
    std::string s;                                   // Num: source text; Str: value
    std::vector<J> a;
    std::vector<std::pair<std::string, J>> o;
    const J* get(const std::string& k) const {
        if (kind != Obj) return nullptr;
        for (const auto& m : o)
            if (m.first == k) return &m.second;
        return nullptr;
    }
};

class Parser {
public:
    explicit Parser(const std::string& t) : t_(t) {}
    bool parse(J& out, std::string* err) {
        try {
            value(out, 0);
            ws();
            if (i_ != t_.size()) fail("trailing text");
        } catch (const std::exception& e) {   // HJ-6b m1: std::stoul (bad \\u escape) throws invalid_argument / out_of_range
            if (err) *err = e.what();
            return false;
        }
        return true;
    }
private:
    const std::string& t_;
    size_t i_ = 0;
    [[noreturn]] void fail(const std::string& w) { throw std::runtime_error("json: " + w + " at offset " + std::to_string(i_)); }
    void ws() { while (i_ < t_.size() && (t_[i_] == ' ' || t_[i_] == '\n' || t_[i_] == '\r' || t_[i_] == '\t')) ++i_; }
    char peek() { ws(); if (i_ >= t_.size()) fail("unexpected end"); return t_[i_]; }
    void expect(char c) { if (peek() != c) fail(std::string("expected '") + c + "'"); ++i_; }
    std::string str() {
        expect('"');
        std::string r;
        while (true) {
            if (i_ >= t_.size()) fail("unterminated string");
            char c = t_[i_++];
            if (c == '"') break;
            if (c == '\\') {
                if (i_ >= t_.size()) fail("bad escape");
                char e = t_[i_++];
                switch (e) {
                    case 'n': r += '\n'; break;
                    case 't': r += '\t'; break;
                    case 'r': r += '\r'; break;
                    case 'b': r += '\b'; break;
                    case 'f': r += '\f'; break;
                    case 'u': {   // keep ASCII, replace the rest (no field we read needs non-ASCII)
                        if (i_ + 4 > t_.size()) fail("bad \\u");
                        const unsigned v = static_cast<unsigned>(std::stoul(t_.substr(i_, 4), nullptr, 16));
                        i_ += 4;
                        r += v < 128 ? static_cast<char>(v) : '?';
                        break;
                    }
                    default: r += e;
                }
            } else {
                r += c;
            }
        }
        return r;
    }
    void value(J& v, int depth) {
        if (depth > 64) fail("nesting too deep");
        const char c = peek();
        if (c == '{') {
            ++i_;
            v.kind = J::Obj;
            if (peek() == '}') { ++i_; return; }
            while (true) {
                std::string k = str();
                expect(':');
                J x;
                value(x, depth + 1);
                v.o.emplace_back(std::move(k), std::move(x));
                if (peek() == ',') { ++i_; continue; }
                expect('}');
                return;
            }
        }
        if (c == '[') {
            ++i_;
            v.kind = J::Arr;
            if (peek() == ']') { ++i_; return; }
            while (true) {
                J x;
                value(x, depth + 1);
                v.a.push_back(std::move(x));
                if (peek() == ',') { ++i_; continue; }
                expect(']');
                return;
            }
        }
        if (c == '"') { v.kind = J::Str; v.s = str(); return; }
        if (t_.compare(i_, 4, "true") == 0) { v.kind = J::Bool; v.s = "true"; i_ += 4; return; }
        if (t_.compare(i_, 5, "false") == 0) { v.kind = J::Bool; v.s = "false"; i_ += 5; return; }
        if (t_.compare(i_, 4, "null") == 0) { v.kind = J::Null; i_ += 4; return; }
        const size_t s = i_;
        while (i_ < t_.size() && (std::isdigit(static_cast<unsigned char>(t_[i_])) || t_[i_] == '-' || t_[i_] == '+' || t_[i_] == '.' ||
                                  t_[i_] == 'e' || t_[i_] == 'E'))
            ++i_;
        if (s == i_) fail("unexpected character");
        v.kind = J::Num;
        v.s = t_.substr(s, i_ - s);
    }
};

bool IsIntText(const std::string& s) {
    if (s.empty()) return false;
    size_t b = s[0] == '-' ? 1 : 0;
    if (b == s.size()) return false;
    for (size_t i = b; i < s.size(); ++i)
        if (!std::isdigit(static_cast<unsigned char>(s[i]))) return false;
    return true;
}
// an integer given as a JSON number or a decimal string
bool IntOf(const J* x, int64_t* out) {
    if (!x || (x->kind != J::Num && x->kind != J::Str) || !IsIntText(x->s) || x->s.size() > 18) return false;
    *out = std::stoll(x->s);
    return true;
}
const J* First(const J& o, std::initializer_list<const char*> keys, std::vector<std::string>* notes, const char* canonical) {
    for (const char* k : keys) {
        if (const J* x = o.get(k)) {
            if (notes && std::string(k) != canonical) notes->push_back(std::string("alias:") + k + "->" + canonical);
            return x;
        }
    }
    return nullptr;
}

std::string Hex16(uint64_t v) {
    char b[32];
    std::snprintf(b, sizeof b, "0x%016llx", static_cast<unsigned long long>(v));
    return b;
}

uint64_t FnvRowMajor(const std::vector<nf::BigInt>& F, uint32_t r) {
    std::vector<std::vector<nf::BigInt>> cols(r, std::vector<nf::BigInt>(r));
    for (uint32_t i = 0; i < r; ++i)
        for (uint32_t j = 0; j < r; ++j) cols[j][i] = F[size_t(i) * r + j];
    return integral_descent::freez::MatrixFnv(cols, r);
}

std::string JoinU(const std::vector<uint32_t>& v) {
    std::ostringstream o;
    for (size_t i = 0; i < v.size(); ++i) o << (i ? "," : "") << v[i];
    return o.str();
}
std::string Q(const std::string& s) {
    std::string r = "\"";
    for (char c : s) {
        if (c == '"' || c == '\\') r += '\\';
        r += c;
    }
    return r + "\"";
}

}  // namespace

std::string JlWord(const std::string& w) {
    std::string r = w;
    const std::string bad = "certified";
    for (size_t p; (p = r.find(bad)) != std::string::npos;) r.replace(p, bad.size(), "met(hacs_word)");
    return r;
}

uint64_t MazurNumber(uint32_t N) {
    if (N < 2) return 0;
    const uint64_t a = N - 1, g = std::gcd<uint64_t>(a, 12);
    return a / g;
}
uint32_t MazurValuation(uint32_t N, uint64_t ell) {
    uint64_t m = MazurNumber(N);
    uint32_t v = 0;
    while (m && m % ell == 0) { m /= ell; ++v; }
    return v;
}

bool ParseBrandtRecord(const std::string& text, const std::string& where, BrandtRecord* out, std::string* err) {
    J root;
    if (!Parser(text).parse(root, err)) return false;
    BrandtRecord R;
    R.where = where;
    // envelope {provenance, data}; the record at data.free_block_z (tolerant: top-level free_block_z, or the object itself)
    const J* data = root.get("data") ? root.get("data") : &root;
    if (const J* w = data->get("writer"); w && w->kind == J::Str) R.writer = w->s;
    const J* fb = data->get("free_block_z");
    if (!fb) fb = data->get("free_block");
    if (!fb && data->get("F")) fb = data;
    if (!fb || fb->kind != J::Obj) { *err = "no free_block_z record"; return false; }
    for (const J* s : {data->get("schema"), fb->get("schema")}) {
        // HJ-6b: v1 and v2 (v2 adds canonical / order_ties, ignored here like every unknown field; the reads are GL_h(Z)-invariant)
        if (s && (s->kind != J::Str || (s->s != "langlandscape_brandt/v1" && s->s != "langlandscape_brandt/v2"))) {
            *err = "schema is not langlandscape_brandt/v1 or v2";
            return false;
        }
    }
    if (!fb->get("schema") && !data->get("schema")) R.notes.push_back("schema:absent");
    // scalars: the record first, then data (Lane A's interim writer kept D/M/k at the top level)
    auto scalar = [&](std::initializer_list<const char*> keys, const char* canon, int64_t* v) {
        const J* x = First(*fb, keys, &R.notes, canon);
        if (!x) x = First(*data, keys, &R.notes, canon);
        return IntOf(x, v);
    };
    int64_t v = 0;
    if (!scalar({"D", "q", "disc"}, "D", &v) || v < 2) { *err = "D missing"; return false; }
    // HJ-6b m4: every narrowing to uint32 is range-checked (ENGINE_CHECK throws; the callers count it per file)
    auto u32 = [](int64_t x, const char* what) {
        ENGINE_CHECK_MSG(x >= 0 && x <= int64_t(UINT32_MAX), what);
        return static_cast<uint32_t>(x);
    };
    R.D = u32(v, "D out of uint32 range");
    R.M = scalar({"M"}, "M", &v) ? u32(v, "M out of uint32 range") : (R.notes.push_back("default:M=1"), 1u);
    R.k = scalar({"k"}, "k", &v) ? u32(v, "k out of uint32 range") : (R.notes.push_back("default:k=2"), 2u);
    ENGINE_CHECK_MSG(R.k >= 2, "k < 2");
    R.n = scalar({"n"}, "n", &v) ? u32(v, "n out of uint32 range") : R.k - 2;
    ENGINE_CHECK_MSG(uint64_t(R.D) * R.M <= UINT32_MAX, "D*M overflows uint32");
    R.N = scalar({"N"}, "N", &v) ? u32(v, "N out of uint32 range") : R.D * R.M;
    if (R.N != R.D * R.M) { *err = "N != D*M"; return false; }
    if (R.n + 2 != R.k) { *err = "n != k-2"; return false; }
    if (const J* s = fb->get("status"); s && s->kind == J::Str) R.status = s->s;
    else { R.status = "ok"; R.notes.push_back("default:status=ok"); }
    if (R.status == "no_integral_basis") { *err = "status no_integral_basis"; return false; }
    if (scalar({"d_algebra", "d", "d_target"}, "d_algebra", &v)) R.d_algebra = v;
    if (scalar({"e_eis", "r_eis"}, "e_eis", &v)) R.e_eis = v;
    if (const J* s = fb->get("basis_rule"); s && s->kind == J::Str) R.basis_rule = s->s;
    if (const J* s = fb->get("convention"); s && s->kind == J::Str) R.convention = s->s;
    // ops
    const J* ops = First(*fb, {"ops", "primes", "P"}, &R.notes, "ops");
    if (!ops || ops->kind != J::Arr) { *err = "ops missing"; return false; }
    for (const J& x : ops->a) {
        if (!IntOf(&x, &v) || v < 2) { *err = "ops: not an integer"; return false; }
        R.ops.push_back(u32(v, "op out of uint32 range"));
    }
    // F: per op nested rows of decimal strings (spec), or flat r*r (the interim writer); numbers tolerated
    const J* F = fb->get("F");
    if (!F || F->kind != J::Arr || F->a.size() != R.ops.size()) { *err = "F missing or not one matrix per op"; return false; }
    int64_t rr = -1;
    if (scalar({"rank", "r", "h"}, "rank", &v)) rr = v;
    for (size_t o = 0; o < F->a.size(); ++o) {
        std::vector<nf::BigInt> flat;
        const J& m = F->a[o];
        if (m.kind != J::Arr) { *err = "F[o] not an array"; return false; }
        bool nested = !m.a.empty() && m.a[0].kind == J::Arr;
        for (const J& row : m.a) {
            const std::vector<J> one{row};
            const std::vector<J>& ents = nested ? row.a : one;
            if (nested && row.kind != J::Arr) { *err = "F: ragged rows"; return false; }
            for (const J& e : ents) {
                if ((e.kind != J::Str && e.kind != J::Num) || !IsIntText(e.s)) { *err = "F: entry not a decimal integer"; return false; }
                flat.push_back(nf::BigInt::from_string(e.s));
            }
        }
        uint32_t r = 0;
        while (size_t(r) * r < flat.size()) ++r;
        if (size_t(r) * r != flat.size()) { *err = "F[o] not square"; return false; }
        if (nested && m.a.size() != r) { *err = "F[o]: row count != r"; return false; }
        if (o == 0) R.r = r;
        else if (r != R.r) { *err = "ops disagree on rank"; return false; }
        R.F.push_back(std::move(flat));
    }
    if (F->a.empty()) R.r = rr > 0 ? u32(rr, "rank out of uint32 range") : 0;
    if (rr >= 0 && rr != R.r) { *err = "rank field != sqrt(len F)"; return false; }
    // F_fnv: verify against HACS MatrixFnv
    const J* fnv = fb->get("F_fnv");
    for (size_t o = 0; o < R.F.size(); ++o) {
        R.F_fnv.push_back(FnvRowMajor(R.F[o], R.r));
        std::string w;
        if (fnv && fnv->kind == J::Arr && o < fnv->a.size() && fnv->a[o].kind == J::Str) w = fnv->a[o].s;
        R.F_fnv_json.push_back(w);
        if (w.empty()) R.notes.push_back("F_fnv:absent(op " + std::to_string(R.ops[o]) + ")");
        else if (w != Hex16(R.F_fnv[o])) ++R.fnv_mismatch;
    }
    if (const J* p = fb->get("proof"); p && p->kind == J::Arr)
        for (const J& x : p->a) R.proof.push_back(x.kind == J::Str ? x.s : "?");
    const J* g = First(*fb, {"gammas", "weights"}, &R.notes, "gammas");
    if (!g) g = First(*data, {"gammas", "weights"}, &R.notes, "gammas");   // the interim writer: data.weights = |Gamma_x|
    if (g && g->kind == J::Arr) {
        for (const J& x : g->a)
            if (IntOf(&x, &v) && v > 0) R.gammas.push_back(static_cast<uint64_t>(v));
        if (R.gammas.size() != R.r) R.gammas.clear();
    }
    if (R.d_algebra < 0) R.notes.push_back("d_algebra:absent(fallback rank)");
    if (R.e_eis < 0) R.notes.push_back("e_eis:absent(fallback 1 at k=2)");
    *out = std::move(R);
    return true;
}

std::vector<std::string> BrandtInputFiles(const std::string& path, std::string* err) {
    namespace fs = std::filesystem;
    std::vector<std::string> out;
    std::error_code ec;
    fs::path p(path);
    auto from_index = [&](const fs::path& idx) {
        std::ifstream in(idx);
        std::stringstream ss;
        ss << in.rdbuf();
        J root;
        std::string e;
        if (!Parser(ss.str()).parse(root, &e)) return false;
        // collect every string value naming a *.json file other than index.json (tolerant of the index layout)
        std::vector<const J*> st{&root};
        while (!st.empty()) {
            const J* x = st.back();
            st.pop_back();
            if (x->kind == J::Str && x->s.size() > 5 && x->s.compare(x->s.size() - 5, 5, ".json") == 0 &&
                fs::path(x->s).filename() != "index.json") {
                fs::path f = idx.parent_path() / fs::path(x->s).filename();
                if (fs::exists(f, ec)) out.push_back(f.string());
            }
            for (const J& y : x->a) st.push_back(&y);
            for (const auto& m : x->o) st.push_back(&m.second);
        }
        return !out.empty();
    };
    if (fs::is_regular_file(p, ec)) {
        if (p.filename() == "index.json") {
            if (!from_index(p)) p = p.parent_path();
            else goto done;
        } else {
            out.push_back(p.string());
            return out;
        }
    }
    if (fs::is_directory(p, ec)) {
        if (fs::exists(p / "index.json", ec) && from_index(p / "index.json")) goto done;
        for (const auto& e : fs::directory_iterator(p, ec))
            if (e.is_regular_file() && e.path().extension() == ".json" && e.path().filename() != "index.json")
                out.push_back(e.path().string());
    } else if (out.empty()) {
        *err = "JL_BRANDT_IN: not a file or directory: " + path;
    }
done:
    std::sort(out.begin(), out.end());
    out.erase(std::unique(out.begin(), out.end()), out.end());
    return out;
}

mx::FreeBlockZ ToFreeBlockZ(const BrandtRecord& R) {
    mx::FreeBlockZ G;
    G.basis_rule = R.basis_rule.empty() ? "-" : R.basis_rule;
    G.q0_key = "-";
    G.saturation = R.r == 0 ? "rank0" : "exact_basis";
    G.bound_basis = "-";
    G.F = R.F;
    G.F_fnv = R.F_fnv;
    G.proof = R.proof;
    G.lane_route = "cpu";
    return G;
}

mx::FreeBlockZ DoubledFreeBlockZ(const BrandtRecord& R) {
    mx::FreeBlockZ G = ToFreeBlockZ(R);
    const uint32_t r = R.r, r2 = 2 * r;
    G.F.clear();
    G.F_fnv.clear();
    for (const auto& F : R.F) {
        std::vector<nf::BigInt> X(size_t(r2) * r2, nf::BigInt(0));
        for (uint32_t i = 0; i < r; ++i)
            for (uint32_t j = 0; j < r; ++j) {
                X[size_t(i) * r2 + j] = F[size_t(i) * r + j];
                X[size_t(i + r) * r2 + j + r] = F[size_t(i) * r + j];
            }
        G.F_fnv.push_back(FnvRowMajor(X, r2));
        G.F.push_back(std::move(X));
    }
    G.basis_rule += " (+) itself (Langlandscape L+L for the at-root read)";
    return G;
}

namespace {

OwnRead OwnReads(const BrandtRecord& R, const loc::LatticeModule& M, uint32_t e) {
    OwnRead O;
    const size_t D = M.D;
    const loc::Zlk Z = loc::Zlk::Make(M.ell, M.K);
    const loc::Zlk F1 = loc::Zlk::Make(M.ell, 1);
    // rank / index data of T = Z[T_p : p in P] (x) Z/ell^K, as the subalgebra of End(L / ell^K) the operators generate
    {
        const loc::Span A = loc::AlgebraClosure(Z, M.T, D);
        O.T_len = A.length();
        O.T_gens = A.generators();
        std::vector<loc::Mat> T1 = M.T;
        for (auto& X : T1)
            for (auto& x : X) x = F1.red(x);
        O.A1_dim = loc::AlgebraClosure(F1, T1, D).length();
    }
    // the Eisenstein congruence module by Smith form: c_p = chi_p / (x - lambda_p)^e annihilates L_cusp, c_p(T_p) L = (c_p(lambda)/d) L_eis
    // with d = [L : L_eis (+) L_cusp]-ell-part, so eta = v(c_p(lambda)) - a_p (a_p = the Smith valuation of c_p(T_p)); every op agrees.
    if (e == 0) {   // k > 2 on the definite side: no Eisenstein system (HJ-B0 Sec. 7 item 1), only the rank / index data
        O.status = "no_eisenstein(e_eis=0)";
        return O;
    }
    std::ostringstream po;
    bool have = false, bad = false;
    for (size_t i = 0; i < M.P.size(); ++i) {
        const uint32_t p = M.P[i];
        uint64_t pk = 1 % Z.q;
        for (uint32_t t = 0; t < M.n + 1; ++t) pk = Z.mul(pk, p % Z.q);
        const uint64_t lam = Z.add(1 % Z.q, pk);   // 1 + p^{k-1} mod ell^K
        const loc::Poly chi = loc::Charpoly(Z, M.T[i], D);
        loc::Poly c;
        po << (i ? "|" : "") << p << ":";
        if (!loc::DivideByRoot(Z, chi, lam, e, &c)) {
            po << "not_exact";
            bad = true;
            continue;
        }
        const uint32_t v = Z.val(loc::PolyEval(Z, c, lam));
        po << "v=" << v;
        if (O.v_gP_local < 0 || int32_t(v) < O.v_gP_local) O.v_gP_local = int32_t(v);
        if (v >= M.K) { po << ":open(precision)"; continue; }
        const std::vector<uint32_t> a = loc::SmithValuations(Z, loc::MatPolyEval(Z, c, M.T[i], D), D, D);
        po << ":a=[" << JoinU(a) << "]";
        if (a.size() != e) { po << ":rank_mismatch"; bad = true; continue; }
        int32_t et = 0;
        for (uint32_t ai : a) et = std::max<int32_t>(et, int32_t(v) - int32_t(ai));
        po << ":eta=" << et;
        if (!have) { O.v_cong = et; have = true; }
        else if (et != O.v_cong) bad = true;
    }
    O.per_op = po.str();
    O.status = bad ? "inconsistent" : have ? "ok" : "open(precision)";
    // exact cross-check from the weights: phi = (L / |Gamma_c|)_c (primitive) is the left Eisenstein eigenvector of F (|G_j| F_ij = |G_i| F_ji),
    // L_cusp = ker phi, phi(L) = Z, so [L : L_eis (+) L_cusp] = phi(1,..,1) = sum_c L/|Gamma_c| / gcd.
    if (!R.gammas.empty()) {
        uint64_t L = 1;
        for (uint64_t g : R.gammas) L = std::lcm(L, g);
        uint64_t s = 0, g0 = 0;
        for (uint64_t g : R.gammas) { s += L / g; g0 = std::gcd(g0, L / g); }
        uint64_t idx = s / g0;
        int32_t vm = 0;
        while (idx % M.ell == 0) { idx /= M.ell; ++vm; }
        O.v_mass = vm;
    }
    return O;
}

void ReadJson(std::ostringstream& o, const loc::LocalRead& L) {
    o << "{\"D_lattice\":" << L.D << ",\"d\":" << L.d << ",\"P\":[" << JoinU(L.P) << "],\"t_ell\":" << Q(L.t_ell)
      << ",\"dim_A1\":" << L.dim_A1 << ",\"c3\":" << Q(JlWord(L.c3)) << ",\"mono\":" << Q(JlWord(L.mono)) << ",\"e\":" << L.e
      << ",\"e_op\":" << Q(L.e_op) << ",\"e_status\":" << Q(JlWord(L.e_status)) << ",\"p26\":" << Q(JlWord(L.p26)) << ",\"p26_op\":" << Q(L.p26_op)
      << ",\"eis_block_rank\":" << L.eis_block_rank << ",\"v_gP_local\":" << L.v_gP_local << ",\"v_gP\":" << L.v_gP << ",\"v_gP_source\":"
      << Q(L.v_gP_source) << ",\"v_eta\":" << L.v_eta << ",\"eta\":[" << JoinU(L.eta) << "],\"root\":" << Q(JlWord(L.root))
      << ",\"C_T\":" << Q(JlWord(L.C_T)) << ",\"roots\":\"";
    for (size_t i = 0; i < L.roots.size(); ++i) {
        const auto& r = L.roots[i];
        o << (i ? "|" : "") << r.op << ":" << r.annihilator << ":v=" << r.v_c_lambda << ":a=" << JoinU(r.a) << ":eta=" << JoinU(r.eta) << ":"
          << JlWord(r.status);
    }
    char b[24];
    std::snprintf(b, sizeof b, "%016llx", static_cast<unsigned long long>(L.digest()));
    o << "\",\"digest\":\"0x" << b << "\"}";
}

}  // namespace

JlRead RunJlRead(const BrandtRecord& R, uint64_t ell, uint32_t K, bool do_plain, bool do_LL) {
    const auto t0 = std::chrono::steady_clock::now();
    JlRead X;
    X.D = R.D; X.M = R.M; X.k = R.k; X.N = R.N; X.h = R.r; X.ell = ell; X.K = K;
    for (uint32_t p : R.ops)
        if (R.N % p) X.P.push_back(p);
    if (R.N % ell == 0) {
        X.lm_status = "skipped(ell|N)";
        return X;
    }
    // T_ell: ReadPrimes appends it when ell does not divide N; the record must carry it (else LatticeFromFreeZ's ENGINE_CHECK fires)
    std::string tw;
    std::vector<uint32_t> P = loc::ReadPrimes(R.N, ell, X.P, &tw);
    if (tw == "added" && std::find(R.ops.begin(), R.ops.end(), static_cast<uint32_t>(ell)) == R.ops.end()) {
        P = X.P;
        tw = "omitted(not_in_record)";
    }
    X.P = P;
    X.t_ell = tw;
    const uint32_t e = R.e_eis >= 0 ? static_cast<uint32_t>(R.e_eis) : (R.k == 2 ? 1u : 0u);
    const int64_t d = R.d_algebra >= 0 ? R.d_algebra : R.r;
    loc::ReadOptions opt;
    opt.d_target = d;
    opt.r_eis = e;
    opt.eis_rational = R.k == 2 && e == 1;
    opt.k_weight = R.k;
    opt.full_algebra = false;   // the read set omits T_p for p | N (anemic); ReadLocal does not read the field
    const mx::FreeBlockZ G = ToFreeBlockZ(R);
    loc::LatticeModule M = loc::LatticeFromFreeZ(R.N, R.n, ell, K, X.P, G, R.ops);
    M.t_ell = tw;
    X.lm_status = M.status;
    if (!M.ok) return X;
    if (R.r > 0) X.own = OwnReads(R, M, e);
    if (do_plain && R.r > 0) {
        X.plain = loc::ReadLocal(M, opt);
        X.ran_plain = true;
    }
    if (do_LL && R.r > 0 && opt.eis_rational) {
        const mx::FreeBlockZ G2 = DoubledFreeBlockZ(R);
        loc::LatticeModule M2 = loc::LatticeFromFreeZ(R.N, R.n, ell, K, X.P, G2, R.ops);
        M2.t_ell = tw;
        loc::ReadOptions o2 = opt;
        o2.r_eis = 2 * e;
        X.LL = loc::ReadLocal(M2, o2);
        X.ran_LL = true;
    }
    X.seconds = std::chrono::duration<double>(std::chrono::steady_clock::now() - t0).count();
    return X;
}

std::string JlRead::json() const {
    std::ostringstream o;
    o << "{\"schema\":\"jl_lattice_read/v1\",\"tag\":\"computed (HACS ReadLocal on a JL lattice)\",\"D\":" << D << ",\"M\":" << M
      << ",\"k\":" << k << ",\"N\":" << N << ",\"h\":" << h << ",\"ell\":" << ell << ",\"K\":" << K << ",\"P\":[" << JoinU(P)
      << "],\"t_ell\":" << Q(t_ell) << ",\"lattice_status\":" << Q(lm_status);
    const uint32_t vm = M == 1 ? MazurValuation(N, ell) : 0;
    if (M == 1) o << ",\"mazur_num\":" << MazurNumber(N) << ",\"v_mazur\":" << vm;
    o << ",\"own\":{\"status\":" << Q(own.status) << ",\"v_cong\":" << own.v_cong << ",\"v_mass\":" << own.v_mass
      << ",\"v_gP_local\":" << own.v_gP_local << ",\"T_gens\":" << own.T_gens << ",\"T_len\":" << own.T_len << ",\"hK\":" << h * K
      << ",\"A1_dim\":" << own.A1_dim << ",\"per_op\":" << Q(own.per_op) << "}";
    if (ran_LL) { o << ",\"readlocal_LL\":"; ReadJson(o, LL); }
    if (ran_plain) { o << ",\"readlocal_L\":"; ReadJson(o, plain); }
    char b[32];
    std::snprintf(b, sizeof b, "%.3f", seconds);
    o << ",\"wall_s\":" << b << "}";
    return o.str();
}

}  // namespace hacs_jl
