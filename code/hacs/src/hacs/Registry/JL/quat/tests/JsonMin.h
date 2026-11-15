// SPDX-FileCopyrightText: 2026 Fabian Januszewski, Abhijit (the Langlandscape team)
// SPDX-License-Identifier: LGPL-3.0-only WITH LicenseRef-CUDA-exception
//
// Minimal JSON reader for the hacs_jl standalone tests (a copy of the reader in quat_selftest.cpp, which is left
// untouched). Reads code/results JSON only (trusted, repository-internal input).
#pragma once
#include <cctype>
#include <map>
#include <stdexcept>
#include <string>
#include <vector>

namespace hacs_jl_test {

struct JV {
    enum T { Null, Bool, Num, Str, Arr, Obj } t = Null;
    std::string s;  // number text or string
    bool b = false;
    std::vector<JV> a;
    std::map<std::string, JV> o;
    const JV& operator[](const std::string& k) const {
        auto it = o.find(k);
        if (it == o.end()) throw std::runtime_error("json: missing key " + k);
        return it->second;
    }
    const JV& operator[](size_t i) const { return a.at(i); }
    bool has(const std::string& k) const { return o.count(k) > 0; }
    long long i() const { return std::stoll(s); }
};

class JParser {
public:
    explicit JParser(const std::string& txt) : t_(txt) {}
    JV parse() {
        JV v = value();
        ws();
        return v;
    }

private:
    const std::string& t_;
    size_t p_ = 0;
    void ws() {
        while (p_ < t_.size() && std::isspace((unsigned char)t_[p_])) ++p_;
    }
    char peek() {
        ws();
        if (p_ >= t_.size()) throw std::runtime_error("json: eof");
        return t_[p_];
    }
    std::string str() {
        ++p_;  // opening quote
        std::string out;
        while (t_[p_] != '"') {
            if (t_[p_] == '\\') {
                ++p_;
                char c = t_[p_];
                if (c == 'n') out += '\n';
                else if (c == 't') out += '\t';
                else if (c == 'u') {
                    out += '?';
                    p_ += 4;
                } else out += c;
            } else out += t_[p_];
            ++p_;
        }
        ++p_;
        return out;
    }
    JV value() {
        char c = peek();
        JV v;
        if (c == '{') {
            v.t = JV::Obj;
            ++p_;
            if (peek() == '}') {
                ++p_;
                return v;
            }
            for (;;) {
                peek();
                std::string k = str();
                if (peek() != ':') throw std::runtime_error("json: expected :");
                ++p_;
                v.o[k] = value();
                char d = peek();
                ++p_;
                if (d == '}') break;
                if (d != ',') throw std::runtime_error("json: expected , in object");
            }
        } else if (c == '[') {
            v.t = JV::Arr;
            ++p_;
            if (peek() == ']') {
                ++p_;
                return v;
            }
            for (;;) {
                v.a.push_back(value());
                char d = peek();
                ++p_;
                if (d == ']') break;
                if (d != ',') throw std::runtime_error("json: expected , in array");
            }
        } else if (c == '"') {
            v.t = JV::Str;
            v.s = str();
        } else if (t_.compare(p_, 4, "true") == 0) {
            v.t = JV::Bool;
            v.b = true;
            p_ += 4;
        } else if (t_.compare(p_, 5, "false") == 0) {
            v.t = JV::Bool;
            p_ += 5;
        } else if (t_.compare(p_, 4, "null") == 0) {
            p_ += 4;
        } else {
            v.t = JV::Num;
            size_t q = p_;
            while (q < t_.size() && (std::isdigit((unsigned char)t_[q]) || t_[q] == '-' || t_[q] == '+' || t_[q] == '.' ||
                                     t_[q] == 'e' || t_[q] == 'E'))
                ++q;
            v.s = t_.substr(p_, q - p_);
            p_ = q;
        }
        return v;
    }
};

}  // namespace hacs_jl_test
