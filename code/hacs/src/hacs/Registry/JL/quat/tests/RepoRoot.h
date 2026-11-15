// SPDX-FileCopyrightText: 2026 Fabian Januszewski, Abhijit (the Langlandscape team)
// SPDX-License-Identifier: LGPL-3.0-only WITH LicenseRef-CUDA-exception
//
// The Langlandscape repository root for the standalone hacs_jl tests and tools (HJ-4a audit m1): __FILE__ may be
// absolute or relative to the compile directory, and the binary may run from anywhere. Tries, in order: the prefix of
// __FILE__ before "code/hacs/" (absolute, or relative to the current directory) and then the git top level of the
// current directory. Returns "" if none is a git checkout containing code/results.
#pragma once
#include <cstdio>
#include <string>
#include <vector>
#include <sys/stat.h>

namespace hacs_jl_test {

inline std::string run_capture(const std::string& cmd) {
    std::string out;
    FILE* p = popen(cmd.c_str(), "r");
    if (!p) return "";
    char buf[512];
    while (fgets(buf, sizeof buf, p)) out += buf;
    pclose(p);
    while (!out.empty() && (out.back() == '\n' || out.back() == '\r')) out.pop_back();
    return out;
}

inline std::string repo_root_guess(const std::string& file) {
    auto has_results = [](const std::string& r) {
        struct stat st;
        return !r.empty() && stat((r + "/code/results").c_str(), &st) == 0;
    };
    std::vector<std::string> cands;
    auto pos = file.find("code/hacs/");
    if (pos != std::string::npos) {
        std::string pre = file.substr(0, pos);
        if (pre.empty()) pre = ".";
        cands.push_back(pre);
    }
    cands.push_back(".");
    for (const auto& c : cands) {
        std::string g = run_capture("git -C '" + c + "' rev-parse --show-toplevel 2>/dev/null");
        if (has_results(g)) return g;
    }
    return "";
}

}  // namespace hacs_jl_test
