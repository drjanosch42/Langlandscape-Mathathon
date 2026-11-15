#!/usr/bin/env python3
"""tools/make_manifest.py (S01-X1a; plan/implementation/OVERVIEW.md §3.3): GENERATES lean/Langlandscape/lake-manifest.json.

Loads the import's manifest (lean/trace-formula-project-import/lean/lake-manifest.json of this checkout, a frozen file),
sets "name": "Langlandscape", appends exactly the path entry of GL2TF below and dumps it in Lake's format (indent 1).
The manifest is never hand-edited or deleted; it is regenerated only by this script, by the stage master, and
tools/pins.sha256 is updated in the same commit (`--pins` rewrites it). Never run Lake to produce the manifest.

usage: tools/make_manifest.py [--check] [--pins]
  --check  write nothing; exit 1 if lake-manifest.json differs from the generated content
  --pins   after writing, rewrite tools/pins.sha256 (lakefile.toml, lake-manifest.json, lean-toolchain)
"""
import hashlib
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
PROJ = os.path.dirname(HERE)
IMPORT_MANIFEST = os.path.join(PROJ, "..", "trace-formula-project-import", "lean", "lake-manifest.json")
OUT = os.path.join(PROJ, "lake-manifest.json")
PINNED = ["lakefile.toml", "lake-manifest.json", "lean-toolchain"]
PATH_ENTRY = {"type": "path", "scope": "", "name": "GL2TF", "manifestFile": "lake-manifest.json",
              "inherited": False, "dir": "../trace-formula-project-import/lean", "copy": False, "configFile": "lakefile.toml"}


def generate() -> str:
    with open(IMPORT_MANIFEST, encoding="utf-8") as fh:
        m = json.load(fh)
    assert m.get("version") == "1.3.0", m.get("version")
    assert all(p.get("type") == "git" for p in m["packages"]), "import manifest has a non-git entry"
    m["name"] = "Langlandscape"
    m["packages"].append(dict(PATH_ENTRY))
    return json.dumps(m, indent=1, ensure_ascii=False) + "\n"


def main(argv):
    text = generate()
    if "--check" in argv:
        with open(OUT, encoding="utf-8") as fh:
            ok = fh.read() == text
        print("make_manifest: " + ("OK, lake-manifest.json is the generated one" if ok else "DIFFERS from the generated content"))
        return 0 if ok else 1
    with open(OUT + ".tmp", "w", encoding="utf-8") as fh:
        fh.write(text)
    os.replace(OUT + ".tmp", OUT)
    print(f"make_manifest: wrote {OUT}")
    if "--pins" in argv:
        lines = []
        for f in PINNED:
            with open(os.path.join(PROJ, f), "rb") as fh:
                lines.append(f"{hashlib.sha256(fh.read()).hexdigest()}  {f}\n")
        with open(os.path.join(HERE, "pins.sha256"), "w", encoding="utf-8") as fh:
            fh.writelines(lines)
        print("make_manifest: wrote tools/pins.sha256")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
