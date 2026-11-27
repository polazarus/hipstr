#!/usr/bin/env python3
"""Std compatibility ledger.

Lists the stable inherent methods and trait impls of the std owned types that
hipstr mirrors, and checks them against hipstr's own rustdoc JSON.

    rustup component add rust-docs-json --toolchain nightly
    cargo +nightly rustdoc --all-features -- -Zunstable-options --output-format json
    python3 compat/ledger.py           # check: exit 1 on gaps or a stale LEDGER.md
    python3 compat/ledger.py --write   # regenerate compat/LEDGER.md and UNSTABLE.md
    python3 compat/ledger.py --list    # print every std method and its status

`compat/ledger.toml` lists the std methods hipstr deliberately does not provide,
with the reason; any other std method hipstr lacks is a failure. The full
table, with each method's status, is kept in the repo as `compat/LEDGER.md`;
`compat/UNSTABLE.md` lists the std methods not stable at the MSRV, as
candidates for later (not checked: it follows the nightly).
"""
import glob
import json
import os
import subprocess
import sys
import tomllib

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

# hipstr family -> std types whose API it mirrors (owned, then borrowed)
FAMILIES = {
    "bytes": [("alloc", "Vec"), ("core", "[u8]")],
    "str": [("alloc", "String"), ("core", "str")],
    "cstr": [("alloc", "CString"), ("core", "CStr")],
    "os_str": [("std", "OsString"), ("std", "OsStr")],
    "path": [("std", "PathBuf"), ("std", "Path")],
    # `BString` dereferences to `Vec<u8>`
    "bstr": [("alloc", "Vec"), ("core", "[u8]")],
}
HIP = {
    "bytes": "Bytes",
    "str": "Utf8",
    "cstr": "CStr",
    "os_str": "OsStr",
    "path": "Path",
    "bstr": "BStr",
}


def sysroot_json(krate):
    sysroot = subprocess.check_output(
        ["rustc", "+nightly", "--print", "sysroot"], text=True
    ).strip()
    return json.load(open(os.path.join(sysroot, "share/doc/rust/json", krate + ".json")))


def ty(t):
    """Renders a rustdoc JSON type, roughly."""
    if t is None:
        return "?"
    (k, v), = t.items()
    if k == "resolved_path":
        args = v.get("args") or {}
        a = args.get("angle_bracketed", {}).get("args", [])
        parts = []
        for x in a:
            if "type" in x:
                parts.append(ty(x["type"]))
            elif "lifetime" in x:
                parts.append(x["lifetime"])
            elif "const" in x:
                parts.append(x["const"].get("expr", "N"))
        name = v["path"].split("::")[-1]
        return name + (f"<{', '.join(parts)}>" if parts else "")
    if k == "primitive":
        return v
    if k == "generic":
        return v
    if k == "borrowed_ref":
        return "&" + ("mut " if v["is_mutable"] else "") + ty(v["type"])
    if k == "slice":
        return f"[{ty(v)}]"
    if k == "array":
        return f"[{ty(v['type'])}; {v['len']}]"
    if k == "tuple":
        return "(" + ", ".join(ty(x) for x in v) + ")"
    if k == "raw_pointer":
        return "*" + ("mut " if v["is_mutable"] else "const ") + ty(v["type"])
    if k == "qualified_path":
        return ty(v["self_type"]) + "::" + v["name"]
    if k == "impl_trait":
        return "impl _"
    if k == "dyn_trait":
        return "dyn _"
    return k


def msrv():
    cargo = tomllib.load(open(os.path.join(ROOT, "Cargo.toml"), "rb"))
    return tuple(int(x) for x in cargo["package"]["rust-version"].split("."))


MSRV = msrv()


def stable(item):
    """Stable at the crate's MSRV."""
    s = item.get("stability")
    if s is None or not isinstance(s["level"], dict):
        return False
    since = s["level"]["stable"]["since"]
    if since == "CURRENT_RUSTC_VERSION":
        return False
    return tuple(int(x) for x in since.split(".")) <= MSRV


def stability(item):
    """`unstable (feature)` or `stable since X (feature)`, `None` if unknown."""
    s = item.get("stability")
    if s is None:
        return None
    if isinstance(s["level"], dict):
        since = s["level"]["stable"]["since"]
        if since == "CURRENT_RUSTC_VERSION":
            since = "next release"
        return f"stable since {since} (`{s['feature']}`)"
    return f"unstable (`{s['feature']}`)"


def find_type(d, name):
    idx = d["index"]
    if name.startswith("["):
        return None
    for v in idx.values():
        if v.get("name") == name and v.get("crate_id") == 0 and (
            "struct" in v["inner"] or "primitive" in v["inner"]
        ):
            return v
    raise KeyError(name)


def impls_of(d, name):
    idx = d["index"]
    if name == "[u8]":
        prim = [v for v in idx.values() if v.get("name") == "slice" and "primitive" in v["inner"]][0]
        return [idx[str(i)] for i in prim["inner"]["primitive"]["impls"]]
    t = find_type(d, name)
    inner = t["inner"].get("struct") or t["inner"].get("primitive")
    return [idx[str(i)] for i in inner["impls"]]


def is_self(impl, name):
    f = ty(impl["inner"]["impl"]["for"])
    base = name if name.startswith("[") else name
    return f.split("<")[0] == base or f == base or (name == "[u8]" and f in ("[T]", "[u8]"))


def future_items(fam):
    """Public std methods not stable at the MSRV: unstable or stabilized later."""
    stable_names = set(std_items(fam)[0])
    methods = {}
    for krate, name in FAMILIES[fam]:
        d = sysroot_json(krate)
        idx = d["index"]
        for impl in impls_of(d, name):
            im = impl["inner"]["impl"]
            if im.get("is_synthetic") or im.get("blanket_impl") is not None:
                continue
            if im["trait"] is not None or not is_self(impl, name):
                continue
            for i in im["items"]:
                m = idx.get(str(i))
                if not (m and "function" in m["inner"] and m["visibility"] == "public"):
                    continue
                st = stability(m)
                if st is None or stable(m) or m["name"] in stable_names:
                    continue
                inputs = m["inner"]["function"]["sig"]["inputs"]
                mutable = bool(inputs) and inputs[0][0] == "self" and ty(inputs[0][1]).startswith("&mut ")
                methods.setdefault(m["name"], (f"{name}::{m['name']}", mutable, st))
    return methods


def std_items(fam):
    methods, traits = {}, {}
    for krate, name in FAMILIES[fam]:
        d = sysroot_json(krate)
        idx = d["index"]
        for impl in impls_of(d, name):
            im = impl["inner"]["impl"]
            if im.get("is_synthetic") or im.get("blanket_impl") is not None:
                continue
            if im["trait"] is None:
                if not is_self(impl, name):
                    continue
                for i in im["items"]:
                    m = idx.get(str(i))
                    if m and "function" in m["inner"] and stable(m) and m["visibility"] == "public":
                        inputs = m["inner"]["function"]["sig"]["inputs"]
                        mutable = bool(inputs) and inputs[0][0] == "self" and ty(inputs[0][1]).startswith("&mut ")
                        methods.setdefault(m["name"], (f"{name}::{m['name']}", mutable))
            elif stable(impl):
                tr = ty({"resolved_path": im["trait"]})
                f = ty(im["for"])
                traits.setdefault(f"impl {tr} for {f}", name)
    return methods, traits


def hip_items():
    path = os.path.join(ROOT, "target/doc/hipstr.json")
    d = json.load(open(path))
    idx = d["index"]
    hip = [v for v in idx.values() if v.get("name") == "Hip" and "struct" in v["inner"]][0]
    methods = {}  # encoding -> names
    traits = []
    for i in hip["inner"]["struct"]["impls"]:
        impl = idx[str(i)]
        im = impl["inner"]["impl"]
        if im.get("is_synthetic") or im.get("blanket_impl") is not None:
            continue
        f = ty(im["for"])
        if im["trait"] is None:
            enc = f[len("Hip<"):].split(",")[0].split("::")[-1]
            for j in im["items"]:
                m = idx.get(str(j))
                if m and "function" in m["inner"] and m["visibility"] == "public":
                    methods.setdefault(enc, set()).add(m["name"])
        else:
            traits.append(f"impl {ty({'resolved_path': im['trait']})} for {f}")
    # trait impls where Hip is the trait argument (e.g. `PartialEq<Hip<..>> for str`)
    for v in idx.values():
        im = v["inner"].get("impl")
        if im and im["trait"] and v.get("crate_id") == 0 and "Hip<" in ty({"resolved_path": im["trait"]}):
            traits.append(f"impl {ty({'resolved_path': im['trait']})} for {ty(im['for'])}")
    deref = {"Bytes": "[u8]", "Utf8": "str", "CStr": "CStr", "OsStr": "OsStr", "Path": "Path"}
    return methods, traits, deref


# families whose values dereference mutably (copy-on-write)
DEREF_MUT = {"bytes", "str", "bstr"}


def statuses():
    """Yields (family, std method, status) for every stable std method."""
    ledger = tomllib.load(open(os.path.join(ROOT, "compat/ledger.toml"), "rb"))
    methods, _, _ = hip_items()
    for fam, enc in HIP.items():
        smethods, _ = std_items(fam)
        have = methods.get(enc, set()) | methods.get("E", set())
        na = ledger.get(fam, {}).get("n/a", {})
        borrowed = FAMILIES[fam][1][1]
        for name, (where, mutable) in sorted(smethods.items()):
            if name in have:
                st = "done"
            elif where.startswith(borrowed + "::") and not mutable:
                st = "deref"  # reached through `Deref<Target = borrowed>`
            elif where.startswith(borrowed + "::") and fam in DEREF_MUT:
                st = "deref"  # reached through `DerefMut` (copy-on-write)
            elif name in na:
                st = "n/a: " + na[name]
            else:
                st = "MISSING"
            yield fam, where, st


TITLES = {
    "bytes": "Byte strings (`HipByt`, `SmallByt`, `TinyByt`) vs `Vec<u8>` / `[u8]`",
    "str": "Strings (`HipStr`, `SmallStr`, `TinyStr`) vs `String` / `str`",
    "cstr": "C strings (`HipCStr`, `SmallCStr`, `TinyCStr`) vs `CString` / `CStr`",
    "os_str": "OS strings (`HipOsStr`, `SmallOsStr`, `TinyOsStr`) vs `OsString` / `OsStr`",
    "path": "Paths (`HipPath`, `SmallPath`, `TinyPath`) vs `PathBuf` / `Path`",
    "bstr": "bstr byte strings (`HipBStr`, …) vs `BString` (= `Vec<u8>`) / `[u8]`",
}


def render(rows):
    msrv = ".".join(map(str, MSRV))
    out = [
        "# Std method parity ledger",
        "",
        "<!-- generated by `python3 compat/ledger.py --write`; do not edit -->",
        "",
        f"Every stable (at the MSRV, {msrv}) inherent method of the std types each family",
        "mirrors, and how hipstr provides it:",
        "",
        "- **done**: an inherent method of the same name;",
        "- **deref**: a method of the borrowed type, reached through `Deref` (or, for",
        "  `&mut self` methods, the copy-on-write `DerefMut` of bytes, `str` and `BStr`);",
        "- **n/a**: deliberately not provided (reasons in `compat/ledger.toml`).",
        "",
    ]
    for fam in HIP:
        fam_rows = [r for r in rows if r[0] == fam]
        counts = {}
        for _, _, st in fam_rows:
            k = st.split(":")[0]
            counts[k] = counts.get(k, 0) + 1
        summary = ", ".join(f"{v} {k}" for k, v in sorted(counts.items()))
        out += [f"## {TITLES[fam]}", "", summary, "", "| std method | status |", "|---|---|"]
        out += [f"| `{where}` | {st} |" for _, where, st in fam_rows]
        out.append("")
    return "\n".join(out)


def render_future():
    """Candidates for later: std methods not stable at the MSRV."""
    methods, _, _ = hip_items()
    msrv = ".".join(map(str, MSRV))
    out = [
        "# Std methods not yet stable at the MSRV",
        "",
        "<!-- generated by `python3 compat/ledger.py --write`; do not edit -->",
        "",
        f"Unstable std methods, and those stabilized after the MSRV ({msrv}), of the",
        "types each family mirrors: candidates to implement once they are stable at",
        "the MSRV. Unlike `LEDGER.md`, this list follows the nightly used to generate",
        "it and is not checked by CI.",
        "",
        "- **done**: hipstr already has a method of that name;",
        "- **via deref**: a method of the borrowed type, available through `Deref`",
        "  once stable (`&mut self` ones only for bytes, `str` and `BStr`);",
        "- **candidate**: would need an implementation in hipstr.",
        "",
    ]
    for fam, enc in HIP.items():
        have = methods.get(enc, set()) | methods.get("E", set())
        borrowed = FAMILIES[fam][1][1]
        rows = []
        for name, (where, mutable, st) in sorted(future_items(fam).items()):
            if name in have:
                status = "done"
            elif where.startswith(borrowed + "::") and (not mutable or fam in DEREF_MUT):
                status = "via deref"
            else:
                status = "candidate"
            rows.append(f"| `{where}` | {st} | {status} |")
        out += [f"## {TITLES[fam]}", ""]
        if rows:
            out += ["| std method | stability | hipstr |", "|---|---|---|", *rows]
        else:
            out.append("None.")
        out.append("")
    return "\n".join(out)


def main():
    rows = list(statuses())
    path = os.path.join(ROOT, "compat/LEDGER.md")
    text = render(rows)
    if "--write" in sys.argv:
        open(path, "w").write(text)
        open(os.path.join(ROOT, "compat/UNSTABLE.md"), "w").write(render_future())
    if "--list" in sys.argv:
        for fam, where, st in rows:
            print(f"{fam:7} {where:40} {st}")
    if "--traits" in sys.argv:
        for fam in HIP:
            _, straits = std_items(fam)
            for t in sorted(straits):
                if straits[t] == FAMILIES[fam][0][1]:
                    print(f"{fam:7} trait  {t}")
    missing = [(f, w) for f, w, st in rows if st == "MISSING"]
    for fam, where in missing:
        print(f"{fam:7} {where:40} MISSING")
    if missing:
        print(f"\n{len(missing)} std method(s) neither implemented nor listed as n/a in compat/ledger.toml")
        sys.exit(1)
    if not os.path.exists(path) or open(path).read() != text:
        print("compat/LEDGER.md is out of date: run `python3 compat/ledger.py --write`")
        sys.exit(1)
    print("std method parity: ok")


if __name__ == "__main__":
    main()
