#!/usr/bin/env python3
"""Std compatibility ledger.

Lists the stable inherent methods and trait impls of the std owned types that
hipstr mirrors, and checks them against hipstr's own rustdoc JSON.

    rustup component add rust-docs-json --toolchain nightly
    cargo +nightly rustdoc --all-features -- -Zunstable-options --output-format json
    python3 compat/ledger.py           # check: exit 1 on unlisted gaps
    python3 compat/ledger.py --list    # print every std item and its status

Statuses come from `compat/ledger.toml`:
an item std has, hipstr lacks and the ledger does not mark `n/a` (with a reason)
is a failure. Items hipstr has are `done` automatically.
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
    "c_str": [("alloc", "CString"), ("core", "CStr")],
    "os_str": [("std", "OsString"), ("std", "OsStr")],
    "path": [("std", "PathBuf"), ("std", "Path")],
    # `BString` dereferences to `Vec<u8>`
    "b_str": [("alloc", "Vec"), ("core", "[u8]")],
}
HIP = {
    "bytes": "Bytes",
    "str": "Utf8",
    "c_str": "CStr",
    "os_str": "OsStr",
    "path": "Path",
    "b_str": "BStr",
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
                        methods.setdefault(m["name"], f"{name}::{m['name']}")
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


def main():
    ledger = tomllib.load(open(os.path.join(ROOT, "compat/ledger.toml"), "rb"))
    methods, traits, deref = hip_items()
    list_all = "--list" in sys.argv
    failures = 0
    for fam, enc in HIP.items():
        smethods, straits = std_items(fam)
        have = methods.get(enc, set()) | methods.get("E", set())
        na = ledger.get(fam, {}).get("n/a", {})
        via = ledger.get(fam, {}).get("deref", [])
        owned, borrowed = FAMILIES[fam][0][1], FAMILIES[fam][1][1]
        for name, where in sorted(smethods.items()):
            on_borrowed = where.startswith(borrowed + "::")
            if name in have:
                st = "done"
            elif on_borrowed and name not in ledger.get(fam, {}).get("owned_only", []):
                st = "deref"  # reached through `Deref<Target = borrowed>`
            elif name in via:
                st = "deref"
            elif name in na:
                st = "n/a: " + na[name]
            else:
                st = "MISSING"
                failures += 1
            if list_all or st == "MISSING":
                print(f"{fam:7} method {where:40} {st}")
        if "--traits" in sys.argv:
            for t in sorted(straits):
                if straits[t] == owned:
                    print(f"{fam:7} trait  {t}")
    if failures:
        print(f"\n{failures} std method(s) neither implemented nor listed as n/a in compat/ledger.toml")
        sys.exit(1)
    print("std method parity: ok")


if __name__ == "__main__":
    main()
