"""Lean census: files, lines, declarations, sorry / axiom / native_decide tokens.

The source of the counts in EXTREMAL_VALUES.md, section "Lean census".

Comments (line `--`, nested block `/- ... -/`) and string literals are stripped
before counting, so prose that mentions `sorry` or `theorem` is not counted.
A declaration is counted when, after stripping, a line starts with optional
attributes (`@[...]`), optional modifiers (private, protected, noncomputable,
nonrec) and then the keyword `theorem` or `lemma`.

This is a source-level token count. It is not a build and it is not a
`#print axioms` audit.

Usage:
    python lean_census.py lean          # the table
    python lean_census.py --selftest    # planted-file test, must print PASS
"""
import re
import sys
import tempfile
from pathlib import Path


def strip(src: str) -> str:
    """Remove comments and string literals, keeping every newline."""
    out = []
    i, n, depth = 0, len(src), 0
    in_str = False
    while i < n:
        two = src[i:i + 2]
        if depth:
            if two == "/-":
                depth += 1
                i += 2
            elif two == "-/":
                depth -= 1
                i += 2
            else:
                if src[i] == "\n":
                    out.append("\n")
                i += 1
            continue
        if in_str:
            if src[i] == "\\":
                i += 2
                continue
            if src[i] == '"':
                in_str = False
            elif src[i] == "\n":
                out.append("\n")
            i += 1
            continue
        if two == "/-":
            depth = 1
            i += 2
        elif two == "--":
            while i < n and src[i] != "\n":
                i += 1
        elif src[i] == '"':
            in_str = True
            i += 1
        else:
            out.append(src[i])
            i += 1
    return "".join(out)


MODS = r"(?:(?:private|protected|noncomputable|nonrec)\s+)*"
ATTR = r"(?:@\[[^\]]*\]\s*)"
DECL = re.compile(r"^\s*" + ATTR + r"*" + MODS + r"(theorem|lemma)\s+\S", re.M)
# Same-line form only (`@[simp] theorem foo`): an attribute on the line above leaves the
# declaration line starting with `theorem`, which the older rule did count.
DECL_ATTR = re.compile(r"^[ \t]*(?:@\[[^\]\n]*\][ \t]*)+"
                       r"(?:(?:private|protected|noncomputable|nonrec)[ \t]+)*"
                       r"(theorem|lemma)[ \t]+\S", re.M)
DEF = re.compile(r"^\s*" + ATTR + r"*" + MODS + r"(def|abbrev|instance|structure|inductive)\b", re.M)
SORRY = re.compile(r"(?<![A-Za-z0-9_.'])sorry(?![A-Za-z0-9_'])")
AXIOM = re.compile(r"^\s*(?:private\s+)?axiom\s+\S", re.M)
NATIVE = re.compile(r"native_decide")

HDR = ("file", "lines", "theorem", "lemma", "defs", "sorry", "axiom", "native_decide",
       "raw 'sorry' strings")


def census(root):
    rows = []
    attr_prefixed = 0
    for f in sorted(Path(root).glob("*.lean")):
        if f.name == "lakefile.lean":
            continue
        raw = f.read_text(encoding="utf-8")
        code = strip(raw)
        kinds = [m.group(1) for m in DECL.finditer(code)]
        attr_prefixed += len(DECL_ATTR.findall(code))
        rows.append((f.name, raw.count("\n"), kinds.count("theorem"), kinds.count("lemma"),
                     len(DEF.findall(code)), len(SORRY.findall(code)), len(AXIOM.findall(code)),
                     len(NATIVE.findall(code)), len(re.findall(r"sorry", raw))))
    totals = [sum(r[i] for r in rows) for i in range(1, len(HDR))]
    return rows, totals, attr_prefixed


def main(root):
    rows, tot, attr_prefixed = census(root)
    print("| " + " | ".join(HDR) + " |")
    print("|" + "---|" * len(HDR))
    for r in rows:
        print("| " + " | ".join(str(x) for x in r) + " |")
    print("| **total (%d files)** | " % len(rows) + " | ".join(str(x) for x in tot) + " |")
    decls = tot[1] + tot[2]
    print("theorem+lemma declarations:", decls)
    print("of which the line starts with an attribute (`@[...] theorem`):", attr_prefixed)
    print("counted by the older rule (line starts with `theorem` or `private theorem`):",
          decls - attr_prefixed)


PLANT = "\n".join([
    "-- a comment that says sorry and theorem fake1 : True",
    "/- block /- nested sorry -/ axiom fakeAx : False -/",
    'def s : String := "sorry native_decide"',
    "theorem real1 : True := by sorry",
    "private lemma real2 : True := trivial",
    "axiom realAx : True",
    "@[simp] theorem real3 : (1:Nat) = 1 := by native_decide",
    "theorem sorry' : True := trivial",
    "",
])


def selftest():
    with tempfile.TemporaryDirectory() as d:
        (Path(d) / "Plant.lean").write_text(PLANT, encoding="utf-8")
        rows, tot, attr_prefixed = census(d)
    got = dict(zip(HDR[1:], tot))
    want = {"lines": 8, "theorem": 3, "lemma": 1, "defs": 1, "sorry": 1, "axiom": 1,
            "native_decide": 1, "raw 'sorry' strings": 5}
    ok = got == want and attr_prefixed == 1
    print("selftest got :", got, "attr-prefixed:", attr_prefixed)
    print("selftest want:", want, "attr-prefixed: 1")
    print("PASS" if ok else "FAIL")
    return 0 if ok else 1


if __name__ == "__main__":
    if len(sys.argv) != 2:
        sys.exit(__doc__)
    if sys.argv[1] == "--selftest":
        sys.exit(selftest())
    main(sys.argv[1])
