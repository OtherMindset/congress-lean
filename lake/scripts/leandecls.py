"""List the names a Lean 4 file declares, skipping comments, strings and docstrings.

Covers def, theorem, lemma, abbrev, structure, inductive, class, opaque, axiom,
instance with an explicit name, and namespace prefixes (namespace ... end, _root_).
private declarations are reported but flagged, since they cannot clash across modules.
"""
import re, sys, json

KEYWORDS = ("def", "theorem", "lemma", "abbrev", "structure", "inductive", "class",
            "opaque", "axiom", "instance")
MODS = {"private", "protected", "noncomputable", "partial", "unsafe", "nonrec", "scoped", "local"}
IDENT = r"[A-Za-z_À-ɏͰ-Ͽἀ-῿℀-⅏][A-Za-z0-9_'!?À-ɏͰ-Ͽἀ-῿₀-ₜ℀-⅏]*"
NAME = rf"(?:«[^»]*»|{IDENT})(?:\.(?:«[^»]*»|{IDENT}))*"


def strip(src: str) -> str:
    """Blank out comments, docstrings, strings and char literals, keeping newlines."""
    out = []
    i, n = 0, len(src)
    depth = 0
    while i < n:
        c = src[i]
        if depth:
            if src.startswith("/-", i):
                depth += 1; out.append("  "); i += 2
            elif src.startswith("-/", i):
                depth -= 1; out.append("  "); i += 2
            else:
                out.append("\n" if c == "\n" else " "); i += 1
            continue
        if src.startswith("/-", i):
            depth = 1; out.append("  "); i += 2; continue
        if src.startswith("--", i):
            j = src.find("\n", i)
            j = n if j < 0 else j
            out.append(" " * (j - i)); i = j; continue
        if c == '"':
            j = i + 1
            while j < n and src[j] != '"':
                j += 2 if src[j] == "\\" else 1
            seg = src[i:j + 1]
            out.append("".join("\n" if ch == "\n" else " " for ch in seg)); i = j + 1; continue
        if c == "'" and (i == 0 or not re.match(r"[A-Za-z0-9_'!?.]", src[i - 1])):
            m = re.match(r"'(?:\\.|\\x[0-9a-fA-F]{2}|\\u\{[0-9a-fA-F]+\}|[^\\'\n])'", src[i:])
            if m:
                out.append(" " * len(m.group(0))); i += len(m.group(0)); continue
        out.append(c); i += 1
    return "".join(out)


def declarations(src: str):
    """Return [(full_name, keyword, private, line)]."""
    s = strip(src)
    ns = []          # stack of ("namespace", parts) / ("section", name)
    decls = []
    tok_re = re.compile(
        rf"^[ \t]*(?:@\[[^\]]*\][ \t\n]*)*((?:(?:{'|'.join(MODS)})[ \t\n]+)*)"
        rf"(namespace|section|end|{'|'.join(KEYWORDS)})\b[ \t]*({NAME})?", re.M)
    for m in tok_re.finditer(s):
        mods, kw, name = m.group(1).split(), m.group(2), m.group(3)
        line = s.count("\n", 0, m.start()) + 1
        if kw == "namespace":
            ns.append(("namespace", name.split(".")))
        elif kw == "section":
            ns.append(("section", name))
        elif kw == "end":
            if ns:
                ns.pop()
        else:
            if kw == "instance" and (not name or name in ("priority",)):
                continue  # anonymous instance
            if not name:
                continue
            if kw == "instance":
                # `instance foo : T` has a name; `instance : T` does not (handled above)
                pass
            parts = [p for k, v in ns if k == "namespace" for p in v]
            if name.startswith("_root_."):
                full = name[len("_root_."):]
            else:
                full = ".".join(parts + [name])
            decls.append((full, kw, "private" in mods, line))
    return decls


if __name__ == "__main__":
    for path in sys.argv[1:]:
        for d in declarations(open(path, encoding="utf-8").read()):
            print(path, *d, sep="\t")
