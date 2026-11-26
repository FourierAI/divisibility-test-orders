"""Validate and render the theorem-by-theorem index for the frozen preprint."""

import argparse
import hashlib
import json
from pathlib import Path
import re
import tarfile


ROOT = Path(__file__).resolve().parents[1]
INVENTORY = ROOT / "proofs" / "claims.json"
INDEX = ROOT / "PROOFS.md"
ENV = re.compile(
    r"\\input\{([^}]+)\}|\\begin\{(theorem|lemma|proposition)\}"
    r"(?:\[[^\]]*\])?(.*?)\\end\{\2\}", re.S
)
SOURCE_DIGEST = "88510f239aa2bc8cac49aefdba555418cefd23b62f5d32aa3eab1d09b72e41e4"


def numbered_statements(archive):
    """Read TeX in include order, including the unlabeled Proposition 38."""
    if hashlib.sha256(archive.read_bytes()).hexdigest() != SOURCE_DIGEST:
        raise ValueError("The source archive does not match the reference preprint.")
    with tarfile.open(archive) as ar:
        contents = {m.name: ar.extractfile(m).read().decode() for m in ar.getmembers()
                    if m.isfile() and m.name.endswith(".tex")}

    def visit(name):
        for match in ENV.finditer(contents[name]):
            include, kind, body = match.groups()
            if include:
                yield from visit(include + ".tex")
            else:
                label = re.search(r"\\label\{([^}]+)\}", body)
                canonical = " ".join(body.split()).encode()
                yield {"kind": kind, "label": label[1] if label else None,
                       "source": name, "statement_sha256": hashlib.sha256(canonical).hexdigest()}

    return list(visit("screening_orders.tex"))


def locate(project, symbol):
    mod, sep, declaration = symbol.rpartition(".")
    source = ROOT / project / (mod.replace(".", "/") + ".lean")
    if not sep or not source.is_file():
        raise ValueError(f"No source for {symbol}")
    matches = [(i, line) for i, line in enumerate(source.read_text().splitlines(), 1)
               if re.match(r"(?:theorem|lemma) " + re.escape(declaration) + r"\b", line)]
    if len(matches) != 1:
        raise ValueError(f"Expected one declaration for {symbol}, found {len(matches)}")
    return f"{source.relative_to(ROOT).as_posix()}#L{matches[0][0]}"


def render(claims):
    lines = ["# Formal verification by numbered result", "",
             "The numbers and pages refer to the original 74-page manuscript. "
             "A partial entry identifies a proved step and the remaining mathematical work. "
             "Open entries have no corresponding formal proof of the stated result in this repository. Proposition 39 is indexed under its corrected positive-input statement, with the original signed-domain counterexample linked.", ""]
    for number, c in enumerate(claims, 1):
        if c["number"] != number or c["status"] not in ("open", "partial", "proved"):
            raise ValueError(f"Invalid entry {number}")
        if (c["status"] == "open") != (not c["evidence"]):
            raise ValueError(f"Evidence disagrees with status in entry {number}")
        if c["status"] != "proved" and not c["remaining"]:
            raise ValueError(f"Missing open obligation in entry {number}")
        lines += [f'<a id="claim-{number:02d}"></a>', "",
                  f'### {c["kind"].capitalize()} {number} · {c["title"]}', "",
                  f'Page {c["page"]}. Status **{c["status"]}**.', ""]
        if c["checked"]:
            lines += [c["checked"], ""]
        for project, symbol in c["evidence"]:
            url = locate(project, symbol)
            lines.append(f"- [`{symbol}`]({url})")
        if c["evidence"]:
            lines.append("")
        if c["remaining"]:
            lines += ["Remaining work — " + c["remaining"], ""]
    return "\n".join(lines)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--archive", type=Path, help="cross-check the original arXiv source bundle")
    parser.add_argument("--write", action="store_true", help="regenerate PROOFS.md")
    args = parser.parse_args()
    claims = json.loads(INVENTORY.read_text())
    if len(claims) != 41:
        raise ValueError("Expected 41 numbered statements")
    if args.archive:
        expected = numbered_statements(args.archive)
        recorded = [{k: c[k] for k in ("kind", "label", "source", "statement_sha256")} for c in claims]
        if recorded != expected:
            raise ValueError("The index differs from one or more manuscript statements")
    text = render(claims)
    if args.write:
        INDEX.write_text(text)
    elif INDEX.read_text() != text:
        raise ValueError("Regenerate PROOFS.md from the current formalizations")
    counts = {s: sum(c["status"] == s for c in claims) for s in ("proved", "partial", "open")}
    print(f"Checked {len(claims)} manuscript results. {counts}")


if __name__ == "__main__":
    main()
