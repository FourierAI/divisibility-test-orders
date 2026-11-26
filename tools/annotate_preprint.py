"""Produce a linked TeX edition of the reference manuscript from its source archive."""

import argparse
from collections import Counter, defaultdict
import json
from pathlib import Path
import re
import tarfile

from proof_index import ENV, INVENTORY, numbered_statements


REPOSITORY = "https://github.com/FourierAI/divisibility-test-orders"


def annotate(archive, destination, revision):
    if not re.fullmatch(r"[0-9a-f]{40}", revision):
        raise ValueError("Use a full, immutable Git commit hash.")
    statements = numbered_statements(archive)
    claims = json.loads(INVENTORY.read_text())
    if len(statements) != len(claims) or any(
        any(row[key] != claim[key] for key in row)
        for row, claim in zip(statements, claims)
    ):
        raise ValueError("The proof inventory does not match the manuscript.")
    destination.mkdir(parents=True, exist_ok=True)
    if any(destination.iterdir()):
        raise ValueError("Use an empty output directory for the annotated edition.")
    with tarfile.open(archive) as bundle:
        for entry in bundle:
            if not entry.isfile():
                continue
            target = destination / entry.name
            if not target.resolve().is_relative_to(destination.resolve()):
                raise ValueError(f"Invalid archive path: {entry.name}")
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(bundle.extractfile(entry).read())

    groups = defaultdict(list)
    for claim in claims:
        groups[claim["source"]].append(claim)
    for name, rows in groups.items():
        source = destination / name
        local = iter(rows)
        def add_record(match):
            if match[1]:
                return match[0]
            row = next(local)
            statement = match[0]
            record = r"\paperLeanRef{%02d}{%s}" % (row["number"], row["status"])
            if row["number"] == 39:
                old = "consecutive odd integers with largest value"
                if statement.count(old) != 1:
                    raise ValueError("The reference wording of Proposition 39 has changed.")
                statement = statement.replace(old, "consecutive positive odd integers with largest value")
                record += ("\n" + r"\par\noindent{\footnotesize\emph{Correction to the original edition.} "
                           r"The original statement omitted positivity. Let \(M\) be the product "
                           r"of the \(m\) odd menu primes and take the two equiprobable inputs "
                           r"\(-3M,-3M+2\). With proper divisibility defined using absolute value, "
                           r"each test has hit probability \(1/2\). At fallback cost \(3\), the rule "
                           r"costs \((m+4)/2\) whereas one test attains the optimum \(5/2\). "
                           r"The positive support in the main arithmetic model already excludes these inputs.}\par")
            return statement + "\n" + record
        source.write_text(ENV.sub(add_record, source.read_text()))
        if next(local, None) is not None:
            raise ValueError(f"Missing statement in {name}")

    index_url = f"{REPOSITORY}/blob/{revision}/PROOFS.md"
    counts = Counter(c["status"] for c in claims)
    # The hash in the URI is a literal PDF fragment, distinct from macro parameter #1.
    macro = (r"\newcommand{\paperLeanRef}[2]{\par\noindent{\footnotesize"
             r"\href{" + index_url + r"\#claim-#1}{Lean record #1 (#2)}}\par}" + "\n")
    (destination / "lean_verification.tex").write_text(macro)
    main = destination / "screening_orders.tex"
    original = main.read_text()
    marker = r"\section*{Use of generative AI}"
    preamble = r"\begin{document}"
    if original.count(marker) != 1 or original.count(preamble) != 1:
        raise ValueError("Unexpected document structure.")
    section = (
        "\\section*{Code and formal verification}\n"
        "Each numbered result links to a record at the same version of the code. "
        f"Of the {len(claims)} results, {counts['proved']} have a complete proof in Lean, "
        f"{counts['partial']} have formal proofs of specified steps, and {counts['open']} "
        "remain open. Proposition 39 is counted in its corrected positive-input formulation. "
        "Each partial record states its outstanding obligations. "
        "The index cites the page numbers of the original edition. "
        "The repository also contains the four-prime example, the finite checks, "
        "the benchmark programs, and their recorded measurements. "
        f"\\href{{{index_url}}}{{Verification index and source code}}.\n\n"
    )
    main.write_text(original.replace(preamble, r"\input{lean_verification}" + "\n" + preamble)
                    .replace(marker, section + marker))


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("archive", type=Path)
    parser.add_argument("destination", type=Path)
    parser.add_argument("revision", help="Git commit containing the corresponding PROOFS.md")
    args = parser.parse_args()
    annotate(args.archive, args.destination, args.revision)
