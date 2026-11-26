"""Rebuild or verify the stand-alone edition of the standard-library proofs."""

import argparse
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def generate(project):
    imports = set()
    bodies = {}
    visited = set()

    def visit(name):
        if name in visited:
            return
        visited.add(name)
        body = []
        for line in (project / (name.replace(".", "/") + ".lean")).read_text().splitlines():
            if line.startswith("import "):
                dep = line.split()[1]
                if dep == "Screening" or dep.startswith("Screening."):
                    visit(dep)
                else:
                    imports.add(dep)
            else:
                body.append(line)
        if name != "Screening":
            bodies[name] = "\n".join(body).strip()

    visit("Audit")
    for source in (project / "Screening").glob("*.lean"):
        if f"Screening.{source.stem}" not in bodies:
            raise ValueError(f"Module not imported by the audit: {source.name}")
    pieces = ["\n".join("import " + dep for dep in sorted(imports)),
              "/-! Standard-library proofs from Learning Divisibility Test Orders from the "
              "Largest Hits. Generated with tools/standalone.py. See PROOFS.md for coverage. -/"]
    for module, body in bodies.items():
        pieces.extend([f"/- Source module: {module} -/", body])
    return "\n\n".join(pieces) + "\n"


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write", action="store_true", help="regenerate FirstPaperProofs.lean")
    args = parser.parse_args()
    target = ROOT / "FirstPaperProofs.lean"
    contents = generate(ROOT / "lean")
    if args.write:
        target.write_text(contents)
    elif target.read_text() != contents:
        raise ValueError("Regenerate FirstPaperProofs.lean with --write.")
