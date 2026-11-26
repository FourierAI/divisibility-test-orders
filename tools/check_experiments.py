"""Run the paper's executable finite checks from their documented directory."""

from pathlib import Path
import subprocess
import sys


def main():
    data = Path(__file__).resolve().parents[1] / "anc"
    checks = sorted(data.glob("check_*.py")) + [data / "menu_transition_example.py"]
    for script in checks:
        print(f"Running {script.name}", flush=True)
        subprocess.run([sys.executable, "-B", script.name], cwd=data, check=True)
    print(f"Passed {len(checks)} finite checks.")


if __name__ == "__main__":
    main()
