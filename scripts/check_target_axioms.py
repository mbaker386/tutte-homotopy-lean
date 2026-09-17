#!/usr/bin/env python3
"""Require actual transitive axiom output for both public theorem names."""
import argparse
from pathlib import Path
import re

ALLOWED = {'propext','Classical.choice','Quot.sound'}

def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument('log_directory', type=Path)
    args = parser.parse_args()
    expected = {
      'path-statement.log':'TutteFormalization.path_theorem',
      'homotopy-statement.log':'TutteFormalization.homotopy_theorem',
    }
    for filename, target in expected.items():
        text = (args.log_directory/filename).read_text()
        match = re.search(r"'"+re.escape(target)+r"' depends on axioms:\s*\[([^\]]*)\]", text)
        if not match:
            raise SystemExit(f"Missing theorem axiom output: {target}")
        axioms = {s.strip() for s in match.group(1).split(',') if s.strip()}
        if not axioms <= ALLOWED:
            raise SystemExit(f"Unapproved axiom dependency in {target}: {sorted(axioms-ALLOWED)}")
        print(f"PASS: {target}: {sorted(axioms)}")
    return 0

if __name__ == '__main__':
    raise SystemExit(main())
