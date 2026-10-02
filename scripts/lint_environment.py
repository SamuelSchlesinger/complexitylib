#!/usr/bin/env python3
"""Run all required environment linters in fresh processes under one Lake environment.

Build the required roots and `runLinter` first, then run from the repository root:
  lake env python3 scripts/lint_environment.py

Each invocation retains the upstream linter's original import environment and
checks, including slow linters and validation-only declarations. Separate
processes release each environment before loading the next, without changing
the imports or attributes visible to any individual lint run.
"""

import subprocess

from lint_style import BUILD_ROOTS


def main() -> None:
    for module in BUILD_ROOTS:
        print(f"Environment lint: {module}", flush=True)
        subprocess.run(["runLinter", module], check=True)


if __name__ == "__main__":
    main()
