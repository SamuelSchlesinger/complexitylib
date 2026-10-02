"""Keep environment-lint coverage, isolation, and failure propagation intact."""

import subprocess
import unittest
from unittest.mock import call, patch

import lint_environment
from lint_style import BUILD_ROOTS


class EnvironmentLintTests(unittest.TestCase):
    @patch("builtins.print")
    @patch("lint_environment.subprocess.run")
    def test_runs_every_root_in_a_separate_process(self, run, _print):
        lint_environment.main()
        self.assertEqual(run.call_args_list, [
            call(["runLinter", root], check=True) for root in BUILD_ROOTS
        ])

    @patch("builtins.print")
    @patch("lint_environment.subprocess.run")
    def test_first_failure_stops_the_gate(self, run, _print):
        error = subprocess.CalledProcessError(1, ["runLinter", BUILD_ROOTS[1]])
        run.side_effect = [None, error]
        with self.assertRaises(subprocess.CalledProcessError) as raised:
            lint_environment.main()
        self.assertIs(raised.exception, error)
        self.assertEqual(run.call_count, 2)


if __name__ == "__main__":
    unittest.main()
