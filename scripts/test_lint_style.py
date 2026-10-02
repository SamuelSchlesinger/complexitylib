"""Preserve native-evaluation detection while avoiding unnecessary lexing."""

import random
import unittest
from pathlib import Path
from unittest.mock import Mock, patch

import lint_style


def native_evaluation(text: str) -> bool:
    """Check in-memory source through the same entry point as the file linter."""
    path = Mock(spec=Path)
    path.read_text.return_value = text
    return lint_style.uses_native_evaluation(path)


class NativeEvaluationTests(unittest.TestCase):
    def test_forbidden_spellings_and_comment_separated_options(self):
        for text in (
            "example : True := by native_decide",
            "example : True := by decide +native",
            "native := true",
            "native/- nested /- comment -/ -/:=/- comment -/true",
            "native\n:=\ntrue",
            "Lean.ofReduceBool value proof",
            "Lean.ofReduceNat value proof",
            "-- permitted comment\nexample : True := by native_decide",
        ):
            with self.subTest(source=text):
                self.assertTrue(native_evaluation(text))

    def test_comments_literals_and_similar_names_are_not_violations(self):
        for text in (
            "-- native_decide\nexample : True := by trivial",
            "/- native := true /- ofReduceNat -/ ofReduceBool -/",
            'def text := "native_decide; decide +native; native := true"',
            'def text := "escaped \\\" native_decide"',
            "def letter := 'n' -- native_decide",
            "def native_method := 0",
            "native := false",
            "native_/- comment -/decide",
        ):
            with self.subTest(source=text):
                self.assertFalse(native_evaluation(text))

    def test_marker_free_source_does_not_need_the_lexer(self):
        with patch.object(lint_style, "lean_code") as lexer:
            self.assertFalse(native_evaluation("example : True := by trivial\n"))
            lexer.assert_not_called()

    def test_split_markers_cannot_appear_after_lexing(self):
        for marker in ("native", "ofReduceBool", "ofReduceNat"):
            for index in range(1, len(marker)):
                for separator in ('/- comment -/', '-- comment\n', '"literal"',
                                  "'x'", '/-', '"'):
                    text = marker[:index] + separator + marker[index:]
                    with self.subTest(source=text):
                        expected = lint_style.NATIVE_RE.search(lint_style.lean_code(text))
                        self.assertEqual(native_evaluation(text), expected is not None)

    def test_prefilter_agrees_with_full_scan(self):
        # Deterministic adversarial fragments exercise token boundaries,
        # comments, literals, and all spellings without rescanning the library.
        fragments = (
            "native", "native_decide", "+native", ":=", "true", "false",
            "ofReduceBool", "ofReduceNat", "x", " ", "\n", "'n'", "_",
            "/- native_decide /- nested -/ -/", "-- ofReduceBool\n",
            '"native := true"', '"escaped \\\" +native"', "/-", "-/",
        )
        generator = random.Random(0)
        for _ in range(500):
            text = "".join(generator.choices(fragments, k=12))
            expected = lint_style.NATIVE_RE.search(lint_style.lean_code(text)) is not None
            with self.subTest(source=text):
                self.assertEqual(native_evaluation(text), expected)


if __name__ == "__main__":
    unittest.main()
