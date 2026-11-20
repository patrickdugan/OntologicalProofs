"""Regression checks for failures that the spectral audit must reject."""

import unittest

from check_recursive_spectral import audit_output, declarations


class SpectralAuditTests(unittest.TestCase):
    def test_standard_wrapped_report(self):
        output = "'M.t' depends on axioms: [propext,\n Classical.choice, Quot.sound]"
        self.assertEqual(audit_output(["M.t"], output), [])

    def test_axiom_free_report(self):
        self.assertEqual(audit_output(["M.t"], "'M.t' does not depend on any axioms"), [])

    def test_missing_report(self):
        self.assertTrue(audit_output(["M.t"], ""))

    def test_duplicate_report(self):
        report = "'M.t' does not depend on any axioms\n"
        self.assertTrue(audit_output(["M.t"], report * 2))

    def test_arbitrary_extra_dependency(self):
        for extra in ("sorryAx", "ofReduceBool", "M.unprovedAssumption"):
            with self.subTest(extra=extra):
                self.assertTrue(audit_output(["M.t"], f"'M.t' depends on axioms: [{extra}]"))

    def test_unexpected_report(self):
        self.assertTrue(audit_output([], "'M.t' does not depend on any axioms"))

    def test_lean_error_alongside_report(self):
        output = "'M.t' does not depend on any axioms\nfile.lean:2:1: error: unknown constant"
        self.assertTrue(audit_output(["M.t"], output))

    def test_all_named_declarations(self):
        source = "namespace M\ndef x := 1\n@[simp] theorem t : x = 1 := rfl\nend M\n"
        self.assertEqual(declarations("M", source), ["M.x", "M.t"])

    def test_prohibited_source_tokens(self):
        for token in ("sorry", "admit", "axiom", "unsafe", "native_decide"):
            with self.subTest(token=token), self.assertRaises(ValueError):
                declarations("M", f"namespace M\ntheorem t : True := by {token}\nend M")

    def test_namespace_mismatch(self):
        with self.assertRaises(ValueError):
            declarations("M", "namespace N\ndef x := 1\nend N")

    def test_unsupported_declarations_are_rejected(self):
        for decl in ("structure S where", "inductive T", "class C where",
                     "@[simp] private theorem hidden : True := trivial"):
            with self.subTest(decl=decl), self.assertRaises(ValueError):
                declarations("M", f"namespace M\ndef x := 1\n{decl}\nend M")

    def test_unnamed_instances_are_rejected(self):
        for prefix in (":", "(n : Nat)", "{n : Nat}", "[Nonempty Nat]"):
            with self.subTest(prefix=prefix), self.assertRaises(ValueError):
                declarations("M", f"namespace M\ndef x := 1\ninstance {prefix} Foo := bar\nend M")

    def test_named_instance_is_audited(self):
        source = "namespace M\ninstance cubeFintype (n : Nat) : Fintype (Cube n) := by infer_instance\nend M"
        self.assertEqual(declarations("M", source), ["M.cubeFintype"])


if __name__ == "__main__":
    unittest.main()
