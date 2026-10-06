#!/usr/bin/env python3
"""Validates: selected inventory declarations exist and report only standard axioms.

Run from any directory. This imports existing Lean build artifacts; it does not
rebuild the library, prove source/artifact freshness, or replace repository gates.
The complete compiler output is written beside this script as check-output.txt.
"""

from pathlib import Path
import re
import subprocess
import tempfile


ROOT = Path(__file__).resolve().parents[4]
EXPECTED = "b030149cd09f755bfead55f473d670f0880eedb0"
SOURCE_PATHS = [
    "Complexitylib/", "blueprint/", "ROADMAP.md", "lean-toolchain",
    "lakefile.toml", "lake-manifest.json",
]
DECLARATIONS = [
    "Algebraic.MCSP.mcspScalar",
    "Algebraic.MCSP.mcspCostScalar",
    "Algebraic.MCSP.card_yesSet_le_sharpBudget",
    "Algebraic.MCSP.mcspCostScalar_deMorgan_essentialAt",
    "Algebraic.MCSP.mcspScalar_binary_comp_tableTranslate",
    "Algebraic.MCSP.mcspTarget_binary_size_lower_bound",
    "Algebraic.MCSP.mcspCostTarget_deMorgan_binaryCost_lower_bound",
    "Algebraic.MCSP.costComplexity_muxTarget_self",
    "Algebraic.MCSP.costComplexity_muxTarget_ge_add_one",
    "Algebraic.MCSP.mcspCostScalar_pairTruthTable_left_eq_true_iff",
    "Algebraic.MCSP.mcspCostScalar_pairTruthTable_right_eq_true_iff",
    "Algebraic.MCSP.mcsp_singleCut_card_exactCostSet_le",
    "Algebraic.MCSP.sensitiveCoordinates_mcsp_pairTruthTable_eq_univ",
    "Algebraic.MCSP.mcsp_formula_leaves_lower_bound",
    "Algebraic.MCSP.mcsp_sharedGateCount_cost_lower_bound",
    "Algebraic.MCSP.mcsp_binaryFormula_leavesIn_leftBlock_lower_bound",
    "Algebraic.MCSP.exactCostSet_deMorgan_one_nonempty",
    "Algebraic.MCSP.mcspCostTarget_deMorgan_one_size_lower_bound",
    "Complexity.MCSP.Instance.length_encode",
    "Complexity.MCSP.mem_encode_iff_sizeComplexity_le",
    "Complexity.MCSP.mem_atThreshold_encode_iff",
    "Complexity.MCSP.mem_rawAtThreshold_tableBits_iff",
    "Complexity.MCSP.shannon_threshold_window",
    "Complexity.MCSP.rawWitnessRelation_polyBalanced",
    "Complexity.GapMCSP.rawSliceProblem_mapReducesVia_rawToCanonical",
    "Complexity.Circuit.size_toStraightLine",
    "Complexity.SchnorrDeMorgan.Translation.cost_eq",
    "Complexity.Frontier.RectangleFree",
    "Complexity.Frontier.lowerBound_gaussian",
    "Complexity.Frontier.sourceReductionHardFamily_lt_innerSize_gaussian",
    "Complexity.GapMCSP.Magnification.DenominatorConstant.HasMagnificationLowerBoundHypothesis",
    "Complexity.GapMCSP.Magnification.AntiCheckerLemma.hasGenerators_of_hasApproximateCounterFamilies",
]
AXIOM_DECLARATIONS = [
    DECLARATIONS[i] for i in (5, 6, 8, 9, 11, 13, 14, 29, 31)
]
IMPORTS = [
    "Complexitylib.Algebraic.LowerBound.MCSP",
    "Complexitylib.Metacomplexity.MCSP",
    "Complexitylib.Metacomplexity.MCSP.Raw",
    "Complexitylib.Metacomplexity.MCSP.Shannon",
    "Complexitylib.Metacomplexity.MCSP.Magnification.Frontier",
    "Complexitylib.Metacomplexity.MCSP.Magnification.AntiChecker.Generator.Assembly",
    "Complexitylib.Circuits.Frontier.Explicit",
    "Complexitylib.Circuits.Internal.SchnorrDeMorgan",
]


def main():
    source_diff = subprocess.run(
        ["git", "diff", "--quiet", EXPECTED, "--", *SOURCE_PATHS], cwd=ROOT
    )
    if source_diff.returncode:
        raise SystemExit(f"Audited sources differ from {EXPECTED}, or source comparison failed")
    source = "\n".join(f"import {module}" for module in IMPORTS)
    source += "\n\n" + "\n".join(f"#check {name}" for name in DECLARATIONS)
    source += "\n\n" + "\n".join(
        f"#print axioms {name}" for name in AXIOM_DECLARATIONS
    ) + "\n"
    with tempfile.TemporaryDirectory(prefix="mcsp-inventory-") as temporary:
        probe = Path(temporary) / "CheckInventory.lean"
        probe.write_text(source)
        checked = subprocess.run(
            ["lake", "env", "lean", str(probe)], cwd=ROOT,
            capture_output=True, text=True,
        )
    output = checked.stdout + checked.stderr
    report = (
        f"Audited source snapshot: {EXPECTED}\n"
        "Check: imports existing artifacts; no rebuild or full repository gates.\n"
        f"Declaration checks: {len(DECLARATIONS)}\n"
        f"Axiom reports: {len(AXIOM_DECLARATIONS)}\n"
        f"Compiler exit: {checked.returncode}\n\n{output}"
    )
    Path(__file__).with_name("check-output.txt").write_text(report)
    if checked.returncode:
        print(output)
        raise SystemExit(checked.returncode)
    reports = re.findall(r"depends on axioms:\s*\[([^\]]*)\]", output)
    if len(reports) != len(AXIOM_DECLARATIONS):
        raise SystemExit(f"Expected {len(AXIOM_DECLARATIONS)} axiom reports, got {len(reports)}")
    for report in reports:
        names = {name.strip() for name in report.split(",")}
        if not names <= {"propext", "Classical.choice", "Quot.sound"}:
            raise SystemExit(f"Unexpected axiom report: {report}")
    print(f"OK: {len(DECLARATIONS)} declarations; {len(AXIOM_DECLARATIONS)} standard-axiom reports.")


if __name__ == "__main__":
    main()
