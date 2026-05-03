from pathlib import Path

DOC = Path("docs/status/PND_D3EL_COUPLED_DISCHARGE_FRONTIER_2026_05_03.md")


def main() -> None:
    text = DOC.read_text()

    required = [
        "OPEN_FRONTIER",
        "PND-D3EL is equivalent to the coupled discharge",
        "`PLManifoldLike`",
        "`ExposedFeatures`",
        "`LocalDegree`",
        "`MoveAdmissible`",
        "`BarrierHeight`",
        "These primitives are jointly blocking",
        "`local_classification` as previously written is vacuous",
        "`inadmissible_case` is closeable",
        "`PND-CDT-1` is usable",
        "`exposure_case`, blocked on `ExposedFeatures` and `LocalDegree`",
        "`descent_case`, blocked on `MoveAdmissible` and `BarrierHeight`",
        "`local_classification_nontrivial`, which is exactly PND-D3EL",
        "lemma pnd_d3el_coupled_discharge",
        "HasDegreeThreeExposure S",
        "∃ S' : State, Step S S' ∧ beta S' < beta S",
        "This document does not prove PND-D3EL",
        "This document does not define the five missing primitives",
        "This document does not prove the Poincare conjecture",
        "This document does not assert unconditional theorem-level closure",
        "This document does not promote repository build success to mathematical proof",
        "Build success verifies artifact integrity only",
        "No further progress is possible without new input",
    ]

    forbidden = [
        "PND-D3EL is proved",
        "Poincare conjecture proved",
        "unconditional theorem-level closure achieved",
        "repository build success proves",
        "five missing primitives are defined",
        "terminal-exposure bridge proved",
    ]

    for token in required:
        if token not in text:
            raise SystemExit(f"missing required token: {token}")

    for token in forbidden:
        if token in text:
            raise SystemExit(f"forbidden token present: {token}")

    print("PND-D3EL coupled discharge frontier verification OK.")


if __name__ == "__main__":
    main()
