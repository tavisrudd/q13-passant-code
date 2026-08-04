#!/usr/bin/env python3
"""Generate compact transition layers for the q=13 isolated weight-ten profiles."""

from __future__ import annotations

import argparse
import hashlib
import itertools
import json
from pathlib import Path


Q = 13
ROOT = Path(__file__).parent
DATA_OUTPUT = ROOT / "PassantCodeQ13" / "WeightTen" / "ReachabilityData"
CERTIFICATE_OUTPUT = ROOT / "PassantCodeQ13" / "WeightTen" / "IsolatedReachability"
MANIFEST = ROOT / "weight_ten_reachability_manifest.json"
OBSOLETE_OUTPUTS = [
    CERTIFICATE_OUTPUT / f"Fibre{special}" / "TerminalDisjoint.lean"
    for special in range(7)
]

LEFT_STAGES = (
    ("LeftOrdinaryA", "leftOrdinaryA"),
    ("LeftOrdinaryB", "leftOrdinaryB"),
    ("LeftOrdinaryC", "leftOrdinaryC"),
)
RIGHT_STAGES = (
    ("Base", "rightBase"),
    ("DistinguishedTriple", "rightDistinguishedTriple"),
    ("RightOrdinaryA", "rightOrdinaryA"),
    ("RightOrdinaryB", "rightOrdinaryB"),
    ("RightOrdinaryC", "rightOrdinaryC"),
)
TERMINAL_PARTS = (
    ("FirstThird", "leftTerminalFirstThird"),
    ("MiddleThird", "leftTerminalMiddleThird"),
    ("LastThird", "leftTerminalLastThird"),
)


def projective_triples() -> list[tuple[int, int, int]]:
    return (
        [(1, y, z) for y in range(Q) for z in range(Q)]
        + [(0, 1, z) for z in range(Q)]
        + [(0, 0, 1)]
    )


def incidence_data() -> tuple[list[int], int, list[list[int]]]:
    triples = projective_triples()
    squares = {value * value % Q for value in range(1, Q)}
    internal = [
        point
        for point in triples
        if (point[1] * point[1] - point[0] * point[2]) % Q not in squares | {0}
    ]
    passants = [
        line
        for line in triples
        if (line[1] * line[1] - 4 * line[0] * line[2]) % Q not in squares | {0}
    ]

    def incident(line: tuple[int, int, int], point: tuple[int, int, int]) -> bool:
        return sum(left * right for left, right in zip(line, point)) % Q == 0

    columns = [
        sum(1 << row for row, line in enumerate(passants) if incident(line, point))
        for point in internal
    ]
    base = internal.index((1, 0, 2))
    through = [row for row, line in enumerate(passants) if incident(line, internal[base])]
    fibres = [
        [
            index
            for index, point in enumerate(internal)
            if index != base and incident(passants[row], point)
        ]
        for row in through
    ]
    assert len(internal) == len(passants) == 78
    assert base == 0 and len(through) == 7
    assert [len(fibre) for fibre in fibres] == [6] * 7
    return columns, base, fibres


def xor_values(values: tuple[int, ...] | list[int]) -> int:
    answer = 0
    for value in values:
        answer ^= value
    return answer


def transition_layers(options: list[list[int]]) -> list[list[int]]:
    states = [0]
    layers = []
    for increments in options:
        states = [state ^ increment for state in states for increment in increments]
        assert len(states) == len(set(states))
        layers.append(states)
    return layers


def lean_nats(values: list[int], indent: str) -> str:
    if not values:
        return "[]"
    lines = []
    for start in range(0, len(values), 4):
        lines.append(indent + ", ".join(map(str, values[start : start + 4])))
    return "[\n" + ",\n".join(lines) + "\n" + indent[:-2] + "]"


def lean_layers(layers: list[list[int]]) -> str:
    rendered = [lean_nats(layer, "    ") for layer in layers]
    return "[\n  " + ",\n  ".join(rendered) + "\n]"


def render_data(special: int, columns: list[int], base: int, fibres: list[list[int]]) -> str:
    remaining = [index for index in range(7) if index != special]
    left_options = [[columns[point] for point in fibres[index]] for index in remaining[:3]]
    # `List.sublistsLen` emits fixed-length sublists in reverse lexicographic order.
    triple_options = [
        xor_values([columns[point] for point in triple])
        for triple in reversed(list(itertools.combinations(fibres[special], 3)))
    ]
    right_options = (
        [[columns[base]], triple_options]
        + [[columns[point] for point in fibres[index]] for index in remaining[3:]]
    )
    left_layers = transition_layers(left_options)
    right_layers = transition_layers(right_options)
    assert len(left_layers[-1]) == 216
    assert len(right_layers[-1]) == 4320
    assert set(left_layers[-1]).isdisjoint(right_layers[-1])
    definitions = [
        "/-- Syndrome increments for the three left-hand ordinary-fibre choices. -/\n"
        f"abbrev leftOptions : List (List Nat) := {lean_layers(left_options)}",
        "/-- Syndrome increments for the base, distinguished triple, and three right-hand "
        "ordinary-fibre choices. -/\n"
        f"abbrev rightOptions : List (List Nat) := {lean_layers(right_options)}",
    ]
    for stage, ((_, lean_name), layer) in enumerate(zip(LEFT_STAGES, left_layers)):
        if stage < 2:
            definitions.append(
                f"/-- Reachable states after this left-hand ordinary-fibre choice. -/\n"
                f"def {lean_name} : List Nat := {lean_nats(layer, '  ')}"
            )
            continue
        part_size = len(layer) // 3
        for part_index, (_, part_name) in enumerate(TERMINAL_PARTS):
            start = part_index * part_size
            stop = len(layer) if part_index == 2 else (part_index + 1) * part_size
            definitions.append(
                "/-- One Cartesian-enumeration third of the terminal left-hand states. -/\n"
                f"def {part_name} : List Nat := {lean_nats(layer[start:stop], '  ')}"
            )
        definitions.append(
            "/-- Reachable states after the third left-hand ordinary-fibre choice. -/\n"
            "def leftOrdinaryC : List Nat := leftTerminalFirstThird ++ "
            "leftTerminalMiddleThird ++ leftTerminalLastThird"
        )
    for (_, lean_name), layer in zip(RIGHT_STAGES, right_layers):
        definitions.append(
            f"/-- Reachable states after this right-hand profile choice. -/\n"
            f"def {lean_name} : List Nat := {lean_nats(layer, '  ')}"
        )
    definitions.append(
        "/-- The three left-hand transition layers in mathematical choice order. -/\n"
        "abbrev leftLayers : List (List Nat) :=\n  [leftOrdinaryA, leftOrdinaryB, leftOrdinaryC]"
    )
    definitions.append(
        "/-- The five right-hand transition layers in mathematical choice order. -/\n"
        "abbrev rightLayers : List (List Nat) :=\n"
        "  [rightBase, rightDistinguishedTriple, rightOrdinaryA, rightOrdinaryB, rightOrdinaryC]"
    )
    return f'''/-!
# Generated isolated-profile syndrome reachability data

This file is generated by `generate_weight_ten_reachability.py`.  It records the exact reachable
syndrome sets after each Cartesian transition for distinguished passant fibre {special}.  The
checker verifies every transition against the normalized incidence columns; generation carries no
logical authority.
-/

namespace PassantCodeQ13.WeightTen.ReachabilityData.IsolatedFibre{special}

set_option maxRecDepth 100000

{chr(10).join(definitions)}

end PassantCodeQ13.WeightTen.ReachabilityData.IsolatedFibre{special}
'''


def render_transition_certificate(special: int, side: str, stage: int) -> str:
    stages = LEFT_STAGES if side == "left" else RIGHT_STAGES
    module_name, lean_name = stages[stage]
    data_namespace = f"PassantCodeQ13.WeightTen.ReachabilityData.IsolatedFibre{special}"
    current = f"{data_namespace}.{lean_name}"
    previous = "[0]" if stage == 0 else f"{data_namespace}.{stages[stage - 1][1]}"
    unfolded_data = current if stage == 0 else f"{previous} {current}"
    option_data = f"{data_namespace}.{'leftOptions' if side == 'left' else 'rightOptions'}"
    unfolded_data = f"{unfolded_data} {option_data}"
    if side == "left" and stage == 2:
        unfolded_data += " " + " ".join(part_name for _, part_name in TERMINAL_PARTS)
    side_description = "left-hand" if side == "left" else "right-hand"
    return f'''import PassantCodeQ13.WeightTen.Reachability
import PassantCodeQ13.WeightTen.ReachabilityData.IsolatedFibre{special}

/-!
# One {side_description} transition for an isolated weight-ten fibre

This file is generated by `generate_weight_ten_reachability.py`.  Kernel reduction checks the
canonical successor list for one mathematical choice in distinguished passant fibre {special}.
The profile aggregator combines the independently compiled transition theorems.
-/

namespace PassantCodeQ13.WeightTen.IsolatedReachability.Fibre{special}.{module_name}

open PassantCodeQ13.WeightTen
open PassantCodeQ13.WeightTen.Reachability
open PassantCodeQ13.WeightTen.ReachabilityData.IsolatedFibre{special}

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

/-- This generated layer is exactly the canonical XOR-successor list for its Cartesian choice. -/
theorem transition_checked :
    transitionCheck {previous} ({option_data}.getD {stage} []) {current} = true := by
  unfold {unfolded_data}
  unfold transitionCheck transitionSuccessors
  decide +kernel

end PassantCodeQ13.WeightTen.IsolatedReachability.Fibre{special}.{module_name}
'''


def render_disjoint_certificate(special: int, part_module: str, part_name: str) -> str:
    data_namespace = f"PassantCodeQ13.WeightTen.ReachabilityData.IsolatedFibre{special}"
    return f'''import PassantCodeQ13.WeightTen.Reachability
import PassantCodeQ13.WeightTen.ReachabilityData.IsolatedFibre{special}

/-!
# Terminal disjointness for an isolated weight-ten fibre

This file is generated by `generate_weight_ten_reachability.py`.  Kernel reduction checks that
the two terminal reachable-state lists for distinguished passant fibre {special} are disjoint.
-/

namespace PassantCodeQ13.WeightTen.IsolatedReachability.Fibre{special}.TerminalDisjoint.{part_module}

open PassantCodeQ13.WeightTen.Reachability
open PassantCodeQ13.WeightTen.ReachabilityData.IsolatedFibre{special}

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

/-- This Cartesian-enumeration third is disjoint from the terminal right-hand states. -/
theorem checked :
    disjointCheck {data_namespace}.{part_name} {data_namespace}.rightOrdinaryC = true := by
  unfold {data_namespace}.{part_name} {data_namespace}.rightOrdinaryC
  unfold disjointCheck
  decide +kernel

end PassantCodeQ13.WeightTen.IsolatedReachability.Fibre{special}.TerminalDisjoint.{part_module}
'''


def render_options_certificate(special: int, side: str) -> str:
    title = "Left" if side == "left" else "Right"
    semantic = "isolatedLeftOptions" if side == "left" else "isolatedRightOptions"
    generated = "leftOptions" if side == "left" else "rightOptions"
    xor_unfold = " xorColumns" if side == "right" else ""
    data_namespace = f"PassantCodeQ13.WeightTen.ReachabilityData.IsolatedFibre{special}"
    return f'''import PassantCodeQ13.WeightTen.Reachability
import PassantCodeQ13.WeightTen.ReachabilityData.IsolatedFibre{special}

/-!
# {title}-hand option bridge for an isolated weight-ten fibre

This file is generated by `generate_weight_ten_reachability.py`.  Kernel reduction checks that
the compact syndrome-increment lists for distinguished passant fibre {special} agree with the
normalized conic incidence columns used by the formal Cartesian domain.
-/

namespace PassantCodeQ13.WeightTen.IsolatedReachability.Fibre{special}.{title}Options

open PassantCodeQ13.WeightTen

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

/-- The generated increment lists equal the executable normalized-incidence option lists. -/
theorem checked : {semantic} {special} = {data_namespace}.{generated} := by
  unfold {data_namespace}.{generated}
  unfold {semantic} remainingFibres columnOptions fibres linesThroughBase columnSyndrome
    incidentAt internalAt passantAt{xor_unfold}
  unfold RelativeConicArcs.PassantCodeQ13.internalCoordinateList
    RelativeConicArcs.PassantCodeQ13.passantCoordinateList
    RelativeConicArcs.PassantCodeQ13.projectiveTripleList
    RelativeConicArcs.PassantCodeQ13.fieldElements
    RelativeConicArcs.PassantCodeQ13.pointDiscriminant
    RelativeConicArcs.PassantCodeQ13.lineDiscriminant
    RelativeConicArcs.PassantCodeQ13.isNonzeroSquare
    RelativeConicArcs.PassantCodeQ13.affineTriple
    RelativeConicArcs.PassantCodeQ13.infiniteTriple
    RelativeConicArcs.PassantCodeQ13.verticalTriple
  decide +kernel

end PassantCodeQ13.WeightTen.IsolatedReachability.Fibre{special}.{title}Options
'''


def render_certificate(special: int) -> str:
    imports = [
        f"import PassantCodeQ13.WeightTen.IsolatedReachability.Fibre{special}.LeftOptions",
        f"import PassantCodeQ13.WeightTen.IsolatedReachability.Fibre{special}.RightOptions",
        *(f"import PassantCodeQ13.WeightTen.IsolatedReachability.Fibre{special}.{name}"
          for name, _ in LEFT_STAGES),
        *(f"import PassantCodeQ13.WeightTen.IsolatedReachability.Fibre{special}.{name}"
          for name, _ in RIGHT_STAGES),
        *(f"import PassantCodeQ13.WeightTen.IsolatedReachability.Fibre{special}.TerminalDisjoint.{name}"
          for name, _ in TERMINAL_PARTS),
    ]
    return f'''{chr(10).join(imports)}

/-!
# Reachability certificate for an isolated weight-ten fibre

The generated state lists contain every syndrome reached by the complete Cartesian domains on the
two sides of the meet-in-the-middle decomposition for distinguished passant fibre {special}.
Independent kernel-reduced modules check each mathematical transition and terminal disjointness.
The terminal theorem therefore excludes equality for arbitrary choices, rather than only for the
generated enumeration order.
-/

namespace PassantCodeQ13.WeightTen.IsolatedReachability.Fibre{special}

open PassantCodeQ13.WeightTen
open PassantCodeQ13.WeightTen.Reachability
open PassantCodeQ13.WeightTen.ReachabilityData.IsolatedFibre{special}

/-- The generated left layers cover all three ordinary-fibre choices. -/
theorem left_chain : chainCheck [0] (isolatedLeftOptions {special}) leftLayers = true := by
  rw [LeftOptions.checked]
  exact chainCheck_cons_of_transitionCheck LeftOrdinaryA.transition_checked
    (chainCheck_cons_of_transitionCheck LeftOrdinaryB.transition_checked
      (chainCheck_cons_of_transitionCheck LeftOrdinaryC.transition_checked
        (chainCheck_nil leftOrdinaryC)))

/-- The generated right layers cover the base, three-point, and three remaining fibres. -/
theorem right_chain : chainCheck [0] (isolatedRightOptions {special}) rightLayers = true := by
  rw [RightOptions.checked]
  exact chainCheck_cons_of_transitionCheck Base.transition_checked
    (chainCheck_cons_of_transitionCheck DistinguishedTriple.transition_checked
      (chainCheck_cons_of_transitionCheck RightOrdinaryA.transition_checked
        (chainCheck_cons_of_transitionCheck RightOrdinaryB.transition_checked
          (chainCheck_cons_of_transitionCheck RightOrdinaryC.transition_checked
            (chainCheck_nil rightOrdinaryC)))))

/-- The two terminal reachable-state lists are disjoint. -/
theorem terminal_disjoint :
    disjointCheck (terminalStates [0] leftLayers) (terminalStates [0] rightLayers) = true := by
  have first_two := disjointCheck_append TerminalDisjoint.FirstThird.checked
    TerminalDisjoint.MiddleThird.checked
  have all_three := disjointCheck_append first_two TerminalDisjoint.LastThird.checked
  simpa [terminalStates, leftLayers, rightLayers, leftOrdinaryC] using all_three

/-- No complete isolated-profile Cartesian choice for the distinguished fibre has zero syndrome. -/
theorem no_equal_cartesian_syndromes
    {{leftPath rightPath : List Nat}}
    (leftChoices : ChoicePath (isolatedLeftOptions {special}) leftPath)
    (rightChoices : ChoicePath (isolatedRightOptions {special}) rightPath) :
    leftPath.foldl (fun state increment => state ^^^ increment) 0 ≠
      rightPath.foldl (fun state increment => state ^^^ increment) 0 := by
  apply ne_of_disjointCheck terminal_disjoint
  · exact foldl_xor_mem_terminalStates left_chain (by simp) leftChoices
  · exact foldl_xor_mem_terminalStates right_chain (by simp) rightChoices

/-- Executable Cartesian-product membership is sufficient for the same syndrome exclusion. -/
theorem no_equal_of_mem_choices
    {{leftPath rightPath : List Nat}}
    (left_mem : leftPath ∈ choices (isolatedLeftOptions {special}))
    (right_mem : rightPath ∈ choices (isolatedRightOptions {special})) :
    leftPath.foldl (fun state increment => state ^^^ increment) 0 ≠
      rightPath.foldl (fun state increment => state ^^^ increment) 0 :=
  no_equal_cartesian_syndromes
    (choicePath_of_mem_choices left_mem) (choicePath_of_mem_choices right_mem)

end PassantCodeQ13.WeightTen.IsolatedReachability.Fibre{special}
'''


def generated_files() -> dict[Path, str]:
    columns, base, fibres = incidence_data()
    files = {}
    for special in range(7):
        files[DATA_OUTPUT / f"IsolatedFibre{special}.lean"] = render_data(
            special, columns, base, fibres
        )
        files[CERTIFICATE_OUTPUT / f"Fibre{special}.lean"] = render_certificate(special)
        files[CERTIFICATE_OUTPUT / f"Fibre{special}" / "LeftOptions.lean"] = (
            render_options_certificate(special, "left")
        )
        files[CERTIFICATE_OUTPUT / f"Fibre{special}" / "RightOptions.lean"] = (
            render_options_certificate(special, "right")
        )
        for stage, (module_name, _) in enumerate(LEFT_STAGES):
            files[CERTIFICATE_OUTPUT / f"Fibre{special}" / f"{module_name}.lean"] = (
                render_transition_certificate(special, "left", stage)
            )
        for stage, (module_name, _) in enumerate(RIGHT_STAGES):
            files[CERTIFICATE_OUTPUT / f"Fibre{special}" / f"{module_name}.lean"] = (
                render_transition_certificate(special, "right", stage)
            )
        for part_module, part_name in TERMINAL_PARTS:
            files[
                CERTIFICATE_OUTPUT
                / f"Fibre{special}"
                / "TerminalDisjoint"
                / f"{part_module}.lean"
            ] = render_disjoint_certificate(special, part_module, part_name)
    records = []
    for path, content in sorted(files.items()):
        encoded = content.encode()
        records.append(
            {
                "path": str(path.relative_to(ROOT)),
                "bytes": len(encoded),
                "sha256": hashlib.sha256(encoded).hexdigest(),
            }
        )
    generator_bytes = Path(__file__).read_bytes()
    manifest = {
        "schema": "q13-isolated-weight-ten-reachability-v1",
        "field_order": Q,
        "distinguished_fibres": 7,
        "ordinary_choices_per_fibre": 6,
        "distinguished_triple_choices": 20,
        "generator": {
            "path": Path(__file__).name,
            "bytes": len(generator_bytes),
            "sha256": hashlib.sha256(generator_bytes).hexdigest(),
        },
        "files": records,
    }
    files[MANIFEST] = json.dumps(manifest, indent=2, sort_keys=True) + "\n"
    return files


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    files = generated_files()
    if args.check:
        stale = [path for path, content in files.items() if not path.exists() or path.read_text() != content]
        stale.extend(path for path in OBSOLETE_OUTPUTS if path.exists())
        if stale:
            raise SystemExit("stale generated reachability data: " + ", ".join(map(str, stale)))
        print("q=13 isolated weight-ten reachability data: PASS")
        return
    for path in OBSOLETE_OUTPUTS:
        path.unlink(missing_ok=True)
    for path, content in files.items():
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(content)


if __name__ == "__main__":
    main()
