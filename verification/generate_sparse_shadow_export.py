#!/usr/bin/env python3
"""Generate the paper-owned sparse-shadow export for Paper IV."""

from __future__ import annotations

import argparse
import hashlib
import itertools
import json
from collections import Counter, deque
from pathlib import Path

import verify_pair_reconstruction as pair_reconstruction


EXPORT_SCHEMA = "sparse-shadow/v1"
REQUIRED_EXPORT = "verification/sparse_shadow_export.json"
PAIR_CERTIFICATE = Path(__file__).with_name("pair_reconstruction.json")
PGL_GENERATORS = (
    (1, 1, 0, 1),
    (0, 1, 12, 0),
    (2, 0, 0, 1),
)


def permutation_for(
    matrix: tuple[int, int, int, int],
    points: list[tuple[int, int, int]],
) -> tuple[int, ...]:
    point_index = {point: index for index, point in enumerate(points)}
    return tuple(point_index[pair_reconstruction.act(matrix, point)] for point in points)


def compose(left: tuple[int, ...], right: tuple[int, ...]) -> tuple[int, ...]:
    return tuple(left[right[index]] for index in range(len(left)))


def generated_group_order(generators: tuple[tuple[int, ...], ...]) -> int:
    identity = tuple(range(len(generators[0])))
    seen = {identity}
    pending = deque([identity])
    while pending:
        element = pending.popleft()
        for generator in generators:
            product = compose(generator, element)
            if product not in seen:
                seen.add(product)
                pending.append(product)
    return len(seen)


def compute() -> dict[str, object]:
    points = pair_reconstruction.internal_points()
    point_index = {point: index for index, point in enumerate(points)}
    matrices = pair_reconstruction.pgl_matrices()
    assert len(points) == 78
    assert len(matrices) == 2184

    minimum_supports: set[frozenset[int]] = set()
    for representative in pair_reconstruction.REPRESENTATIVES:
        minimum_supports.update(
            frozenset(point_index[pair_reconstruction.act(matrix, point)] for point in representative)
            for matrix in matrices
        )
    assert len(minimum_supports) == 364

    concurrence: Counter[tuple[int, int]] = Counter()
    for support in minimum_supports:
        concurrence.update(itertools.combinations(sorted(support), 2))
    assert len(concurrence) == 78 * 77 // 2
    assert Counter(concurrence.values()) == Counter({6: 1092, 7: 546, 8: 273, 9: 546, 12: 546})

    generators = tuple(permutation_for(matrix, points) for matrix in PGL_GENERATORS)
    assert generated_group_order(generators) == 2184

    source_bytes = PAIR_CERTIFICATE.read_bytes()
    source_sha256 = hashlib.sha256(source_bytes).hexdigest()
    return {
        "schema": EXPORT_SCHEMA,
        "profile": {
            "adapter": "paper_iv_minimum_words",
            "input": {
                "gate": {
                    "enabled": True,
                    "reason": "paper-owned sparse-shadow export frozen",
                    "required_export": REQUIRED_EXPORT,
                },
                "source": {
                    "paper": "IV",
                    "theorem": "exact arity-two minimum-word reconstruction",
                    "artifact": "verification/pair_reconstruction.json",
                    "sha256": source_sha256,
                },
                "field": {
                    "characteristic": 13,
                    "degree": 1,
                    "modulus_coefficients_low_to_high": [],
                    "element_encoding": "least_nonnegative_residue",
                },
                "coordinate_count": 78,
                "minimum_support_count": 364,
                "weighted_pair_section": [
                    {"left": left, "right": right, "multiplicity": concurrence[left, right]}
                    for left, right in sorted(concurrence)
                ],
                "action": {
                    "kind": "vertex_permutations",
                    "degree": 78,
                    "generators": [list(generator) for generator in generators],
                },
                "recovered_carrier": "PG(2,13), conic, and polarity",
                "ambiguity": {"kind": "marking_torsor", "group": "PGL2(13)"},
                "minimality_collisions": [],
            },
        },
    }


def canonical_json(value: dict[str, object]) -> str:
    return json.dumps(value, indent=2, sort_keys=True) + "\n"


def main() -> None:
    parser = argparse.ArgumentParser()
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--write", type=Path)
    mode.add_argument("--check", type=Path)
    args = parser.parse_args()
    rendered = canonical_json(compute())
    if args.write:
        args.write.write_text(rendered, encoding="utf-8")
    else:
        assert args.check.read_text(encoding="utf-8") == rendered
        print("Paper IV sparse-shadow export: PASS")


if __name__ == "__main__":
    main()
