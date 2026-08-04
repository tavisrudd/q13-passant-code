#!/usr/bin/env python3
"""Canonical meet-in-the-middle certificates for the two q=13 weight-ten profiles."""

from __future__ import annotations

import argparse
import hashlib
import itertools
import json
import math
from pathlib import Path


ROOT = Path(__file__).resolve().parent
ARTIFACT = ROOT / "weight_ten_profiles.json"
Q = 13


def canonical(vector: tuple[int, ...]) -> tuple[int, ...]:
    first = next(value for value in vector if value)
    inverse = pow(first, -1, Q)
    return tuple(value * inverse % Q for value in vector)


def projective_points() -> list[tuple[int, int, int]]:
    return (
        [(1, y, z) for y in range(Q) for z in range(Q)]
        + [(0, 1, z) for z in range(Q)]
        + [(0, 0, 1)]
    )


def quadratic(point: tuple[int, int, int]) -> int:
    return (point[1] * point[1] - point[0] * point[2]) % Q


def incidence_geometry() -> tuple[
    list[int], int, list[list[int]], list[int], list[tuple[int, int, int]]
]:
    points = projective_points()
    nonzero_squares = {value * value % Q for value in range(1, Q)}
    internal = [
        point for point in points
        if quadratic(point) not in nonzero_squares | {0}
    ]
    passants = [
        line for line in points
        if (line[1] * line[1] - 4 * line[0] * line[2]) % Q
        not in nonzero_squares | {0}
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
            index for index, point in enumerate(internal)
            if index != base and incident(passants[row], point)
        ]
        for row in through
    ]
    passant_neighbors = set().union(*(set(fibre) for fibre in fibres))
    secant_neighbors = [
        index for index in range(len(internal))
        if index != base and index not in passant_neighbors
    ]
    assert len(internal) == len(passants) == 78
    assert len(through) == 7
    assert [len(fibre) for fibre in fibres] == [6] * 7
    assert len(secant_neighbors) == 35
    return columns, base, fibres, secant_neighbors, internal


def xor_columns(columns: list[int], indices: tuple[int, ...]) -> int:
    answer = 0
    for index in indices:
        answer ^= columns[index]
    return answer


def digest_integers(values: set[int]) -> str:
    digest = hashlib.sha256()
    for value in sorted(values):
        digest.update(value.to_bytes(10, "big"))
    return digest.hexdigest()


def product_xors(columns: list[int], fibres: list[list[int]]) -> set[int]:
    return {
        xor_columns(columns, choice)
        for choice in itertools.product(*fibres)
    }


def profile_zero_certificate(
    columns: list[int], base: int, fibres: list[list[int]]
) -> list[dict[str, object]]:
    records = []
    for special in range(7):
        remaining = [index for index in range(7) if index != special]
        left = product_xors(columns, [fibres[index] for index in remaining[:3]])
        right = {
            columns[base]
            ^ xor_columns(columns, triple)
            ^ xor_columns(columns, tail)
            for triple in itertools.combinations(fibres[special], 3)
            for tail in itertools.product(*(fibres[index] for index in remaining[3:]))
        }
        intersection = left & right
        assert not intersection
        records.append(
            {
                "special_fibre": special,
                "raw_domain": 20 * 6**6,
                "left_raw": 6**3,
                "left_unique": len(left),
                "left_sha256": digest_integers(left),
                "right_raw": 20 * 6**3,
                "right_unique": len(right),
                "right_sha256": digest_integers(right),
                "intersection_size": 0,
            }
        )
    return records


def profile_two_certificate(
    columns: list[int], base: int, fibres: list[list[int]], secant_neighbors: list[int]
) -> dict[str, object]:
    left = product_xors(columns, fibres[:3])
    right = {
        columns[base]
        ^ xor_columns(columns, tail)
        ^ xor_columns(columns, pair)
        for tail in itertools.product(*fibres[3:])
        for pair in itertools.combinations(secant_neighbors, 2)
    }
    intersection = left & right
    assert not intersection
    return {
        "raw_domain": 6**7 * math.comb(35, 2),
        "left_raw": 6**3,
        "left_unique": len(left),
        "left_sha256": digest_integers(left),
        "right_raw": 6**4 * math.comb(35, 2),
        "right_unique": len(right),
        "right_sha256": digest_integers(right),
        "intersection_size": 0,
    }
def build_record() -> dict[str, object]:
    columns, base, fibres, secant_neighbors, internal = incidence_geometry()
    profile_zero = profile_zero_certificate(columns, base, fibres)
    profile_two = profile_two_certificate(columns, base, fibres, secant_neighbors)
    column_digest = hashlib.sha256(
        b"".join(column.to_bytes(10, "big") for column in columns)
    ).hexdigest()
    return {
        "schema": "q13-passant-code-weight-ten-profiles-v1",
        "field": 13,
        "conic": "XZ-Y^2=0",
        "base_point": list(internal[base]),
        "incidence_column_sha256": column_digest,
        "local_partition": {
            "passant_fibres": 7,
            "points_per_fibre_excluding_base": 6,
            "secant_neighbors": 35,
        },
        "parity_derivation": {
            "secant_neighbor_count": "s is even",
            "passant_fibre_occupancies": "seven positive odd integers summing to 9-s",
            "solutions": [
                {"s": 0, "occupancies": [3, 1, 1, 1, 1, 1, 1]},
                {"s": 2, "occupancies": [1, 1, 1, 1, 1, 1, 1]},
            ],
            "global_secant_graph": "every support vertex has secant degree 0 or 2, so the induced secant-join graph is a disjoint union of cycles and isolated vertices",
        },
        "profile_s0": profile_zero,
        "profile_s2": profile_two,
        "certified_conclusion": "no weight-ten kernel word containing the fixed base point",
        "symmetry_boundary": "PGL(2,13) is transitive on internal points, so the fixed-base exclusion is global",
    }


def canonical_bytes(record: dict[str, object]) -> bytes:
    return (json.dumps(record, indent=2, sort_keys=True) + "\n").encode()


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--output", type=Path, default=ARTIFACT)
    args = parser.parse_args()
    generated = canonical_bytes(build_record())
    if args.check:
        expected = args.output.read_bytes()
        if generated != expected:
            raise SystemExit(f"stale artifact: {args.output}")
        print(
            f"OK {args.output.name} {len(expected)} bytes "
            f"sha256={hashlib.sha256(expected).hexdigest()}"
        )
        return
    args.output.write_bytes(generated)
    print(
        f"wrote {args.output} {len(generated)} bytes "
        f"sha256={hashlib.sha256(generated).hexdigest()}"
    )


if __name__ == "__main__":
    main()
