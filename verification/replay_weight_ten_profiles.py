#!/usr/bin/env python3
"""Independent dynamic-programming replay of the q=13 weight-ten exclusions."""

from __future__ import annotations

import hashlib
import itertools
import json
from pathlib import Path


Q = 13
ARTIFACT = Path(__file__).with_name("weight_ten_profiles.json")


def points() -> list[tuple[int, int, int]]:
    return (
        [(1, y, z) for y in range(Q) for z in range(Q)]
        + [(0, 1, z) for z in range(Q)]
        + [(0, 0, 1)]
    )


def qpoint(point: tuple[int, int, int]) -> int:
    return (point[1] ** 2 - point[0] * point[2]) % Q


def incident(line: tuple[int, int, int], point: tuple[int, int, int]) -> bool:
    return sum(a * b for a, b in zip(line, point)) % Q == 0


def xor_all(values: tuple[int, ...]) -> int:
    answer = 0
    for value in values:
        answer ^= value
    return answer


def extend(reachable: set[int], choices: list[int]) -> set[int]:
    return {old ^ choice for old in reachable for choice in choices}


def main() -> None:
    projective = points()
    squares = {value * value % Q for value in range(1, Q)}
    internal = [point for point in projective if qpoint(point) not in squares | {0}]
    passants = [
        line for line in projective
        if (line[1] ** 2 - 4 * line[0] * line[2]) % Q not in squares | {0}
    ]
    columns = [
        sum(1 << row for row, line in enumerate(passants) if incident(line, point))
        for point in internal
    ]
    base = internal.index((1, 0, 2))
    through = [line for line in passants if incident(line, internal[base])]
    fibre_indices = [
        [index for index, point in enumerate(internal) if index != base and incident(line, point)]
        for line in through
    ]
    fibre_columns = [[columns[index] for index in fibre] for fibre in fibre_indices]
    passant_neighbors = set().union(*(set(fibre) for fibre in fibre_indices))
    secant_indices = [
        index for index in range(78) if index != base and index not in passant_neighbors
    ]
    artifact = json.loads(ARTIFACT.read_text())
    digest = hashlib.sha256(
        b"".join(column.to_bytes(10, "big") for column in columns)
    ).hexdigest()
    assert digest == artifact["incidence_column_sha256"]

    profile_zero_counts = []
    for special in range(7):
        reachable = {0}
        for index, choices in enumerate(fibre_columns):
            if index != special:
                reachable = extend(reachable, choices)
        triple_targets = {
            columns[base] ^ xor_all(tuple(columns[index] for index in triple))
            for triple in itertools.combinations(fibre_indices[special], 3)
        }
        assert reachable.isdisjoint(triple_targets)
        profile_zero_counts.append((len(reachable), len(triple_targets)))

    fibre_reachable = {0}
    for choices in fibre_columns:
        fibre_reachable = extend(fibre_reachable, choices)
    pair_reachable = {
        columns[first] ^ columns[second]
        for first, second in itertools.combinations(secant_indices, 2)
    }
    shifted_fibres = {columns[base] ^ value for value in fibre_reachable}
    assert shifted_fibres.isdisjoint(pair_reachable)

    print(
        "independent q=13 weight-ten replay: PASS; "
        f"s=0 DP sizes={profile_zero_counts}; "
        f"s=2 DP sizes=({len(fibre_reachable)},{len(pair_reachable)})"
    )


if __name__ == "__main__":
    main()
