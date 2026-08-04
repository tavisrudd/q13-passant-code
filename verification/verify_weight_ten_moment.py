#!/usr/bin/env python3
"""Exact moment-and-stabilizer certificate for weight ten at q=13."""

from __future__ import annotations

import argparse
import itertools
import json
from collections import Counter
from pathlib import Path


Q = 13


def canonical(vector: tuple[int, ...]) -> tuple[int, ...]:
    first = next(value for value in vector if value % Q)
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


def incident(line: tuple[int, int, int], point: tuple[int, int, int]) -> bool:
    return sum(left * right for left, right in zip(line, point)) % Q == 0


def projective_group() -> list[tuple[int, int, int, int]]:
    matrices = (
        [(1, b, c, d) for b in range(Q) for c in range(Q) for d in range(Q)]
        + [(0, 1, c, d) for c in range(Q) for d in range(Q)]
        + [(0, 0, 1, d) for d in range(Q)]
        + [(0, 0, 0, 1)]
    )
    return [
        matrix
        for matrix in matrices
        if (matrix[0] * matrix[3] - matrix[1] * matrix[2]) % Q
    ]


def act_quadratic(
    matrix: tuple[int, int, int, int], point: tuple[int, int, int]
) -> tuple[int, int, int]:
    a, b, c, d = matrix
    x, y, z = point
    return canonical(
        (
            (a * a * x + 2 * a * b * y + b * b * z) % Q,
            (a * c * x + (a * d + b * c) * y + b * d * z) % Q,
            (c * c * x + 2 * c * d * y + d * d * z) % Q,
        )
    )


def binary_rank(rows: list[int], variables: int) -> int:
    pivots: dict[int, int] = {}
    for original in rows:
        row = original
        while row:
            pivot = min(row.bit_length() - 1, variables - 1)
            # When an augmented bit is present, it is a genuine extra column.
            if row.bit_length() - 1 >= variables:
                pivot = row.bit_length() - 1
            if pivot in pivots:
                row ^= pivots[pivot]
            else:
                pivots[pivot] = row
                break
    return len(pivots)


def feature_pair_index(first: int, second: int, size: int) -> int:
    assert first < second
    return size + first * (2 * size - first - 1) // 2 + second - first - 1


def quadratic_lift(value: int, size: int) -> int:
    support = [index for index in range(size) if value >> index & 1]
    result = value
    for position, first in enumerate(support):
        for second in support[position + 1 :]:
            result |= 1 << feature_pair_index(first, second, size)
    return result


def xor_columns(columns: list[int], indices: tuple[int, ...]) -> int:
    answer = 0
    for index in indices:
        answer ^= columns[index]
    return answer


def compute() -> dict[str, object]:
    all_points = projective_points()
    squares = {value * value % Q for value in range(1, Q)}
    internal = [
        point for point in all_points if quadratic(point) not in squares | {0}
    ]
    passants = [
        line
        for line in all_points
        if (line[1] * line[1] - 4 * line[0] * line[2]) % Q
        not in squares | {0}
    ]
    assert len(internal) == len(passants) == 78
    point_index = {point: index for index, point in enumerate(internal)}
    line_points = [
        [index for index, point in enumerate(internal) if incident(line, point)]
        for line in passants
    ]
    assert {len(row) for row in line_points} == {7}
    point_lines = [
        [row for row, support in enumerate(line_points) if point in support]
        for point in range(78)
    ]
    passant_pair = [[False] * 78 for _ in range(78)]
    for support in line_points:
        for first, second in itertools.combinations(support, 2):
            passant_pair[first][second] = passant_pair[second][first] = True
    assert {sum(row) for row in passant_pair} == {42}

    columns = [
        sum(
            1 << row
            for row, line in enumerate(passants)
            if incident(line, point)
        )
        for point in internal
    ]
    base = point_index[(1, 0, 2)]
    through = [
        row for row, line in enumerate(passants) if incident(line, internal[base])
    ]
    fibres = [
        [point for point in line_points[row] if point != base] for row in through
    ]
    passant_neighbors = set().union(*(set(fibre) for fibre in fibres))
    secant_neighbors = [
        point
        for point in range(78)
        if point != base and point not in passant_neighbors
    ]
    assert [len(fibre) for fibre in fibres] == [6] * 7
    assert len(secant_neighbors) == 35

    group = projective_group()
    assert len(group) == 2184
    permutations = [
        tuple(point_index[act_quadratic(matrix, point)] for point in internal)
        for matrix in group
    ]

    # The moment identity leaves m=6 and m=10.  Here m is the number of
    # vertices of the induced secant graph, whose degrees are zero or two.
    moment_solutions = []
    for m in range(11):
        solutions = []
        for n4 in range(18):
            for n6 in range(12):
                if 4 * n4 + 12 * n6 == 10 - m:
                    n2 = (70 - 4 * n4 - 6 * n6) // 2
                    if 2 * n2 + 4 * n4 + 6 * n6 == 70 and n2 >= 0:
                        solutions.append((n2, n4, n6))
        if solutions and m != 2:  # two degree-two vertices cannot form cycles.
            moment_solutions.append((m, solutions))
    assert moment_solutions == [(6, [(33, 1, 0)]), (10, [(35, 0, 0)])]

    # m=6: four isolated points lie on the unique four-point passant.
    standard_line = set(line_points[0])
    line_stabilizer = [
        permutation
        for permutation in permutations
        if {permutation[point] for point in standard_line} == standard_line
    ]
    assert len(line_stabilizer) == 28
    start = min(standard_line)
    cyclic_labels = None
    for permutation in line_stabilizer:
        orbit = []
        current = start
        while current not in orbit:
            orbit.append(current)
            current = permutation[current]
        if len(orbit) == 7:
            cyclic_labels = orbit
            break
    assert cyclic_labels is not None
    label = {point: index for index, point in enumerate(cyclic_labels)}
    remaining_four_sets = set(itertools.combinations(sorted(standard_line), 4))
    four_set_records = []
    while remaining_four_sets:
        seed = min(remaining_four_sets)
        orbit = {
            tuple(sorted(permutation[point] for point in seed))
            for permutation in line_stabilizer
        }
        remaining_four_sets -= orbit
        representative = min(
            tuple(sorted(label[point] for point in member)) for member in orbit
        )
        candidates = [
            point
            for point in range(78)
            if point not in seed
            and all(passant_pair[point][fixed] for fixed in seed)
        ]
        degree_sequence = sorted(
            sum(
                not passant_pair[first][second]
                for second in candidates
                if second != first
            )
            for first in candidates
        )
        six_profiles = Counter(
            tuple(
                sorted(
                    sum(
                        not passant_pair[first][second]
                        for second in six
                        if second != first
                    )
                    for first in six
                )
            )
            for six in itertools.combinations(candidates, 6)
        )
        assert six_profiles.get((2, 2, 2, 2, 2, 2), 0) == 0
        four_set_records.append(
            {
                "cyclic_representative": list(representative),
                "fixed_line_orbit_size": len(orbit),
                "global_four_set_count": 78 * len(orbit),
                "common_passant_neighbor_count": len(candidates),
                "secant_degree_sequence": degree_sequence,
                "six_subsets_checked": sum(six_profiles.values()),
                "two_regular_six_subsets": 0,
            }
        )
    four_set_records.sort(key=lambda record: record["cyclic_representative"])
    assert [record["fixed_line_orbit_size"] for record in four_set_records] == [
        7,
        14,
        7,
        7,
    ]

    # m=10: normalize a selected point.  Its two secant neighbors have 33
    # orbits under the D_28 stabilizer.  A pruned seven-fibre exact search uses
    # only line caps and secant degrees, never incidence syndromes.
    base_stabilizer = [
        permutation for permutation in permutations if permutation[base] == base
    ]
    assert len(base_stabilizer) == 28
    remaining_pairs = set(itertools.combinations(secant_neighbors, 2))

    def prefix_survivors(pair: tuple[int, int]) -> tuple[int, ...]:
        selected = [base, *pair]
        degrees = [
            sum(
                not passant_pair[first][second]
                for second in selected
                if second != first
            )
            for first in selected
        ]
        line_counts = [0] * 78
        for point in selected:
            for line in point_lines[point]:
                line_counts[line] += 1
        if max(degrees) > 2 or max(line_counts) > 2:
            return (0,) * 8
        levels = [0] * 8
        levels[0] = 1

        def visit(level: int) -> None:
            if level == 7:
                if degrees == [2] * 10:
                    levels[7] += 1
                return
            for point in fibres[level]:
                connections = [
                    not passant_pair[point][other] for other in selected
                ]
                if sum(connections) > 2:
                    continue
                if any(
                    degrees[index] + connections[index] > 2
                    for index in range(len(selected))
                ):
                    continue
                if any(line_counts[line] >= 2 for line in point_lines[point]):
                    continue
                selected.append(point)
                degrees.append(sum(connections))
                for index, edge in enumerate(connections):
                    degrees[index] += edge
                for line in point_lines[point]:
                    line_counts[line] += 1
                levels[level + 1] += 1
                visit(level + 1)
                for line in point_lines[point]:
                    line_counts[line] -= 1
                for index, edge in enumerate(connections):
                    degrees[index] -= edge
                degrees.pop()
                selected.pop()

        visit(0)
        return tuple(levels)

    pair_orbit_records = []
    while remaining_pairs:
        seed = min(remaining_pairs)
        orbit = {
            tuple(sorted((permutation[seed[0]], permutation[seed[1]])))
            for permutation in base_stabilizer
        }
        remaining_pairs -= orbit
        representative = min(orbit)
        levels = prefix_survivors(representative)
        assert levels[7] == 0
        pair_orbit_records.append(
            {
                "representative": list(representative),
                "orbit_size": len(orbit),
                "pair_join": (
                    "passant"
                    if passant_pair[representative[0]][representative[1]]
                    else "secant"
                ),
                "surviving_prefixes_after_0_to_7_fibres": list(levels),
                "last_nonzero_depth": max(
                    index for index, value in enumerate(levels) if value
                ),
            }
        )
    pair_orbit_records.sort(key=lambda record: record["representative"])
    assert len(pair_orbit_records) == 33
    assert sum(record["orbit_size"] for record in pair_orbit_records) == 595
    maximum_depth = max(
        record["last_nonzero_depth"] for record in pair_orbit_records
    )
    assert maximum_depth < 7
    depth_mass = Counter()
    for record in pair_orbit_records:
        depth_mass[record["last_nonzero_depth"]] += record["orbit_size"]

    # Failure boundaries for simpler syndrome duals.
    fibre_constancy = []
    for fibre in fibres:
        for point in fibre[1:]:
            fibre_constancy.append(columns[point] ^ columns[fibre[0]])
    secant_constancy = [
        columns[point] ^ columns[secant_neighbors[0]]
        for point in secant_neighbors[1:]
    ]
    target = columns[base]
    for fibre in fibres:
        target ^= columns[fibre[0]]
    s0_coefficients = fibre_constancy + [target]
    s0_augmented = fibre_constancy + [target | (1 << 78)]
    s2_coefficients = fibre_constancy + secant_constancy + [target]
    s2_augmented = fibre_constancy + secant_constancy + [target | (1 << 78)]
    linear_ranks = {
        "s0": [binary_rank(s0_coefficients, 78), binary_rank(s0_augmented, 79)],
        "s2": [binary_rank(s2_coefficients, 78), binary_rank(s2_augmented, 79)],
    }
    assert linear_ranks == {"s0": [32, 33], "s2": [34, 35]}

    feature_count = 78 + 78 * 77 // 2
    product = itertools.product(*fibres)
    first_choice = next(product)
    second_choice = next(product)
    quadratic_syndromes = [
        columns[base]
        ^ xor_columns(columns, first_choice)
        ^ xor_columns(columns, pair)
        for pair in itertools.combinations(secant_neighbors, 2)
    ]
    quadratic_syndromes.append(
        columns[base]
        ^ xor_columns(columns, second_choice)
        ^ xor_columns(columns, (secant_neighbors[0], secant_neighbors[1]))
    )
    quadratic_rows = [
        quadratic_lift(syndrome, 78) for syndrome in quadratic_syndromes
    ]
    quadratic_augmented = [
        row | (1 << feature_count) for row in quadratic_rows
    ]
    quadratic_ranks = [
        binary_rank(quadratic_rows, feature_count),
        binary_rank(quadratic_augmented, feature_count + 1),
    ]
    assert quadratic_ranks == [595, 596]

    return {
        "schema": "paper-iv-weight-ten-moment-v1",
        "field": Q,
        "global_moment_reduction": {
            "support_size": 10,
            "incidences": 70,
            "pairs": 45,
            "identity": "4*n4+12*n6+24*n8+...=10-m",
            "solutions": [
                {
                    "secant_cycle_vertices_m": 6,
                    "passant_line_counts": {"n2": 33, "n4": 1},
                    "shape": "four isolated points on the unique 4-line plus six cycle vertices",
                },
                {
                    "secant_cycle_vertices_m": 10,
                    "passant_line_counts": {"n2": 35},
                    "shape": "ten cycle vertices and every passant meets the support in 0 or 2 points",
                },
            ],
        },
        "m6_four_set_orbits": four_set_records,
        "m10_secant_pair_orbits": {
            "orbit_count": len(pair_orbit_records),
            "total_pairs": 595,
            "depth_mass": {str(depth): mass for depth, mass in sorted(depth_mass.items())},
            "maximum_surviving_prefix_depth": maximum_depth,
            "records": pair_orbit_records,
        },
        "simpler_dual_obstructions": {
            "linear_separator_coefficient_and_augmented_ranks": linear_ranks,
            "quadratic_s2_subset_size": len(quadratic_rows),
            "quadratic_s2_coefficient_and_augmented_ranks": quadratic_ranks,
        },
        "certified_conclusion": (
            "both weight-ten global shapes are impossible using moments, "
            "line caps, secant degrees, and stabilizer orbits; no syndrome "
            "meet-in-the-middle enumeration is used"
        ),
        "checked_domain": {
            "projective_group_elements": len(group),
            "four_subsets_on_standard_passant": 35,
            "four_set_stabilizer_orbits": len(four_set_records),
            "secant_neighbor_pairs_at_base": 595,
            "secant_pair_stabilizer_orbits": len(pair_orbit_records),
            "all_orbits_stop_before_seven_fibres": True,
        },
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--write", type=Path)
    parser.add_argument("--check", type=Path)
    args = parser.parse_args()
    assert not (args.write and args.check)
    result = compute()
    rendered = json.dumps(result, indent=2, sort_keys=True) + "\n"
    if args.write:
        args.write.write_text(rendered)
    elif args.check:
        assert args.check.read_text() == rendered
        print("q=13 weight-ten moment certificate: PASS")
    else:
        print(rendered, end="")


if __name__ == "__main__":
    main()
