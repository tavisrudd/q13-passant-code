#!/usr/bin/env python3
"""Exact pair-concurrence closure and reconstruction for Paper IV."""

from __future__ import annotations

import argparse
import itertools
import json
from collections import Counter
from pathlib import Path


Q = 13
RELATIONS = (0, 1, 3, 9, 10, 12)
REPRESENTATIVES = (
    (
        (1, 0, 2), (1, 0, 5), (1, 1, 3), (1, 1, 6),
        (1, 2, 9), (1, 3, 4), (1, 3, 7), (1, 6, 5),
        (1, 8, 7), (1, 11, 2), (1, 11, 12), (1, 12, 6),
    ),
    (
        (1, 0, 2), (1, 0, 5), (1, 1, 3), (1, 1, 6),
        (1, 2, 12), (1, 5, 5), (1, 6, 2), (1, 6, 4),
        (1, 8, 4), (1, 8, 6), (1, 9, 9), (1, 12, 9),
    ),
    (
        (1, 0, 2), (1, 3, 2), (1, 4, 5), (1, 1, 8),
        (1, 4, 8), (1, 1, 7), (1, 7, 12), (1, 3, 3),
        (1, 9, 11), (1, 10, 11), (1, 0, 5), (1, 8, 7),
    ),
    (
        (1, 0, 2), (1, 0, 7), (1, 1, 6), (1, 2, 11),
        (1, 3, 7), (1, 3, 11), (1, 5, 1), (1, 5, 10),
        (1, 6, 4), (1, 7, 2), (1, 8, 1), (1, 8, 6),
    ),
)


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


def delta(point: tuple[int, int, int]) -> int:
    x, y, z = point
    return (y * y - x * z) % Q


def internal_points() -> list[tuple[int, int, int]]:
    squares = {value * value % Q for value in range(1, Q)}
    return [
        point
        for point in projective_points()
        if delta(point) not in squares | {0}
    ]


def rho(first: tuple[int, int, int], second: tuple[int, int, int]) -> int:
    x, y, z = first
    u, v, w = second
    beta = (2 * y * v - x * w - z * u) % Q
    return beta * beta * pow(delta(first) * delta(second), -1, Q) % Q


def pgl_matrices() -> list[tuple[int, int, int, int]]:
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


def act(
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


def coherent_refinement(colors: list[list[int]]) -> list[list[int]]:
    size = len(colors)
    signatures = []
    for first in range(size):
        for second in range(size):
            intersection_counts = Counter(
                (colors[first][middle], colors[middle][second])
                for middle in range(size)
            )
            signatures.append(
                (colors[first][second], tuple(sorted(intersection_counts.items())))
            )
    labels = {
        signature: label for label, signature in enumerate(sorted(set(signatures)))
    }
    return [
        [labels[signatures[first * size + second]] for second in range(size)]
        for first in range(size)
    ]


def incident(
    line: tuple[int, int, int], point: tuple[int, int, int]
) -> bool:
    return sum(a * b for a, b in zip(line, point)) % Q == 0


def binary_identity(size: int) -> list[int]:
    return [1 << index for index in range(size)]


def binary_add(*matrices: list[int]) -> list[int]:
    result = []
    for rows in zip(*matrices):
        value = 0
        for row in rows:
            value ^= row
        result.append(value)
    return result


def binary_multiply(first: list[int], second: list[int]) -> list[int]:
    product = []
    for support in first:
        row = 0
        while support:
            bit = support & -support
            row ^= second[bit.bit_length() - 1]
            support ^= bit
        product.append(row)
    return product


def binary_rank(rows: list[int]) -> int:
    pivots: dict[int, int] = {}
    for original in rows:
        row = original
        while row:
            pivot = row.bit_length() - 1
            if pivot in pivots:
                row ^= pivots[pivot]
            else:
                pivots[pivot] = row
                break
    return len(pivots)


def compute() -> dict[str, object]:
    points = internal_points()
    point_index = {point: index for index, point in enumerate(points)}
    matrices = pgl_matrices()
    assert len(points) == 78
    assert len(matrices) == 2184

    orbits = []
    for representative in REPRESENTATIVES:
        orbit = {
            frozenset(point_index[act(matrix, point)] for point in representative)
            for matrix in matrices
        }
        assert len(orbit) == 91
        orbits.append(orbit)
    minimum_supports = set().union(*orbits)
    assert len(minimum_supports) == 364
    point_degrees = Counter(point for support in minimum_supports for point in support)
    assert set(point_degrees.values()) == {56}

    pair_concurrence: Counter[tuple[int, int]] = Counter()
    for support in minimum_supports:
        pair_concurrence.update(itertools.combinations(sorted(support), 2))
    assert len(pair_concurrence) == 78 * 77 // 2
    concurrence_distribution = Counter(pair_concurrence.values())
    assert concurrence_distribution == Counter({6: 1092, 7: 546, 8: 273, 9: 546, 12: 546})

    rho_to_concurrence = {
        value: sorted(
            {
                pair_concurrence[tuple(sorted((first, second)))]
                for first in range(78)
                for second in range(first)
                if rho(points[first], points[second]) == value
            }
        )
        for value in RELATIONS
    }
    assert rho_to_concurrence == {
        0: [8], 1: [6], 3: [6], 9: [12], 10: [7], 12: [9]
    }

    initial = [
        [
            -1
            if first == second
            else pair_concurrence[tuple(sorted((first, second)))]
            for second in range(78)
        ]
        for first in range(78)
    ]
    first_refinement = coherent_refinement(initial)
    stable_refinement = coherent_refinement(first_refinement)
    assert first_refinement == stable_refinement
    assert len({color for row in initial for color in row}) == 6
    assert len({color for row in first_refinement for color in row}) == 7

    refined_colors_by_rho = {
        value: sorted(
            {
                first_refinement[first][second]
                for first in range(78)
                for second in range(first)
                if rho(points[first], points[second]) == value
            }
        )
        for value in RELATIONS
    }
    assert all(len(colors) == 1 for colors in refined_colors_by_rho.values())
    assert len({colors[0] for colors in refined_colors_by_rho.values()}) == 6

    common_sevens_by_rho = {}
    for value in (1, 3):
        counts = {
            sum(
                initial[first][middle] == 7 and initial[middle][second] == 7
                for middle in range(78)
            )
            for first in range(78)
            for second in range(first)
            if rho(points[first], points[second]) == value
        }
        common_sevens_by_rho[value] = sorted(counts)
    assert common_sevens_by_rho == {1: [2], 3: [4]}

    color_eight_neighborhoods = {
        frozenset(
            second
            for second in range(78)
            if second != first and initial[first][second] == 8
        )
        for first in range(78)
    }
    assert len(color_eight_neighborhoods) == 78
    assert {len(row) for row in color_eight_neighborhoods} == {7}

    squares = {value * value % Q for value in range(1, Q)}
    passants = [
        line
        for line in projective_points()
        if (line[1] * line[1] - 4 * line[0] * line[2]) % Q
        not in squares | {0}
    ]
    incidence_rows = {
        frozenset(index for index, point in enumerate(points) if incident(line, point))
        for line in passants
    }
    polar_rows = {
        frozenset(
            index
            for index, second in enumerate(points)
            if incident(canonical((-point[2] % Q, 2 * point[1] % Q, -point[0] % Q)), second)
        )
        for point in points
    }
    assert len(passants) == 78
    assert color_eight_neighborhoods == polar_rows == incidence_rows

    relation_matrices = {
        value: [
            sum(
                1 << second
                for second in range(78)
                if first != second and rho(points[first], points[second]) == value
            )
            for first in range(78)
        ]
        for value in RELATIONS
    }
    pair_parity = [
        sum(
            1 << second
            for second in range(78)
            if first != second and initial[first][second] % 2
        )
        for first in range(78)
    ]
    assert pair_parity == binary_add(relation_matrices[10], relation_matrices[12])
    assert binary_rank(pair_parity) == 36
    assert binary_rank(relation_matrices[0]) == 42
    assert binary_multiply(relation_matrices[0], pair_parity) == [0] * 78

    pair_parity_powers = {0: binary_identity(78)}
    for exponent in range(1, 8):
        pair_parity_powers[exponent] = binary_multiply(
            pair_parity_powers[exponent - 1], pair_parity
        )
    pair_parity_seventh = pair_parity_powers[7]
    code_projector = binary_add(
        binary_identity(78),
        binary_multiply(relation_matrices[0], relation_matrices[0]),
    )
    recovered_a9 = pair_parity_powers[3]
    assert pair_parity_seventh == code_projector
    assert binary_add(pair_parity, recovered_a9) == code_projector
    assert recovered_a9 == relation_matrices[9]
    assert pair_parity_powers[5] == relation_matrices[12]
    assert pair_parity_powers[6] == relation_matrices[10]
    assert pair_parity_powers == {
        0: binary_identity(78),
        1: binary_add(relation_matrices[10], relation_matrices[12]),
        2: binary_add(relation_matrices[9], relation_matrices[12]),
        3: relation_matrices[9],
        4: binary_add(relation_matrices[9], relation_matrices[10]),
        5: relation_matrices[12],
        6: relation_matrices[10],
        7: code_projector,
    }
    recovered_a9_squared = binary_multiply(recovered_a9, recovered_a9)
    recovered_a9_cubed = binary_multiply(recovered_a9_squared, recovered_a9)
    assert binary_add(
        recovered_a9_cubed, recovered_a9_squared, code_projector
    ) == [0] * 78

    return {
        "schema": "paper-iv-pair-reconstruction-v1",
        "point_count": len(points),
        "minimum_support_count": len(minimum_supports),
        "minimum_orbit_sizes": [len(orbit) for orbit in orbits],
        "weighted_1_section_point_degree": 56,
        "pair_concurrence_distribution": {
            str(value): count for value, count in sorted(concurrence_distribution.items())
        },
        "rho_to_pair_concurrence": {
            str(value): concurrences for value, concurrences in rho_to_concurrence.items()
        },
        "coherent_closure_color_counts_including_diagonal": [6, 7, 7],
        "common_concurrence_7_neighbors_for_concurrence_6_pair": {
            "rho_1": 2,
            "rho_3": 4,
        },
        "coherent_closure_verdict": (
            "one refinement splits rho=1 and rho=3 and recovers all six elliptic relations"
        ),
        "color_8_neighborhood_count": len(color_eight_neighborhoods),
        "color_8_neighborhood_size": 7,
        "color_8_neighborhoods_equal_passant_incidence_rows": True,
        "pair_concurrence_parity_operator": {
            "rank_over_F2": 36,
            "image": "binary code K",
            "P^7": "code projector e_K",
            "P^3": "A9=alpha",
            "P+P^3": "code projector e_K",
            "minimal_polynomial_on_K": "t^3+t+1",
            "characteristic_polynomial_on_F2^78": "t^42*(t^3+t+1)^12",
            "power_table": {
                "P^1": "A10+A12",
                "P^2": "A9+A12",
                "P^3": "A9",
                "P^4": "A9+A10",
                "P^5": "A12",
                "P^6": "A10",
                "P^7": "A9+A10+A12=e_K",
            },
            "recovered_field": "F2[P]/(P^3+P+e_K)=F8",
        },
        "automorphism_group_order_via_full_scheme_rigidity": 2184,
        "independent_closure_checks": [
            "full coherent signature refinement",
            "direct common-concurrence-7 count",
        ],
    }


def canonical_json(result: dict[str, object]) -> str:
    return json.dumps(result, indent=2, sort_keys=True) + "\n"


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--write", type=Path)
    parser.add_argument("--check", type=Path)
    args = parser.parse_args()
    rendered = canonical_json(compute())
    if args.write:
        args.write.write_text(rendered, encoding="utf-8")
    elif args.check:
        assert args.check.read_text(encoding="utf-8") == rendered
        print("q=13 pair reconstruction certificate: PASS")
    else:
        print(rendered, end="")


if __name__ == "__main__":
    main()
