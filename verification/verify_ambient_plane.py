#!/usr/bin/env python3
"""Exact intrinsic conic-action and ambient-plane certificate at q=13."""

from __future__ import annotations

import argparse
import hashlib
import itertools
import json
import math
from collections import Counter
from pathlib import Path


Q = 13
IDENTITY = (1, 0, 0, 1)
P1 = tuple(range(Q + 1))  # Q denotes infinity.


def canonical(vector: tuple[int, ...]) -> tuple[int, ...]:
    first = next(value for value in vector if value % Q)
    inverse = pow(first, -1, Q)
    return tuple(value * inverse % Q for value in vector)


def projective_group() -> tuple[tuple[int, int, int, int], ...]:
    matrices = (
        [(1, b, c, d) for b in range(Q) for c in range(Q) for d in range(Q)]
        + [(0, 1, c, d) for c in range(Q) for d in range(Q)]
        + [(0, 0, 1, d) for d in range(Q)]
        + [(0, 0, 0, 1)]
    )
    return tuple(
        matrix
        for matrix in matrices
        if (matrix[0] * matrix[3] - matrix[1] * matrix[2]) % Q
    )


def multiply(
    first: tuple[int, int, int, int], second: tuple[int, int, int, int]
) -> tuple[int, int, int, int]:
    a, b, c, d = first
    e, f, g, h = second
    return canonical(
        (
            (a * e + b * g) % Q,
            (a * f + b * h) % Q,
            (c * e + d * g) % Q,
            (c * f + d * h) % Q,
        )
    )


def inverse(matrix: tuple[int, int, int, int]) -> tuple[int, int, int, int]:
    a, b, c, d = matrix
    return canonical((d, -b % Q, -c % Q, a))


def mobius(matrix: tuple[int, int, int, int], point: int) -> int:
    a, b, c, d = matrix
    if point == Q:
        return Q if c == 0 else a * pow(c, -1, Q) % Q
    numerator = (a * point + b) % Q
    denominator = (c * point + d) % Q
    return Q if denominator == 0 else numerator * pow(denominator, -1, Q) % Q


def permutation_order(permutation: tuple[int, ...]) -> int:
    seen: set[int] = set()
    answer = 1
    for start in range(len(permutation)):
        if start in seen:
            continue
        current = start
        length = 0
        while current not in seen:
            seen.add(current)
            current = permutation[current]
            length += 1
        answer = math.lcm(answer, length)
    return answer


def cyclic_subgroup(
    generator: tuple[int, int, int, int]
) -> frozenset[tuple[int, int, int, int]]:
    result = {IDENTITY}
    current = IDENTITY
    while True:
        current = multiply(current, generator)
        if current == IDENTITY:
            return frozenset(result)
        assert current not in result
        result.add(current)


def conjugate(
    matrix: tuple[int, int, int, int], subgroup: frozenset[tuple[int, int, int, int]]
) -> frozenset[tuple[int, int, int, int]]:
    matrix_inverse = inverse(matrix)
    return frozenset(
        multiply(multiply(matrix, element), matrix_inverse) for element in subgroup
    )


def conic_point(point: int) -> tuple[int, int, int]:
    return (1, 0, 0) if point == Q else canonical((point * point % Q, point, 1))


def internal_points() -> tuple[tuple[int, int, int], ...]:
    squares = {value * value % Q for value in range(1, Q)}
    projective = (
        [(1, y, z) for y in range(Q) for z in range(Q)]
        + [(0, 1, z) for z in range(Q)]
        + [(0, 0, 1)]
    )
    return tuple(
        point
        for point in projective
        if (point[1] * point[1] - point[0] * point[2]) % Q
        not in squares | {0}
    )


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


def determinant3(
    first: tuple[int, int, int],
    second: tuple[int, int, int],
    third: tuple[int, int, int],
) -> int:
    a, b, c = first
    d, e, f = second
    g, h, i = third
    return (a * (e * i - f * h) - b * (d * i - f * g) + c * (d * h - e * g)) % Q


def digest(value: object) -> str:
    rendered = json.dumps(value, sort_keys=True, separators=(",", ":"))
    return hashlib.sha256(rendered.encode()).hexdigest()


def compute() -> dict[str, object]:
    group = projective_group()
    group_set = set(group)
    group_index = {matrix: index for index, matrix in enumerate(group)}
    assert len(group) == Q * (Q * Q - 1) == 2184
    assert IDENTITY in group_set

    p1_permutations = {
        matrix: tuple(mobius(matrix, point) for point in P1) for matrix in group
    }
    order_histogram = Counter(permutation_order(permutation) for permutation in p1_permutations.values())
    order_thirteen = tuple(
        matrix for matrix in group if permutation_order(p1_permutations[matrix]) == 13
    )
    assert len(order_thirteen) == 168

    sylow_subgroups = sorted(
        {cyclic_subgroup(matrix) for matrix in order_thirteen},
        key=lambda subgroup: sorted(subgroup),
    )
    assert len(sylow_subgroups) == 14
    assert {len(subgroup) for subgroup in sylow_subgroups} == {13}
    sylow_index = {subgroup: index for index, subgroup in enumerate(sylow_subgroups)}

    fixed_points = []
    for subgroup in sylow_subgroups:
        fixed = [
            point
            for point in P1
            if all(mobius(element, point) == point for element in subgroup)
        ]
        assert len(fixed) == 1
        fixed_points.append(fixed[0])
    assert set(fixed_points) == set(P1)

    conjugation_permutations = []
    normalizer_sizes = []
    for matrix in group:
        permutation = tuple(
            sylow_index[conjugate(matrix, subgroup)] for subgroup in sylow_subgroups
        )
        conjugation_permutations.append(permutation)
    for index in range(len(sylow_subgroups)):
        normalizer_sizes.append(
            sum(permutation[index] == index for permutation in conjugation_permutations)
        )
    assert set(normalizer_sizes) == {Q * (Q - 1)} == {156}
    assert len(set(conjugation_permutations)) == len(group)

    for matrix, permutation in zip(group, conjugation_permutations):
        for index, image in enumerate(permutation):
            assert fixed_points[image] == mobius(matrix, fixed_points[index])

    base_triple = (0, 1, 2)
    triple_orbit = {
        tuple(permutation[index] for index in base_triple)
        for permutation in conjugation_permutations
    }
    assert len(triple_orbit) == len(group)
    assert triple_orbit == set(itertools.permutations(range(14), 3))

    sylow_rows = []
    for index, subgroup in enumerate(sylow_subgroups):
        generators = sorted(element for element in subgroup if element != IDENTITY)
        sylow_rows.append(
            {
                "index": index,
                "fixed_projective_point": fixed_points[index],
                "canonical_generator": list(generators[0]),
                "normalizer_order": normalizer_sizes[index],
            }
        )

    points = internal_points()
    assert len(points) == 78
    point_index = {point: index for index, point in enumerate(points)}
    point_actions = {
        matrix: tuple(point_index[act_quadratic(matrix, point)] for point in points)
        for matrix in group
    }

    matchings = []
    stabilizer_orders = []
    stabilizer_center_orders = []
    central_involutions = []
    for point_index_value, point in enumerate(points):
        stabilizer = tuple(
            matrix
            for matrix in group
            if point_actions[matrix][point_index_value] == point_index_value
        )
        stabilizer_set = set(stabilizer)
        assert len(stabilizer) == 2 * (Q + 1) == 28
        center = tuple(
            matrix
            for matrix in stabilizer
            if all(multiply(matrix, other) == multiply(other, matrix) for other in stabilizer)
        )
        assert len(center) == 2 and IDENTITY in center
        involution = next(matrix for matrix in center if matrix != IDENTITY)
        assert multiply(involution, involution) == IDENTITY
        assert involution in stabilizer_set

        permutation = conjugation_permutations[group_index[involution]]
        assert all(permutation[index] != index for index in range(14))
        assert all(permutation[permutation[index]] == index for index in range(14))
        matching = tuple(
            sorted(
                (index, permutation[index])
                for index in range(14)
                if index < permutation[index]
            )
        )
        assert len(matching) == 7
        for first, second in matching:
            assert determinant3(point, conic_point(fixed_points[first]), conic_point(fixed_points[second])) == 0

        matchings.append(matching)
        stabilizer_orders.append(len(stabilizer))
        stabilizer_center_orders.append(len(center))
        central_involutions.append(involution)

    assert len(set(central_involutions)) == 78
    assert len(set(matchings)) == 78
    chord_counts = Counter(pair for matching in matchings for pair in matching)
    all_chords = set(itertools.combinations(range(14), 2))
    assert set(chord_counts) == all_chords
    assert set(chord_counts.values()) == {(Q - 1) // 2} == {6}

    chord_stabilizer_orders = []
    for first, second in sorted(all_chords):
        chord_stabilizer_orders.append(
            sum(
                {permutation[first], permutation[second]} == {first, second}
                for permutation in conjugation_permutations
            )
        )
    assert set(chord_stabilizer_orders) == {2 * (Q - 1)} == {24}

    # The abstract group contains the rest of the plane as well.  Its 169
    # involutions are the off-conic points in the adjoint three-space.  The
    # conic polarity is intrinsic: two off-conic points are incident exactly
    # when the product of their involutions is an involution, while a conic
    # point is incident with an off-conic point exactly when that involution
    # normalizes the corresponding Sylow subgroup.
    element_orders = {
        matrix: permutation_order(p1_permutations[matrix]) for matrix in group
    }
    involutions = tuple(matrix for matrix in group if element_orders[matrix] == 2)
    assert len(involutions) == Q * Q == 169
    involution_group_indices = tuple(group_index[matrix] for matrix in involutions)
    involution_centralizer_sizes = {
        matrix: sum(
            multiply(matrix, other) == multiply(other, matrix) for other in group
        )
        for matrix in involutions
    }
    assert Counter(involution_centralizer_sizes.values()) == {28: 78, 24: 91}
    assert {
        matrix for matrix, size in involution_centralizer_sizes.items() if size == 28
    } == set(central_involutions)
    plane_point_count = len(sylow_subgroups) + len(involutions)
    assert plane_point_count == Q * Q + Q + 1 == 183

    def is_incident(first: int, second: int) -> bool:
        first_is_conic = first < 14
        second_is_conic = second < 14
        if first_is_conic and second_is_conic:
            return first == second
        if first_is_conic:
            involution_group_index = involution_group_indices[second - 14]
            return conjugation_permutations[involution_group_index][first] == first
        if second_is_conic:
            involution_group_index = involution_group_indices[first - 14]
            return conjugation_permutations[involution_group_index][second] == second
        first_involution = involutions[first - 14]
        second_involution = involutions[second - 14]
        return first != second and element_orders[multiply(first_involution, second_involution)] == 2

    polarity_rows = tuple(
        frozenset(second for second in range(plane_point_count) if is_incident(first, second))
        for first in range(plane_point_count)
    )
    assert {len(row) for row in polarity_rows} == {Q + 1} == {14}
    assert all(
        (second in polarity_rows[first]) == (first in polarity_rows[second])
        for first in range(plane_point_count)
        for second in range(plane_point_count)
    )
    common_polar_line_counts = Counter()
    for first, second in itertools.combinations(range(plane_point_count), 2):
        common = sum(
            first in polarity_rows[line] and second in polarity_rows[line]
            for line in range(plane_point_count)
        )
        common_polar_line_counts[common] += 1
    assert common_polar_line_counts == {1: math.comb(plane_point_count, 2)}

    def involution_point(matrix: tuple[int, int, int, int]) -> tuple[int, int, int]:
        a, b, c, d = matrix
        assert (a + d) % Q == 0
        return canonical((-b % Q, a, c))

    plane_coordinates = tuple(conic_point(point) for point in fixed_points) + tuple(
        involution_point(matrix) for matrix in involutions
    )
    assert len(set(plane_coordinates)) == plane_point_count
    standard_plane_points = set(
        [(1, y, z) for y in range(Q) for z in range(Q)]
        + [(0, 1, z) for z in range(Q)]
        + [(0, 0, 1)]
    )
    assert set(plane_coordinates) == standard_plane_points, (
        sorted(standard_plane_points - set(plane_coordinates)),
        sorted(set(plane_coordinates) - standard_plane_points),
    )

    def polar_pairing(
        first: tuple[int, int, int], second: tuple[int, int, int]
    ) -> int:
        x, y, z = first
        u, v, w = second
        return (2 * y * v - x * w - z * u) % Q

    assert all(
        is_incident(first, second)
        == (polar_pairing(plane_coordinates[first], plane_coordinates[second]) == 0)
        for first in range(plane_point_count)
        for second in range(plane_point_count)
    )
    conic_coordinate_indices = {
        index
        for index, (x, y, z) in enumerate(plane_coordinates)
        if (y * y - x * z) % Q == 0
    }
    assert conic_coordinate_indices == set(range(14))
    internal_involution_points = {
        involution_point(matrix) for matrix in central_involutions
    }
    assert internal_involution_points == set(points)
    external_involution_count = len(involutions) - len(central_involutions)
    assert external_involution_count == 91

    # A second, coordinate-free equivariance check: the central involution of
    # Stab(P) conjugates to the central involution of Stab(gP).
    central_by_point = dict(zip(points, central_involutions))
    for matrix in group:
        matrix_inverse = inverse(matrix)
        for point in points:
            image = act_quadratic(matrix, point)
            assert central_by_point[image] == multiply(
                multiply(matrix, central_by_point[point]), matrix_inverse
            )

    serialized_action = [list(permutation) for permutation in conjugation_permutations]
    serialized_incidence = [
        [list(pair) for pair in matching] for matching in matchings
    ]
    return {
        "schema": "paper-iv-ambient-plane-v1",
        "field": Q,
        "group": {
            "name": "PGL(2,13)",
            "order": len(group),
            "element_order_histogram": dict(sorted(order_histogram.items())),
            "order_13_element_count": len(order_thirteen),
        },
        "intrinsic_projective_line": {
            "sylow_13_subgroup_count": len(sylow_subgroups),
            "subgroup_order": 13,
            "normalizer_order": 156,
            "conjugation_action_kernel_order": 1,
            "ordered_distinct_triple_count": len(triple_orbit),
            "ordered_triple_stabilizer_order": 1,
            "action": "sharply 3-transitive",
            "sylow_subgroups": sylow_rows,
            "conjugation_action_sha256": digest(serialized_action),
            "coordinate_fixed_point_bijection_checked": True,
            "coordinate_equivariance_checked": True,
        },
        "intrinsic_secant_incidence": {
            "internal_vertex_count": len(points),
            "vertex_stabilizer_order": 28,
            "vertex_stabilizer_center_order": 2,
            "distinct_central_involutions": len(set(central_involutions)),
            "central_involution_cycle_type_on_conic_points": "2^7",
            "chord_count": len(chord_counts),
            "chords_per_internal_vertex": 7,
            "internal_vertices_per_chord": 6,
            "chord_stabilizer_order": 24,
            "secant_incidence_pair_count": sum(chord_counts.values()),
            "secant_incidence_sha256": digest(serialized_incidence),
            "geometric_collinearity_checked": True,
            "G_equivariance_checked": True,
        },
        "intrinsic_ambient_plane": {
            "point_count": plane_point_count,
            "line_count_via_polarity": len(polarity_rows),
            "conic_points_as_sylow_13_subgroups": 14,
            "off_conic_points_as_involutions": len(involutions),
            "internal_involution_class_size": len(central_involutions),
            "external_involution_class_size": external_involution_count,
            "involution_centralizer_size_histogram": {"24": 91, "28": 78},
            "points_per_line": Q + 1,
            "lines_through_point": Q + 1,
            "distinct_point_pairs_with_unique_line": sum(common_polar_line_counts.values()),
            "polarity_incidence_sha256": digest(
                [sorted(row) for row in polarity_rows]
            ),
            "projective_plane_axioms_checked": True,
            "coordinate_identification_with_PG_2_13_checked": True,
            "conic_identification_checked": True,
            "internal_point_identification_checked": True,
        },
        "boundary": {
            "recovered": [
                "the canonical 14-element Sylow-13 G-set",
                "its sharply 3-transitive projective-line action",
                "all 91 abstract chords",
                "the 78-by-91 internal-point/secant incidence",
                "all 183 points and lines of PG(2,13) with the conic polarity",
            ],
            "not_recovered_without_choices_or_more_data": [
                "a preferred ordered projective frame or F13 coordinate",
                "a preferred quadratic equation for a plane conic",
            ],
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
        print("q=13 ambient plane certificate: PASS")
    else:
        print(rendered, end="")


if __name__ == "__main__":
    main()
