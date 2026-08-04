#!/usr/bin/env python3
"""Exact toric--octahedral minimum-geometry certificate at q=13."""

from __future__ import annotations

import argparse
import json
from collections import Counter
from pathlib import Path


Q = 13
P1 = tuple(range(Q + 1))  # Q denotes infinity.

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


def internal_points() -> list[tuple[int, int, int]]:
    squares = {value * value % Q for value in range(1, Q)}
    projective = (
        [(1, y, z) for y in range(Q) for z in range(Q)]
        + [(0, 1, z) for z in range(Q)]
        + [(0, 0, 1)]
    )
    return [
        point
        for point in projective
        if (point[1] * point[1] - point[0] * point[2]) % Q
        not in squares | {0}
    ]


def projective_points() -> list[tuple[int, int, int]]:
    return (
        [(1, y, z) for y in range(Q) for z in range(Q)]
        + [(0, 1, z) for z in range(Q)]
        + [(0, 0, 1)]
    )


def passant_lines() -> list[tuple[int, int, int]]:
    squares = {value * value % Q for value in range(1, Q)}
    return [
        line
        for line in projective_points()
        if (line[1] * line[1] - 4 * line[0] * line[2]) % Q
        not in squares | {0}
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


def rho(first: tuple[int, int, int], second: tuple[int, int, int]) -> int:
    x, y, z = first
    u, v, w = second
    beta = (2 * y * v - x * w - z * u) % Q
    first_delta = (y * y - x * z) % Q
    second_delta = (v * v - u * w) % Q
    return beta * beta * pow(first_delta * second_delta, -1, Q) % Q


def relation_matrix(
    points: list[tuple[int, int, int]], value: int
) -> list[int]:
    return [
        sum(
            1 << j
            for j, second in enumerate(points)
            if i != j and rho(first, second) == value
        )
        for i, first in enumerate(points)
    ]


def identity(size: int) -> list[int]:
    return [1 << index for index in range(size)]


def binary_add(*matrices: list[int]) -> list[int]:
    return [xor_all(rows) for rows in zip(*matrices)]


def xor_all(values: tuple[int, ...]) -> int:
    answer = 0
    for value in values:
        answer ^= value
    return answer


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


def coordinate_basis(rows: list[int]) -> tuple[list[int], dict[int, tuple[int, int]]]:
    selected: list[int] = []
    pivots: dict[int, tuple[int, int]] = {}
    for original in rows:
        row = original
        coefficients = 1 << len(selected)
        while row:
            pivot = row.bit_length() - 1
            if pivot in pivots:
                reduced, change = pivots[pivot]
                row ^= reduced
                coefficients ^= change
            else:
                pivots[pivot] = (row, coefficients)
                selected.append(original)
                break
    return selected, pivots


def coordinates(vector: int, pivots: dict[int, tuple[int, int]]) -> int:
    answer = 0
    while vector:
        pivot = vector.bit_length() - 1
        reduced, change = pivots[pivot]
        vector ^= reduced
        answer ^= change
    return answer


def permute_vector(vector: int, permutation: list[int]) -> int:
    answer = 0
    while vector:
        bit = vector & -vector
        answer |= 1 << permutation[bit.bit_length() - 1]
        vector ^= bit
    return answer


def gf8_multiply(first: int, second: int) -> int:
    answer = 0
    left = first
    right = second
    while right:
        if right & 1:
            answer ^= left
        right >>= 1
        left <<= 1
        if left & 8:
            left ^= 0b1101  # alpha^3 + alpha^2 + 1
    return answer


def gf8_power(value: int, exponent: int) -> int:
    answer = 1
    while exponent:
        if exponent & 1:
            answer = gf8_multiply(answer, value)
        value = gf8_multiply(value, value)
        exponent >>= 1
    return answer


def gf8_rank(rows: list[list[int]]) -> int:
    matrix = [row[:] for row in rows]
    pivot_row = 0
    for column in range(len(matrix[0]) if matrix else 0):
        pivot = next(
            (row for row in range(pivot_row, len(matrix)) if matrix[row][column]),
            None,
        )
        if pivot is None:
            continue
        matrix[pivot_row], matrix[pivot] = matrix[pivot], matrix[pivot_row]
        inverse = gf8_power(matrix[pivot_row][column], 6)
        matrix[pivot_row] = [gf8_multiply(inverse, value) for value in matrix[pivot_row]]
        for row in range(len(matrix)):
            if row != pivot_row and matrix[row][column]:
                scale = matrix[row][column]
                matrix[row] = [
                    value ^ gf8_multiply(scale, pivot_value)
                    for value, pivot_value in zip(matrix[row], matrix[pivot_row])
                ]
        pivot_row += 1
    return pivot_row


def gf8_matrix_multiply(first: list[list[int]], second: list[list[int]]) -> list[list[int]]:
    size = len(first)
    return [
        [
            xor_all(
                tuple(gf8_multiply(first[row][middle], second[middle][column]) for middle in range(size))
            )
            for column in range(size)
        ]
        for row in range(size)
    ]


def gf8_matrix_add(first: list[list[int]], second: list[list[int]]) -> list[list[int]]:
    return [[a ^ b for a, b in zip(row_a, row_b)] for row_a, row_b in zip(first, second)]


def gf8_scalar_matrix(value: int, size: int) -> list[list[int]]:
    return [[value if row == column else 0 for column in range(size)] for row in range(size)]


def gf8_polynomial_remainder(dividend: list[int], divisor: list[int]) -> list[int]:
    answer = dividend[:]
    while len(answer) >= len(divisor):
        if answer[-1]:
            scale = answer[-1]
            offset = len(answer) - len(divisor)
            for index, value in enumerate(divisor):
                answer[offset + index] ^= gf8_multiply(scale, value)
        while answer and answer[-1] == 0:
            answer.pop()
    return answer


def gf8_evaluate_matrix(polynomial: list[int], matrix: list[list[int]]) -> list[list[int]]:
    size = len(matrix)
    answer = [[0] * size for _ in range(size)]
    power = gf8_scalar_matrix(1, size)
    for coefficient in polynomial:
        if coefficient:
            answer = gf8_matrix_add(
                answer,
                [[gf8_multiply(coefficient, value) for value in row] for row in power],
            )
        power = gf8_matrix_multiply(power, matrix)
    return answer


def mobius(matrix: tuple[int, int, int, int], point: int) -> int:
    a, b, c, d = matrix
    if point == Q:
        return Q if c == 0 else a * pow(c, -1, Q) % Q
    denominator = (c * point + d) % Q
    return Q if denominator == 0 else (a * point + b) * pow(denominator, -1, Q) % Q


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


def projective_order(matrix: tuple[int, int, int, int]) -> int:
    power = (1, 0, 0, 1)
    for order in range(1, 25):
        power = multiply(power, matrix)
        if power == (1, 0, 0, 1):
            return order
    raise AssertionError(matrix)


def split_orbit_invariant(point: tuple[int, int, int]) -> int:
    x, y, z = point
    assert x and z
    return y * y * pow(x * z, -1, Q) % Q


def point_involution(point: tuple[int, int, int]) -> tuple[int, int, int, int]:
    x, y, z = point
    return canonical((y, -x % Q, z, -y % Q))


def matching_profile(
    point: tuple[int, int, int], partition: list[tuple]
) -> tuple[int, ...]:
    involution = point_involution(point)
    return tuple(
        sum(mobius(involution, member) in orbit for member in orbit) // 2
        for orbit in partition
    )


def cycle_profile(matrix: tuple[int, int, int, int], domain: tuple) -> dict[int, int]:
    unseen = set(domain)
    lengths = []
    while unseen:
        seed = next(iter(unseen))
        cycle = []
        point = seed
        while point not in cycle:
            cycle.append(point)
            unseen.discard(point)
            point = mobius(matrix, point)
        lengths.append(len(cycle))
    return dict(sorted(Counter(lengths).items()))


def generated_subgroup(
    generators: tuple[tuple[int, int, int, int], ...]
) -> set[tuple[int, int, int, int]]:
    subgroup = {(1, 0, 0, 1)}
    queue = [(1, 0, 0, 1)]
    cursor = 0
    while cursor < len(queue):
        element = queue[cursor]
        cursor += 1
        for generator in generators:
            product = multiply(element, generator)
            if product not in subgroup:
                subgroup.add(product)
                queue.append(product)
    return subgroup


def incidence_columns(
    points: list[tuple[int, int, int]], lines: list[tuple[int, int, int]]
) -> list[int]:
    return [
        sum(
            1 << row
            for row, line in enumerate(lines)
            if sum(a * b for a, b in zip(line, point)) % Q == 0
        )
        for point in points
    ]


def support_syndrome(support: tuple, point_index: dict, columns: list[int]) -> int:
    return xor_all(tuple(columns[point_index[point]] for point in support))


def group_matrix_over_f8(
    element: tuple[int, int, int, int],
    points: list[tuple[int, int, int]],
    f8_basis: list[int],
    binary_pivots: dict[int, tuple[int, int]],
) -> list[list[int]]:
    point_index = {point: index for index, point in enumerate(points)}
    permutation = [point_index[act_quadratic(element, point)] for point in points]
    rows = []
    for vector in f8_basis:
        bits = coordinates(permute_vector(vector, permutation), binary_pivots)
        rows.append(
            [
                ((bits >> (3 * column)) & 1)
                | (((bits >> (3 * column + 1)) & 1) << 1)
                | (((bits >> (3 * column + 2)) & 1) << 2)
                for column in range(12)
            ]
        )
    return rows


def orbits(domain: tuple, subgroup: list, action) -> list[tuple]:
    unseen = set(domain)
    answer = []
    while unseen:
        seed = min(unseen)
        orbit = tuple(sorted({action(element, seed) for element in subgroup}))
        unseen.difference_update(orbit)
        answer.append(orbit)
    return sorted(answer, key=lambda orbit: (len(orbit), orbit))


def compute() -> dict[str, object]:
    group = projective_group()
    points = internal_points()
    lines = passant_lines()
    assert len(group) == 2184 and len(points) == 78
    assert len(lines) == 78
    point_index = {point: index for index, point in enumerate(points)}
    columns = incidence_columns(points, lines)
    element_orders = {element: projective_order(element) for element in group}

    families = []
    for representative in REPRESENTATIVES:
        support = frozenset(representative)
        stabilizer = [
            element
            for element in group
            if {act_quadratic(element, point) for point in support} == support
        ]
        point_orbits = orbits(P1, stabilizer, mobius)
        internal_orbits = orbits(tuple(points), stabilizer, act_quadratic)
        support_orbit_index = next(
            index
            for index, orbit in enumerate(internal_orbits)
            if frozenset(orbit) == support
        )
        support_orbit = {
            frozenset(act_quadratic(element, point) for point in support)
            for element in group
        }
        assert len(support_orbit) == len(group) // len(stabilizer)
        pair_counts: Counter[tuple[int, int]] = Counter()
        for word in support_orbit:
            indices = sorted(point_index[point] for point in word)
            for first_position, first in enumerate(indices):
                for second in indices[first_position + 1 :]:
                    pair_counts[first, second] += 1
        odd_pair_relation_values = {
            rho(points[first], points[second])
            for (first, second), count in pair_counts.items()
            if count % 2
        }
        assert len(odd_pair_relation_values) == 1
        gram_relation_value = odd_pair_relation_values.pop()
        assert all(
            (pair_counts[tuple(sorted((first, second)))] % 2)
            == (rho(points[first], points[second]) == gram_relation_value)
            for first in range(len(points))
            for second in range(first + 1, len(points))
        )
        toric_data = None
        octahedral_data = None
        if [len(orbit) for orbit in point_orbits] == [2, 12]:
            chord = point_orbits[0]
            transporter = next(
                element
                for element in group
                if {mobius(element, point) for point in chord} == {0, Q}
            )
            transformed_support = [
                act_quadratic(transporter, point) for point in support
            ]
            invariant_values = {
                split_orbit_invariant(point) for point in transformed_support
            }
            assert len(invariant_values) == 1
            invariant_value = invariant_values.pop()
            assert all(
                (point[1] * point[1] - invariant_value * point[0] * point[2])
                % Q
                == 0
                for point in transformed_support
            )
            toric_data = {
                "chord": list(chord),
                "normalizing_transporter": list(transporter),
                "support_invariant_y2_over_xz": invariant_value,
                "normalized_support_is_pencil_conic_y2_equals_r_xz_minus_chord": True,
            }
        else:
            orbit_profiles = [
                sorted({matching_profile(point, point_orbits) for point in orbit})
                for orbit in internal_orbits
            ]
            assert all(len(profiles) == 1 for profiles in orbit_profiles)
            support_point = next(iter(support))
            point_stabilizer = [
                element
                for element in stabilizer
                if act_quadratic(element, support_point) == support_point
            ]
            assert len(point_stabilizer) == 2
            stabilizing_involution = next(
                element for element in point_stabilizer if projective_order(element) == 2
            )
            octahedral_data = {
                "support_matching_profile_within_6_and_8_orbits": list(
                    matching_profile(next(iter(support)), point_orbits)
                ),
                "all_internal_orbit_matching_profiles": [
                    list(profiles[0]) for profiles in orbit_profiles
                ],
                "support_point_stabilizer_generator": list(stabilizing_involution),
                "support_point_stabilizer_P1_cycle_profiles": [
                    cycle_profile(stabilizing_involution, orbit)
                    for orbit in point_orbits
                ],
            }
            octahedral_support = tuple(
                point
                for point in points
                if matching_profile(point, point_orbits) == (2, 3)
            )
            assert frozenset(octahedral_support) == support
            assert support_syndrome(
                octahedral_support, point_index, columns
            ) == 0
            generator_pair = next(
                (first, second)
                for first in stabilizer
                for second in stabilizer
                if element_orders[first] == 4
                and element_orders[second] == 3
                and element_orders[multiply(first, second)] == 2
                and generated_subgroup((first, second)) == set(stabilizer)
            )
            octahedral_data.update(
                {
                    "intrinsic_cross_pair_count": 2,
                    "intrinsic_support_size": len(octahedral_support),
                    "intrinsic_support_has_zero_passant_syndrome": True,
                    "S4_generators_orders_4_3_product_2": [
                        list(generator) for generator in generator_pair
                    ],
                }
            )
        families.append(
            {
                "stabilizer_order": len(stabilizer),
                "minimum_word_orbit_size_by_orbit_stabilizer": len(group)
                // len(stabilizer),
                "stabilizer_type": (
                    "S4_octahedral" if toric_data is None else "D24_split_torus_normalizer"
                ),
                "P1_orbit_sizes": [len(orbit) for orbit in point_orbits],
                "P1_orbits": [list(orbit) for orbit in point_orbits],
                "internal_orbit_sizes": [len(orbit) for orbit in internal_orbits],
                "support_orbit_index": support_orbit_index,
                "support_point_stabilizer_order": len(stabilizer) // len(support),
                "orbit_Gram_relation_rho": gram_relation_value,
                "element_order_profile": dict(
                    sorted(Counter(projective_order(element) for element in stabilizer).items())
                ),
                "toric_data": toric_data,
                "octahedral_data": octahedral_data,
            }
        )

    assert [item["stabilizer_order"] for item in families] == [24] * 4
    assert [item["minimum_word_orbit_size_by_orbit_stabilizer"] for item in families] == [
        91
    ] * 4
    assert families[0]["P1_orbit_sizes"] == [6, 8]
    assert all(item["P1_orbit_sizes"] == [2, 12] for item in families[1:])

    standard_split_orbits = {
        value: tuple(
            point
            for point in points
            if point[0]
            and point[2]
            and split_orbit_invariant(point) == value
        )
        for value in range(Q)
    }
    standard_split_orbits = {
        value: orbit for value, orbit in standard_split_orbits.items() if orbit
    }
    assert {value: len(orbit) for value, orbit in standard_split_orbits.items()} == {
        0: 6,
        2: 12,
        3: 12,
        5: 12,
        9: 12,
        11: 12,
        12: 12,
    }
    standard_split_normalizer = [
        element
        for element in group
        if {mobius(element, point) for point in (0, Q)} == {0, Q}
    ]
    assert len(standard_split_normalizer) == 24
    normalizer_internal_orbits = orbits(
        tuple(points), standard_split_normalizer, act_quadratic
    )
    assert {
        frozenset(orbit) for orbit in normalizer_internal_orbits
    } == {frozenset(orbit) for orbit in standard_split_orbits.values()}

    def quadratic_character(value: int) -> int:
        if value % Q == 0:
            return 0
        return 1 if pow(value, (Q - 1) // 2, Q) == 1 else -1

    toric_orbit_table = []
    for value, orbit in sorted(standard_split_orbits.items()):
        syndrome_zero = support_syndrome(orbit, point_index, columns) == 0
        toric_orbit_table.append(
            {
                "invariant": value,
                "size": len(orbit),
                "quadratic_character_invariant": quadratic_character(value),
                "quadratic_character_invariant_minus_one": quadratic_character(
                    value - 1
                ),
                "zero_passant_syndrome": syndrome_zero,
            }
        )
    assert [
        row["invariant"] for row in toric_orbit_table if row["zero_passant_syndrome"]
    ] == [2, 5, 11]
    assert [item["toric_data"]["support_invariant_y2_over_xz"] for item in families[1:]] == [
        5,
        11,
        2,
    ]

    a0 = relation_matrix(points, 0)
    scalar_alpha_binary = relation_matrix(points, 9)
    projection_to_code = binary_add(
        identity(len(points)), binary_multiply(a0, a0)
    )
    binary_code_basis, _ = coordinate_basis(projection_to_code)
    assert len(binary_code_basis) == 36
    scalar_alpha_squared_binary = binary_multiply(
        scalar_alpha_binary, scalar_alpha_binary
    )
    f8_basis = []
    expanded_basis: list[int] = []
    for vector in binary_code_basis:
        packet = [
            vector,
            binary_multiply([vector], scalar_alpha_binary)[0],
            binary_multiply([vector], scalar_alpha_squared_binary)[0],
        ]
        if binary_rank(expanded_basis + packet) == len(expanded_basis) + 3:
            f8_basis.append(vector)
            expanded_basis.extend(packet)
    assert len(f8_basis) == 12 and len(expanded_basis) == 36
    selected_expanded_basis, expanded_pivots = coordinate_basis(expanded_basis)
    assert selected_expanded_basis == expanded_basis

    nonsplit_point = (1, 0, 2)
    nonsplit_normalizer = [
        element for element in group if act_quadratic(element, nonsplit_point) == nonsplit_point
    ]
    assert len(nonsplit_normalizer) == 28
    torus_generator = next(
        element for element in nonsplit_normalizer if element_orders[element] == 7
    )
    split_order_three = next(
        element
        for element in group
        if element_orders[element] == 3
        and sum(mobius(element, point) == point for point in P1) == 2
    )
    unipotent_order_thirteen = next(
        element for element in group if element_orders[element] == 13
    )
    torus_matrix = group_matrix_over_f8(
        torus_generator, points, f8_basis, expanded_pivots
    )
    split_three_matrix = group_matrix_over_f8(
        split_order_three, points, f8_basis, expanded_pivots
    )
    unipotent_matrix = group_matrix_over_f8(
        unipotent_order_thirteen, points, f8_basis, expanded_pivots
    )
    torus_eigenvalue_multiplicities = [
        12
        - gf8_rank(
            gf8_matrix_add(
                torus_matrix, gf8_scalar_matrix(gf8_power(2, exponent), 12)
            )
        )
        for exponent in range(7)
    ]
    assert sorted(torus_eigenvalue_multiplicities) == [1, 1, 2, 2, 2, 2, 2]
    missing_pair = [
        exponent
        for exponent, multiplicity in enumerate(torus_eigenvalue_multiplicities)
        if multiplicity == 1
    ]
    assert len(missing_pair) == 2 and sum(missing_pair) == 7

    split_three_fixed_dimension = 12 - gf8_rank(
        gf8_matrix_add(split_three_matrix, gf8_scalar_matrix(1, 12))
    )
    assert split_three_fixed_dimension == 4

    cyclotomic_thirteen = [1] * 13
    quartic_factors = []
    for encoded in range(8**4):
        coefficients = []
        value = encoded
        for _ in range(4):
            coefficients.append(value % 8)
            value //= 8
        candidate = coefficients + [1]
        if not gf8_polynomial_remainder(cyclotomic_thirteen, candidate):
            quartic_factors.append(candidate)
    assert len(quartic_factors) == 3
    order_thirteen_factor_kernel_dimensions = [
        12 - gf8_rank(gf8_evaluate_matrix(factor, unipotent_matrix))
        for factor in quartic_factors
    ]
    assert order_thirteen_factor_kernel_dimensions == [4, 4, 4]

    return {
        "schema": "paper-iv-minimum-geometry-v1",
        "field": Q,
        "group": "PGL(2,13)",
        "group_order": len(group),
        "internal_point_count": len(points),
        "families": families,
        "standard_split_torus_normalizer_order": len(standard_split_normalizer),
        "standard_split_torus_orbits": toric_orbit_table,
        "hidden_F8_module_Brauer_diagnostic": {
            "nonsplit_torus_normalizer_order": len(nonsplit_normalizer),
            "chosen_order_7_generator": list(torus_generator),
            "order_7_eigenvalue_multiplicities_for_alpha_powers_0_to_6": (
                torus_eigenvalue_multiplicities
            ),
            "cuspidal_missing_inverse_pair_exponents": missing_pair,
            "split_order_3_generator": list(split_order_three),
            "split_order_3_eigenvalue_multiplicities": [4, 4, 4],
            "unipotent_order_13_generator": list(unipotent_order_thirteen),
            "cyclotomic_13_quartic_factors_over_F8": quartic_factors,
            "order_13_factor_kernel_dimensions": (
                order_thirteen_factor_kernel_dimensions
            ),
            "Brauer_character_on_2_regular_types": {
                "identity": "12",
                "split_order_3": "0",
                "nonsplit_order_7_power_k": (
                    "-(zeta^(a*k)+zeta^(-a*k)), with {a,-a} the missing pair"
                ),
                "unipotent_order_13": "-1",
            },
            "identification": (
                "degree-12 cuspidal PGL(2,13) module for the missing inverse-pair "
                "character of the order-7 quotient of a nonsplit torus, up to Frobenius"
            ),
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
        print("q=13 minimum geometry certificate: PASS")
    else:
        print(rendered, end="")


if __name__ == "__main__":
    main()
