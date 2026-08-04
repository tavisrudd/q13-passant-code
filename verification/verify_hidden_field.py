#!/usr/bin/env python3
"""Exact hidden-F8 diagnostic for the q=13 passant association scheme."""

from __future__ import annotations

import argparse
import json
from pathlib import Path


Q = 13
RELATIONS = (0, 1, 3, 9, 10, 12)


def internal_points() -> list[tuple[int, int, int]]:
    squares = {x * x % Q for x in range(1, Q)}
    projective = (
        [(1, y, z) for y in range(Q) for z in range(Q)]
        + [(0, 1, z) for z in range(Q)]
        + [(0, 0, 1)]
    )
    return [point for point in projective if delta(point) not in squares | {0}]


def delta(point: tuple[int, int, int]) -> int:
    x, y, z = point
    return (y * y - x * z) % Q


def rho(first: tuple[int, int, int], second: tuple[int, int, int]) -> int:
    x, y, z = first
    u, v, w = second
    beta = (2 * y * v - x * w - z * u) % Q
    return beta * beta * pow(delta(first) * delta(second), -1, Q) % Q


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
    return [1 << i for i in range(size)]


def add(*matrices: list[int]) -> list[int]:
    return [
        rows[0] ^ rows[1] if len(rows) == 2 else xor_all(rows)
        for rows in zip(*matrices)
    ]


def xor_all(values: tuple[int, ...]) -> int:
    result = 0
    for value in values:
        result ^= value
    return result


def multiply(first: list[int], second: list[int]) -> list[int]:
    product = []
    for support in first:
        row = 0
        while support:
            bit = support & -support
            row ^= second[bit.bit_length() - 1]
            support ^= bit
        product.append(row)
    return product


def rank_bitset(rows: list[int]) -> int:
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


def rank_dense(rows: list[int], width: int) -> int:
    matrix = [[(row >> column) & 1 for column in range(width)] for row in rows]
    pivot_row = 0
    for column in range(width):
        pivot = next(
            (row for row in range(pivot_row, len(matrix)) if matrix[row][column]),
            None,
        )
        if pivot is None:
            continue
        matrix[pivot_row], matrix[pivot] = matrix[pivot], matrix[pivot_row]
        for row in range(len(matrix)):
            if row != pivot_row and matrix[row][column]:
                matrix[row] = [a ^ b for a, b in zip(matrix[row], matrix[pivot_row])]
        pivot_row += 1
        if pivot_row == len(matrix):
            break
    return pivot_row


def checked_rank(rows: list[int], width: int) -> int:
    first = rank_bitset(rows)
    second = rank_dense(rows, width)
    assert first == second
    return first


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
    result = 0
    while vector:
        pivot = vector.bit_length() - 1
        assert pivot in pivots
        reduced, change = pivots[pivot]
        vector ^= reduced
        result ^= change
    return result


def permute_vector(vector: int, permutation: list[int]) -> int:
    result = 0
    while vector:
        bit = vector & -vector
        result |= 1 << permutation[bit.bit_length() - 1]
        vector ^= bit
    return result


def flatten_matrix(matrix: list[int], size: int) -> int:
    return sum(row << (size * index) for index, row in enumerate(matrix))


def action_algebra_dimension(
    generators: list[list[int]], size: int, *, side: str
) -> int:
    pivots: dict[int, int] = {}
    queue: list[list[int]] = []

    def insert(matrix: list[int]) -> None:
        vector = flatten_matrix(matrix, size)
        while vector:
            pivot = (
                vector.bit_length() - 1
                if side == "right"
                else (vector & -vector).bit_length() - 1
            )
            if pivot in pivots:
                vector ^= pivots[pivot]
            else:
                pivots[pivot] = vector
                queue.append(matrix)
                return

    insert(identity(size))
    cursor = 0
    while cursor < len(queue):
        matrix = queue[cursor]
        cursor += 1
        for generator in generators:
            insert(
                multiply(matrix, generator)
                if side == "right"
                else multiply(generator, matrix)
            )
    return len(pivots)


def canonical_projective(vector: tuple[int, ...]) -> tuple[int, ...]:
    first = next(value for value in vector if value)
    inverse = pow(first, -1, Q)
    return tuple(value * inverse % Q for value in vector)


def multiply_projective(
    first: tuple[int, int, int, int], second: tuple[int, int, int, int]
) -> tuple[int, int, int, int]:
    a, b, c, d = first
    e, f, g, h = second
    return canonical_projective(
        (
            (a * e + b * g) % Q,
            (a * f + b * h) % Q,
            (c * e + d * g) % Q,
            (c * f + d * h) % Q,
        )
    )


def act_projective(
    matrix: tuple[int, int, int, int], point: tuple[int, int, int]
) -> tuple[int, int, int]:
    a, b, c, d = matrix
    x, y, z = point
    return canonical_projective(
        (
            (a * a * x + 2 * a * b * y + b * b * z) % Q,
            (a * c * x + (a * d + b * c) * y + b * d * z) % Q,
            (c * c * x + 2 * c * d * y + d * d * z) % Q,
        )
    )


def mobius(matrix: tuple[int, int, int, int], point: int) -> int:
    a, b, c, d = matrix
    if point == Q:
        return Q if c == 0 else a * pow(c, -1, Q) % Q
    denominator = (c * point + d) % Q
    return (
        Q
        if denominator == 0
        else (a * point + b) * pow(denominator, -1, Q) % Q
    )


def conic_heart_matrix(matrix: tuple[int, int, int, int]) -> list[int]:
    permutation = [mobius(matrix, point) for point in range(Q + 1)]
    rows = []
    for point in range(Q - 1):
        vector = (1 << permutation[point]) ^ (1 << permutation[Q])
        last = (vector >> (Q - 1)) & 1
        rows.append(
            sum((((vector >> index) & 1) ^ last) << index for index in range(Q - 1))
        )
    return rows


def compute() -> dict[str, object]:
    points = internal_points()
    size = len(points)
    assert size == 78
    matrices = {value: relation_matrix(points, value) for value in RELATIONS}
    assert all(matrix == list_transpose(matrix, size) for matrix in matrices.values())

    one = identity(size)
    a0 = matrices[0]
    b = matrices[9]
    b2 = multiply(b, b)
    b3 = multiply(b2, b)
    b4 = multiply(b2, b2)
    b_plus_one = add(b, one)
    a0_squared = multiply(a0, a0)
    projection_to_k = add(one, a0_squared)

    assert b2 == matrices[10]
    assert b4 == matrices[12]
    assert multiply(a0, b) == [0] * size
    assert a0_squared == add(one, b, b2, b4)
    cubic = add(b3, b2, one)
    assert multiply(b_plus_one, cubic) == a0_squared
    assert cubic == a0_squared
    assert multiply(projection_to_k, projection_to_k) == projection_to_k
    assert multiply(projection_to_k, b) == b
    assert multiply(b, projection_to_k) == b

    powers = {0: projection_to_k, 1: b}
    for exponent in range(2, 8):
        powers[exponent] = multiply(powers[exponent - 1], b)
    assert powers[7] == projection_to_k
    assert add(b, b2, b4) == projection_to_k
    assert add(
        multiply(b, b2), multiply(b, b4), multiply(b2, b4)
    ) == [0] * size
    assert multiply(multiply(b, b2), b4) == projection_to_k
    assert all(
        powers[exponent] == list_transpose(powers[exponent], size)
        for exponent in range(7)
    )
    assert all(row.bit_count() % 2 == 0 for row in projection_to_k)
    assert all(
        add(*[matrix for bit, matrix in zip((1, 2, 4), (projection_to_k, b, b2)) if mask & bit])
        != [0] * size
        for mask in range(1, 8)
    )

    zero = [0] * size
    restrictions = {
        "I": multiply(one, projection_to_k),
        **{
            f"A{value}": multiply(matrices[value], projection_to_k)
            for value in RELATIONS
        },
    }
    assert restrictions == {
        "I": projection_to_k,
        "A0": zero,
        "A1": zero,
        "A3": zero,
        "A9": b,
        "A10": b2,
        "A12": b4,
    }

    ranks = {
        "A0": checked_rank(a0, size),
        "A9": checked_rank(b, size),
        "A10": checked_rank(b2, size),
        "A12": checked_rank(b4, size),
        "B_plus_I": checked_rank(b_plus_one, size),
        "stack_A0_B_plus_I": checked_rank(a0 + b_plus_one, size),
    }
    kernel_dimension = size - ranks["A0"]
    fixed_dimension = size - ranks["stack_A0_B_plus_I"]
    assert ranks == {
        "A0": 42,
        "A9": 36,
        "A10": 36,
        "A12": 36,
        "B_plus_I": 78,
        "stack_A0_B_plus_I": 78,
    }
    assert kernel_dimension == 36
    assert fixed_dimension == 0

    group_generators = [(1, 1, 0, 1), (0, 1, 1, 0), (2, 0, 0, 1)]
    generated_group = {(1, 0, 0, 1)}
    group_queue = [(1, 0, 0, 1)]
    cursor = 0
    while cursor < len(group_queue):
        element = group_queue[cursor]
        cursor += 1
        for generator in group_generators:
            product = multiply_projective(element, generator)
            if product not in generated_group:
                generated_group.add(product)
                group_queue.append(product)
    assert len(generated_group) == 2184

    k_basis, k_pivots = coordinate_basis(projection_to_k)
    assert len(k_basis) == 36
    point_index = {point: index for index, point in enumerate(points)}
    k_generators = []
    for generator in group_generators:
        permutation = [
            point_index[act_projective(generator, point)] for point in points
        ]
        k_generators.append(
            [
                coordinates(permute_vector(vector, permutation), k_pivots)
                for vector in k_basis
            ]
        )
    scalar_alpha = [
        coordinates(multiply([vector], b)[0], k_pivots) for vector in k_basis
    ]
    assert all(
        multiply(generator, scalar_alpha) == multiply(scalar_alpha, generator)
        for generator in k_generators
    )
    k_algebra_dimensions = {
        side: action_algebra_dimension(k_generators, 36, side=side)
        for side in ("right", "left")
    }
    assert k_algebra_dimensions == {"right": 432, "left": 432}

    heart_generators = [conic_heart_matrix(generator) for generator in group_generators]
    heart_algebra_dimensions = {
        side: action_algebra_dimension(heart_generators, 12, side=side)
        for side in ("right", "left")
    }
    assert heart_algebra_dimensions == {"right": 144, "left": 144}

    return {
        "schema": "paper-iv-hidden-f8-v1",
        "field": 13,
        "point_count": size,
        "relation_valencies": {
            str(value): matrices[value][0].bit_count() for value in RELATIONS
        },
        "ranks_over_F2": ranks,
        "kernel_A0_dimension_over_F2": kernel_dimension,
        "kernel_A0_intersect_kernel_B_plus_I_dimension": fixed_dimension,
        "kernel_A0_dimension_over_F8": kernel_dimension // 3,
        "PGL2_generators": [list(generator) for generator in group_generators],
        "PGL2_generated_order": len(generated_group),
        "code_module_action_algebra_dimensions_over_F2": k_algebra_dimensions,
        "full_End_F8_dimension_over_F2": 12 * 12 * 3,
        "ordinary_14_point_heart_action_algebra_dimensions_over_F2": (
            heart_algebra_dimensions
        ),
        "representation_verdict": (
            "absolutely irreducible over F8; minimal definition field F8; "
            "not the ordinary 14-point deleted permutation heart"
        ),
        "modular_Bose_Mesner_action_on_kernel_A0": {
            "I": "1",
            "A0": "0",
            "A1": "0",
            "A3": "0",
            "A9": "alpha",
            "A10": "alpha^2",
            "A12": "alpha^4=1+alpha+alpha^2",
            "alpha_relation": "alpha^3+alpha^2+1=0",
        },
        "verified_projector_identities": [
            "A0^2=I+A9^2+A9^3",
            "e_K=I+A0^2",
            "e_K^2=e_K",
            "A9^7=e_K",
        ],
        "verified_Frobenius_packet_identities": [
            "A9+A10+A12=e_K",
            "A9*A10+A9*A12+A10*A12=0",
            "A9*A10*A12=e_K",
        ],
        "verified_binary_form_properties": [
            "e_K is symmetric of rank 36",
            "every vector in image(e_K)=K has even weight",
            "all F8 scalar operators are self-adjoint",
        ],
        "verified_matrix_identities": [
            "A0^2=I+A9+A10+A12",
            "A0*A9=0",
            "A9^2=A10",
            "A10^2=A12",
            "A12^2=A9",
            "(A9+I)*(A9^3+A9^2+I)=A0^2",
        ],
        "independent_rank_implementations": ["bitset_echelon", "dense_rref"],
    }


def list_transpose(matrix: list[int], size: int) -> list[int]:
    return [
        sum(1 << row for row in range(size) if matrix[row] >> column & 1)
        for column in range(size)
    ]


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
        print("q=13 hidden-field certificate: PASS")
    else:
        print(rendered, end="")


if __name__ == "__main__":
    main()
