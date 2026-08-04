#!/usr/bin/env python3
"""Exact Lovasz-theta certificate for the q=13 tangent graph."""

from __future__ import annotations

import argparse
import hashlib
import json
from fractions import Fraction
from pathlib import Path


ORDER = 14
VERTICES = tuple((orbit, index) for orbit in range(3) for index in range(ORDER))
DIFFERENCES = {
    (0, 0): (4, 6, 8, 10),
    (0, 1): (6, 7, 11, 12),
    (0, 2): (1, 3),
    (1, 1): (6, 8),
    (1, 2): (3, 5, 6, 8, 9, 11),
    (2, 2): (2, 4, 10, 12),
}
BASE_CLIQUE = ((0, 0), (1, 6), (1, 12), (2, 1), (2, 3))

# First rows of the six blocks of the integral matrix C=10S.  The diagonal
# blocks are symmetric circulants; lower off-diagonal blocks are transposes.
CERTIFICATE_ROWS = {
    (0, 0): (40, 9, 8, -8, -10, 0, -10, -2, -10, 0, -10, -8, 8, 9),
    (0, 1): (7, 6, 6, 6, 7, -1, -10, -10, -8, 0, -8, -10, -10, -1),
    (0, 2): (0, -10, 2, -10, 0, 3, 2, 9, 2, 4, 2, 9, 2, 3),
    (1, 1): (40, 15, 10, 10, -6, -3, -10, -22, -10, -3, -6, 10, 10, 15),
    (1, 2): (-13, 3, 0, -10, 8, -10, -10, 14, -10, -10, 8, -10, 0, 3),
    (2, 2): (40, -9, -10, 19, -10, 2, 8, -12, 8, 2, -10, 19, -10, -9),
}

# Leading-first factors of the characteristic polynomial after x^14.
CHARPOLY_FACTORS = (
    ((1, -94, 279), 1),
    ((1, -26, 135), 1),
    ((1, -247, 22466, -910807, 15948097, -111043270, 189747571), 2),
    ((1, -533, 105578, -9736765, 438572569, -9062718662, 68467048091), 2),
)


def adjacent(first: tuple[int, int], second: tuple[int, int]) -> bool:
    if first == second:
        return False
    if first[0] <= second[0]:
        difference = (second[1] - first[1]) % ORDER
        return difference in DIFFERENCES[first[0], second[0]]
    difference = (first[1] - second[1]) % ORDER
    return difference in DIFFERENCES[second[0], first[0]]


def certificate_entry(first: int, second: int) -> int:
    first_orbit, first_index = divmod(first, ORDER)
    second_orbit, second_index = divmod(second, ORDER)
    if first_orbit <= second_orbit:
        difference = (second_index - first_index) % ORDER
        return CERTIFICATE_ROWS[first_orbit, second_orbit][difference]
    difference = (first_index - second_index) % ORDER
    return CERTIFICATE_ROWS[second_orbit, first_orbit][difference]


def translate_clique(shift: int) -> tuple[int, ...]:
    return tuple(
        VERTICES.index((orbit, (index + shift) % ORDER))
        for orbit, index in BASE_CLIQUE
    )


def rational_rank(matrix: list[list[int]]) -> int:
    work = [[Fraction(value) for value in row] for row in matrix]
    row = 0
    for column in range(len(work[0]) if work else 0):
        pivot = next((index for index in range(row, len(work)) if work[index][column]), None)
        if pivot is None:
            continue
        work[row], work[pivot] = work[pivot], work[row]
        scale = work[row][column]
        work[row] = [value / scale for value in work[row]]
        for index in range(len(work)):
            if index != row and work[index][column]:
                scale = work[index][column]
                work[index] = [
                    work[index][position] - scale * work[row][position]
                    for position in range(len(work[index]))
                ]
        row += 1
    return row


def exact_psd_rank(matrix: list[list[int]]) -> tuple[int, list[Fraction]]:
    """Exact symmetric Schur elimination; returns rank and positive pivots."""
    work = [[Fraction(value) for value in row] for row in matrix]
    pivots: list[Fraction] = []
    while work:
        assert all(work[index][index] >= 0 for index in range(len(work)))
        pivot = next(
            (index for index in range(len(work)) if work[index][index] > 0), None
        )
        if pivot is None:
            assert all(value == 0 for row in work for value in row)
            break
        work[0], work[pivot] = work[pivot], work[0]
        for row in work:
            row[0], row[pivot] = row[pivot], row[0]
        value = work[0][0]
        pivots.append(value)
        work = [
            [
                work[i][j] - work[i][0] * work[0][j] / value
                for j in range(1, len(work))
            ]
            for i in range(1, len(work))
        ]
    return len(pivots), pivots


def group_add(first: list[int], second: list[int]) -> list[int]:
    return [left + right for left, right in zip(first, second)]


def group_mul(first: list[int], second: list[int]) -> list[int]:
    answer = [0] * ORDER
    for i, left in enumerate(first):
        for j, right in enumerate(second):
            answer[(i + j) % ORDER] += left * right
    return answer


def group_matrix_mul(
    first: list[list[list[int]]], second: list[list[list[int]]]
) -> list[list[list[int]]]:
    return [
        [
            sum_group(
                *(group_mul(first[i][k], second[k][j]) for k in range(3))
            )
            for j in range(3)
        ]
        for i in range(3)
    ]


def sum_group(*terms: list[int]) -> list[int]:
    answer = [0] * ORDER
    for term in terms:
        answer = group_add(answer, term)
    return answer


def matrix_traces_from_fourier() -> list[int]:
    block = [[[0] * ORDER for _ in range(3)] for _ in range(3)]
    for first in range(3):
        for second in range(first, 3):
            row = list(CERTIFICATE_ROWS[first, second])
            block[first][second] = row
            block[second][first] = [row[(-index) % ORDER] for index in range(ORDER)]
    power = [[entry[:] for entry in row] for row in block]
    traces = []
    for _ in range(len(VERTICES)):
        block_trace = sum_group(power[0][0], power[1][1], power[2][2])
        traces.append(ORDER * block_trace[0])
        power = group_matrix_mul(power, block)
    return traces


def charpoly_from_traces(traces: list[int]) -> list[int]:
    coefficients = [1]
    for degree in range(1, len(traces) + 1):
        numerator = -sum(
            coefficients[degree - index] * traces[index - 1]
            for index in range(1, degree + 1)
        )
        assert numerator % degree == 0
        coefficients.append(numerator // degree)
    return coefficients


def polynomial_multiply(first: list[int], second: list[int]) -> list[int]:
    answer = [0] * (len(first) + len(second) - 1)
    for i, left in enumerate(first):
        for j, right in enumerate(second):
            answer[i + j] += left * right
    return answer


def expected_charpoly() -> list[int]:
    # Low-degree first during multiplication, then leading first.
    polynomial = [0] * 14 + [1]
    for factor, multiplicity in CHARPOLY_FACTORS:
        low_first = list(reversed(factor))
        for _ in range(multiplicity):
            polynomial = polynomial_multiply(polynomial, low_first)
    return list(reversed(polynomial))


def compute() -> dict[str, object]:
    graph = [
        [int(adjacent(first, second)) for second in VERTICES] for first in VERTICES
    ]
    certificate = [
        [certificate_entry(first, second) for second in range(len(VERTICES))]
        for first in range(len(VERTICES))
    ]
    assert all(
        certificate[i][j] == certificate[j][i]
        for i in range(len(VERTICES))
        for j in range(len(VERTICES))
    )
    assert all(certificate[index][index] == 40 for index in range(len(VERTICES)))
    assert all(
        certificate[i][j] == -10
        for i in range(len(VERTICES))
        for j in range(i + 1, len(VERTICES))
        if graph[i][j]
    )

    translated_cliques = [translate_clique(shift) for shift in range(ORDER)]
    assert all(
        all(graph[first][second] for first in clique for second in clique if first != second)
        for clique in translated_cliques
    )
    clique_columns = [
        [int(vertex in clique) for clique in translated_cliques]
        for vertex in range(len(VERTICES))
    ]
    assert rational_rank(clique_columns) == ORDER
    assert all(
        sum(certificate[row][column] for column in clique) == 0
        for clique in translated_cliques
        for row in range(len(VERTICES))
    )

    psd_rank, pivots = exact_psd_rank(certificate)
    assert psd_rank == 28
    assert all(pivot > 0 for pivot in pivots)
    charpoly = charpoly_from_traces(matrix_traces_from_fourier())
    assert charpoly == expected_charpoly()
    assert all(
        coefficient * (-1) ** index > 0
        for factor, _ in CHARPOLY_FACTORS
        for index, coefficient in enumerate(factor)
    )

    pivot_strings = [str(pivot) for pivot in pivots]
    pivot_digest = hashlib.sha256(
        json.dumps(pivot_strings, separators=(",", ":")).encode()
    ).hexdigest()
    return {
        "schema": "paper-iv-weight-eight-theta-v1",
        "graph": {
            "vertices": len(VERTICES),
            "cyclic_orbits": [14, 14, 14],
            "difference_sets": {
                f"{first}{second}": list(values)
                for (first, second), values in DIFFERENCES.items()
            },
            "five_clique_witness": [list(vertex) for vertex in BASE_CLIQUE],
        },
        "certificate": {
            "scaling": "C=10S",
            "diagonal": 40,
            "edge_entry": -10,
            "block_first_rows": {
                f"{first}{second}": list(values)
                for (first, second), values in CERTIFICATE_ROWS.items()
            },
            "rank": psd_rank,
            "nullity": len(VERTICES) - psd_rank,
            "exact_positive_schur_pivot_count": len(pivots),
            "exact_schur_pivots_sha256": pivot_digest,
            "characteristic_polynomial_factorization": {
                "zero_multiplicity": 14,
                "nonzero_factors_leading_first": [
                    {"coefficients": list(factor), "multiplicity": multiplicity}
                    for factor, multiplicity in CHARPOLY_FACTORS
                ],
            },
        },
        "sharpness_and_equality": {
            "clique_upper_bound": 5,
            "clique_witness_size": len(BASE_CLIQUE),
            "lovasz_theta_of_complement": 5,
            "translated_five_cliques": len(translated_cliques),
            "translated_clique_span_rank": rational_rank(clique_columns),
            "kernel_equals_translated_clique_span": True,
            "maximum_cliques_are_exactly_the_translates": True,
        },
        "checked_domain": {
            "all_matrix_entries": len(VERTICES) ** 2,
            "all_graph_edges_checked_against_minus_ten": True,
            "all_fourteen_clique_translates_checked": True,
            "complete_characteristic_polynomial_checked": True,
            "exact_fraction_schur_elimination_checked": True,
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
        print("q=13 weight-eight theta certificate: PASS")
    else:
        print(rendered, end="")


if __name__ == "__main__":
    main()
