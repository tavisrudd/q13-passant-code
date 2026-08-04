#!/usr/bin/env python3
"""Exact replay of the q=13 passant code and its minimum-layer reconstruction."""

from __future__ import annotations

import itertools
from collections import Counter


DIFFERENCES = {
    (0, 0): {4, 6, 8, 10},
    (0, 1): {6, 7, 11, 12},
    (0, 2): {1, 3},
    (1, 1): {6, 8},
    (1, 2): {3, 5, 6, 8, 9, 11},
    (2, 2): {2, 4, 10, 12},
}
VERTICES = [(orbit, index) for orbit in range(3) for index in range(14)]


def adjacent(first: tuple[int, int], second: tuple[int, int]) -> bool:
    first_orbit, first_index = first
    second_orbit, second_index = second
    if first_orbit > second_orbit:
        return adjacent(second, first)
    return (
        (second_index - first_index) % 14
        in DIFFERENCES[first_orbit, second_orbit]
    )


def verify_distance() -> None:
    q = 13
    squares = {value * value % q for value in range(1, q)}
    projective = (
        [(1, y, z) for y in range(q) for z in range(q)]
        + [(0, 1, z) for z in range(q)]
        + [(0, 0, 1)]
    )
    internal = [
        point
        for point in projective
        if (point[1] * point[1] - point[0] * point[2]) % q
        not in squares | {0}
    ]
    passants = [
        line
        for line in projective
        if (line[1] * line[1] - 4 * line[0] * line[2]) % q
        not in squares | {0}
    ]

    def incident(line: tuple[int, int, int], point: tuple[int, int, int]) -> bool:
        return sum(a * b for a, b in zip(line, point)) % q == 0

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
    passant_neighbors = set().union(*(set(fibre) for fibre in fibres))
    secant_neighbors = [
        index
        for index in range(78)
        if index != base and index not in passant_neighbors
    ]

    def xor_columns(indices: tuple[int, ...]) -> int:
        value = 0
        for index in indices:
            value ^= columns[index]
        return value

    def binary_rank(words: list[int]) -> int:
        basis: dict[int, int] = {}
        for word in words:
            value = word
            while value:
                pivot = value.bit_length() - 1
                if pivot in basis:
                    value ^= basis[pivot]
                else:
                    basis[pivot] = value
                    break
        return len(basis)

    for special in range(7):
        remaining = [index for index in range(7) if index != special]
        left = {
            xor_columns(choice)
            for choice in itertools.product(*(fibres[index] for index in remaining[:3]))
        }
        for triple in itertools.combinations(fibres[special], 3):
            target = columns[base] ^ xor_columns(triple)
            assert all(
                target ^ xor_columns(choice) not in left
                for choice in itertools.product(
                    *(fibres[index] for index in remaining[3:])
                )
            )

    left = {
        xor_columns(choice)
        for choice in itertools.product(*(fibres[index] for index in range(3)))
    }
    assert all(
        columns[base] ^ xor_columns(choice) ^ xor_columns(pair) not in left
        for choice in itertools.product(*(fibres[index] for index in range(3, 7)))
        for pair in itertools.combinations(secant_neighbors, 2)
    )

    solutions: set[frozenset[int]] = set()

    def add(indices: tuple[int, ...]) -> None:
        support = frozenset((base,) + indices)
        assert len(support) == 12 and xor_columns(tuple(support)) == 0
        solutions.add(support)

    # Exhaust the three possible numbers 0, 2, 4 of secant-join neighbors.
    for special in range(7):
        remaining = [index for index in range(7) if index != special]
        left_choices: dict[int, list[tuple[int, ...]]] = {}
        for head in itertools.product(*(fibres[index] for index in remaining[:3])):
            left_choices.setdefault(xor_columns(head), []).append(head)
        for five in itertools.combinations(fibres[special], 5):
            target = columns[base] ^ xor_columns(five)
            for tail in itertools.product(
                *(fibres[index] for index in remaining[3:])
            ):
                for head in left_choices.get(target ^ xor_columns(tail), []):
                    add(five + head + tail)

    for first, second in itertools.combinations(range(7), 2):
        remaining = [
            index for index in range(7) if index not in (first, second)
        ]
        left_choices = {}
        for head in itertools.product(*(fibres[index] for index in remaining[:2])):
            left_choices.setdefault(xor_columns(head), []).append(head)
        for first_triple in itertools.combinations(fibres[first], 3):
            for second_triple in itertools.combinations(fibres[second], 3):
                target = (
                    columns[base]
                    ^ xor_columns(first_triple)
                    ^ xor_columns(second_triple)
                )
                for tail in itertools.product(
                    *(fibres[index] for index in remaining[2:])
                ):
                    for head in left_choices.get(target ^ xor_columns(tail), []):
                        add(first_triple + second_triple + head + tail)

    secant_pairs = list(itertools.combinations(secant_neighbors, 2))
    for special in range(7):
        remaining = [index for index in range(7) if index != special]
        left_choices = {}
        for triple in itertools.combinations(fibres[special], 3):
            for head in itertools.product(
                *(fibres[index] for index in remaining[:3])
            ):
                choice = triple + head
                left_choices.setdefault(xor_columns(choice), []).append(choice)
        for tail in itertools.product(
            *(fibres[index] for index in remaining[3:])
        ):
            target = columns[base] ^ xor_columns(tail)
            for pair in secant_pairs:
                for head in left_choices.get(target ^ xor_columns(pair), []):
                    add(head + tail + pair)

    left_choices = {}
    for head in itertools.product(*(fibres[index] for index in range(3))):
        for first_pair in secant_pairs:
            left_choices.setdefault(
                xor_columns(head) ^ xor_columns(first_pair), []
            ).append((head, first_pair))
    for tail in itertools.product(*(fibres[index] for index in range(3, 7))):
        target = columns[base] ^ xor_columns(tail)
        for second_pair in secant_pairs:
            for head, first_pair in left_choices.get(
                target ^ xor_columns(second_pair), []
            ):
                if set(first_pair).isdisjoint(second_pair):
                    add(head + tail + first_pair + second_pair)

    assert len(solutions) == 56
    assert all(
        sum(index in secant_neighbors for index in support) == 4
        for support in solutions
    )

    witness_points = (
        (1, 0, 2), (1, 3, 2), (1, 4, 5), (1, 1, 8),
        (1, 4, 8), (1, 1, 7), (1, 7, 12), (1, 3, 3),
        (1, 9, 11), (1, 10, 11), (1, 0, 5), (1, 8, 7),
    )
    witness = tuple(internal.index(point) for point in witness_points)
    assert xor_columns(witness) == 0

    representatives = [
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
        witness_points,
        (
            (1, 0, 2), (1, 0, 7), (1, 1, 6), (1, 2, 11),
            (1, 3, 7), (1, 3, 11), (1, 5, 1), (1, 5, 10),
            (1, 6, 4), (1, 7, 2), (1, 8, 1), (1, 8, 6),
        ),
    ]

    def canonical(vector: tuple[int, ...]) -> tuple[int, ...]:
        first = next(value for value in vector if value)
        inverse = pow(first, -1, q)
        return tuple(value * inverse % q for value in vector)

    matrices = (
        [(1, b, c, d) for b in range(q) for c in range(q) for d in range(q)]
        + [(0, 1, c, d) for c in range(q) for d in range(q)]
        + [(0, 0, 1, d) for d in range(q)]
        + [(0, 0, 0, 1)]
    )
    matrices = [
        matrix
        for matrix in matrices
        if (matrix[0] * matrix[3] - matrix[1] * matrix[2]) % q
    ]

    def act(
        matrix: tuple[int, int, int, int], point: tuple[int, int, int]
    ) -> tuple[int, int, int]:
        a, b, c, d = matrix
        x, y, z = point
        return canonical(
            (
                (a * a * x + 2 * a * b * y + b * b * z) % q,
                (a * c * x + (a * d + b * c) * y + b * d * z) % q,
                (c * c * x + 2 * c * d * y + d * d * z) % q,
            )
        )

    def multiply(
        first: tuple[int, int, int, int],
        second: tuple[int, int, int, int],
    ) -> tuple[int, int, int, int]:
        a, b, c, d = first
        e, f, g, h = second
        return canonical(
            (
                (a * e + b * g) % q,
                (a * f + b * h) % q,
                (c * e + d * g) % q,
                (c * f + d * h) % q,
            )
        )

    def projective_order(matrix: tuple[int, int, int, int]) -> int:
        identity = (1, 0, 0, 1)
        power = identity
        for order in range(1, 25):
            power = multiply(power, matrix)
            if power == identity:
                return order
        raise AssertionError(matrix)

    covered = set()
    all_words = set()
    stabilizer_sizes = []
    stabilizer_order_profiles = []
    orbit_span_dimensions = []
    orbit_gram_dimensions = []
    orbit_gram_rows = []
    for representative in representatives:
        orbit = {
            frozenset(internal.index(act(matrix, point)) for point in representative)
            for matrix in matrices
        }
        stabilizer = [
            matrix
            for matrix in matrices
            if {act(matrix, point) for point in representative}
            == set(representative)
        ]
        stabilizer_sizes.append(len(stabilizer))
        stabilizer_order_profiles.append(
            Counter(projective_order(matrix) for matrix in stabilizer)
        )
        assert len(orbit) == 91
        orbit_span_dimensions.append(
            binary_rank(
                [sum(1 << index for index in support) for support in orbit]
            )
        )
        orbit_pair_counts: Counter[tuple[int, int]] = Counter()
        for support in orbit:
            orbit_pair_counts.update(itertools.combinations(sorted(support), 2))
        gram_rows = [
            sum(
                1 << second
                for second in range(78)
                if first != second
                and orbit_pair_counts[tuple(sorted((first, second)))] % 2
            )
            for first in range(78)
        ]
        orbit_gram_rows.append(gram_rows)
        orbit_gram_dimensions.append(binary_rank(gram_rows))
        all_words |= orbit
        base_slice = {support for support in orbit if base in support}
        assert len(base_slice) == 14
        assert covered.isdisjoint(base_slice)
        covered |= base_slice
    assert stabilizer_sizes == [24, 24, 24, 24]
    assert stabilizer_order_profiles == [
        Counter({2: 9, 3: 8, 4: 6, 1: 1}),
        Counter({2: 13, 12: 4, 3: 2, 4: 2, 6: 2, 1: 1}),
        Counter({2: 13, 12: 4, 3: 2, 4: 2, 6: 2, 1: 1}),
        Counter({2: 13, 12: 4, 3: 2, 4: 2, 6: 2, 1: 1}),
    ]
    assert orbit_span_dimensions == [36, 36, 36, 36]
    assert orbit_gram_dimensions == [36, 36, 36, 36]
    assert covered == solutions
    assert len(all_words) == 364
    assert binary_rank(
        [sum(1 << index for index in support) for support in all_words]
    ) == 36

    pair_concurrences: Counter[tuple[int, int]] = Counter()
    for support in all_words:
        for first, second in itertools.combinations(sorted(support), 2):
            pair_concurrences[first, second] += 1
    assert Counter(pair_concurrences.values()) == Counter(
        {6: 1092, 7: 546, 8: 273, 9: 546, 12: 546}
    )

    def passant_join(first: int, second: int) -> bool:
        return any(
            incident(line, internal[first]) and incident(line, internal[second])
            for line in passants
        )

    assert all(
        passant_join(first, second) == (concurrence in {7, 9, 12})
        for (first, second), concurrence in pair_concurrences.items()
    )

    triple_concurrences: Counter[tuple[int, int, int]] = Counter()
    for support in all_words:
        triple_concurrences.update(itertools.combinations(sorted(support), 3))
    profile_counts = Counter()
    pair_colors = {}
    for (first, second), concurrence in pair_concurrences.items():
        histogram = Counter(
            triple_concurrences[tuple(sorted((first, second, third)))]
            for third in range(78)
            if third not in (first, second)
        )
        color = concurrence, tuple(sorted(histogram.items()))
        pair_colors[first, second] = color
        profile_counts[color] += 1
    assert profile_counts == Counter(
        {
            (6, ((0, 26), (1, 42), (2, 6), (3, 2))): 546,
            (6, ((0, 32), (1, 28), (2, 16))): 546,
            (7, ((0, 25), (1, 36), (2, 13), (4, 2))): 546,
            (8, ((0, 16), (1, 40), (2, 20))): 273,
            (9, ((0, 18), (1, 32), (2, 24), (5, 2))): 546,
            (12, ((0, 7), (1, 34), (2, 27), (3, 4), (5, 4))): 546,
        }
    )

    adjacency = [
        sum(
            1 << second
            for second in range(78)
            if first != second
            and pair_concurrences[tuple(sorted((first, second)))] in {7, 9, 12}
        )
        for first in range(78)
    ]
    seven_cliques: list[frozenset[int]] = []

    def maximal_cliques(
        clique: list[int], candidates: int, excluded: int
    ) -> None:
        if not candidates and not excluded:
            if len(clique) >= 7:
                seven_cliques.append(frozenset(clique))
            return
        if len(clique) + candidates.bit_count() < 7:
            return
        union = candidates | excluded
        pivot = max(
            (index for index in range(78) if union >> index & 1),
            key=lambda index: (candidates & adjacency[index]).bit_count(),
            default=0,
        )
        extensions = candidates & ~adjacency[pivot]
        while extensions:
            bit = extensions & -extensions
            vertex = bit.bit_length() - 1
            maximal_cliques(
                clique + [vertex],
                candidates & adjacency[vertex],
                excluded & adjacency[vertex],
            )
            candidates &= ~bit
            excluded |= bit
            extensions &= ~bit

    maximal_cliques([], (1 << 78) - 1, 0)
    assert len(seven_cliques) == 1716
    reconstructed_rows = {
        clique
        for clique in seven_cliques
        if all(
            triple_concurrences[triple] == 0
            for triple in itertools.combinations(sorted(clique), 3)
        )
    }
    actual_rows = {
        frozenset(
            index
            for index, point in enumerate(internal)
            if incident(line, point)
        )
        for line in passants
    }
    assert len(reconstructed_rows) == 78
    assert reconstructed_rows == actual_rows

    def is_admissible(vertices: tuple[int, ...]) -> bool:
        return all(
            adjacency[first] >> second & 1
            for first, second in itertools.combinations(vertices, 2)
        ) and all(
            triple_concurrences[triple] == 0
            for triple in itertools.combinations(vertices, 3)
        )

    row_triples = {
        triple
        for row in actual_rows
        for triple in itertools.combinations(sorted(row), 3)
    }
    nonrow_admissible_triples = [
        triple
        for triple in itertools.combinations(range(78), 3)
        if triple not in row_triples and is_admissible(triple)
    ]
    assert len(row_triples) == 2730
    assert len(nonrow_admissible_triples) == 1456
    nonrow_admissible_triple_set = set(nonrow_admissible_triples)
    extension_pool_sizes = []
    for triple in sorted(row_triples) + nonrow_admissible_triples:
        extension_pool = [
            point
            for point in range(78)
            if point not in triple and is_admissible((*triple, point))
        ]
        if triple in nonrow_admissible_triple_set:
            extension_pool_sizes.append(len(extension_pool))
        for extra in itertools.combinations(extension_pool, 4):
            vertices = (*triple, *extra)
            if is_admissible(vertices):
                assert frozenset(vertices) in actual_rows
    assert max(extension_pool_sizes) == 10
    assert Counter(extension_pool_sizes) == Counter(
        {5: 208, 6: 201, 4: 199, 3: 196, 8: 143, 7: 132,
         2: 123, 9: 83, 10: 71, 1: 56, 0: 44}
    )

    def quadratic(point: tuple[int, int, int]) -> int:
        return (point[1] * point[1] - point[0] * point[2]) % q

    def rho(first: int, second: int) -> int:
        first_point = internal[first]
        second_point = internal[second]
        polar = (
            2 * first_point[1] * second_point[1]
            - first_point[0] * second_point[2]
            - first_point[2] * second_point[0]
        ) % q
        return (
            polar * polar
            * pow(quadratic(first_point) * quadratic(second_point), -1, q)
            % q
        )

    relation_matrices = {
        value: [
            sum(
                1 << second
                for second in range(78)
                if first != second and rho(first, second) == value
            )
            for first in range(78)
        ]
        for value in (0, 1, 3, 9, 10, 12)
    }
    rho_to_concurrence_color = {
        value: {
            pair_colors[tuple(sorted((first, second)))]
            for first in range(78)
            for second in range(first)
            if rho(first, second) == value
        }
        for value in (0, 1, 3, 9, 10, 12)
    }
    assert all(len(colors) == 1 for colors in rho_to_concurrence_color.values())
    assert len(
        {next(iter(colors)) for colors in rho_to_concurrence_color.values()}
    ) == 6

    relation_labels: tuple[int | None, ...] = (None, 0, 1, 3, 9, 10, 12)
    relation_representatives = {
        value: (
            (0, 0)
            if value is None
            else next(
                (first, second)
                for first in range(78)
                for second in range(78)
                if first != second and rho(first, second) == value
            )
        )
        for value in relation_labels
    }

    def has_relation(first: int, second: int, value: int) -> bool:
        return first != second and rho(first, second) == value

    def intersection_row(first_value: int, second_value: int) -> tuple[int, ...]:
        return tuple(
            sum(
                has_relation(first, middle, first_value)
                and has_relation(middle, second, second_value)
                for middle in range(78)
            )
            for first, second in (
                relation_representatives[value] for value in relation_labels
            )
        )

    assert intersection_row(0, 0) == (7, 0, 0, 0, 1, 1, 1)
    assert intersection_row(0, 9) == (0, 2, 2, 2, 0, 2, 0)
    assert intersection_row(0, 10) == (0, 2, 2, 0, 2, 0, 2)
    assert intersection_row(0, 12) == (0, 2, 0, 2, 0, 2, 2)
    assert intersection_row(9, 9) == (14, 0, 4, 2, 2, 1, 4)
    assert intersection_row(10, 10) == (14, 0, 2, 4, 2, 4, 1)
    assert intersection_row(12, 12) == (14, 4, 2, 2, 3, 2, 2)
    assert [
        next(
            value
            for value, matrix in relation_matrices.items()
            if gram_rows == matrix
        )
        for gram_rows in orbit_gram_rows
    ] == [9, 9, 12, 10]

    polar_row = {
        point_index: passants.index(
            canonical((-point[2] % q, 2 * point[1] % q, -point[0] % q))
        )
        for point_index, point in enumerate(internal)
    }
    assert all(
        relation_matrices[0][point_index]
        == sum(
            1 << column_index
            for column_index, column in enumerate(columns)
            if column >> polar_row[point_index] & 1
        )
        for point_index in range(78)
    )

    def multiply(first: list[int], second: list[int]) -> list[int]:
        return [
            sum(
                1 << column
                for column in range(78)
                if (first[row] & second[column]).bit_count() % 2
            )
            for row in range(78)
        ]

    identity = [1 << index for index in range(78)]
    assert multiply(relation_matrices[0], relation_matrices[0]) == [
        identity[index]
        ^ relation_matrices[9][index]
        ^ relation_matrices[10][index]
        ^ relation_matrices[12][index]
        for index in range(78)
    ]
    assert all(
        multiply(relation_matrices[0], relation_matrices[value]) == [0] * 78
        for value in (9, 10, 12)
    )
    assert multiply(relation_matrices[9], relation_matrices[9]) == relation_matrices[10]
    assert multiply(relation_matrices[10], relation_matrices[10]) == relation_matrices[12]
    assert multiply(relation_matrices[12], relation_matrices[12]) == relation_matrices[9]
    assert {
        value: binary_rank(relation_matrices[value])
        for value in (0, 9, 10, 12)
    } == {0: 42, 9: 36, 10: 36, 12: 36}

    def relation_color(first: int, second: int) -> object:
        if first == second:
            return -1
        return pair_colors[tuple(sorted((first, second)))]

    # A small geometric base replaces group enumeration in the upper bound for
    # the scheme automorphism group.  Its first three rho-relations are
    # (10,3,9); there are 78*14*2=2184 such ordered triples, PGL(2,13) acts
    # freely on them, the fourth base point is forced, and the four rho-values
    # resolve every internal point.
    source_base = [0, 8, 3, 6]
    assert [internal[index] for index in source_base] == [
        (1, 0, 2), (1, 1, 7), (1, 0, 7), (1, 1, 3)
    ]
    assert (
        rho(source_base[0], source_base[1]),
        rho(source_base[0], source_base[2]),
        rho(source_base[1], source_base[2]),
    ) == (10, 3, 9)
    assert all(
        sum(
            rho(first, third) == 3 and rho(second, third) == 9
            for third in range(78)
            if third not in (first, second)
        )
        == 2
        for first in range(78)
        for second in range(78)
        if first != second and rho(first, second) == 10
    )
    assert sum(
        all(
            act(matrix, internal[index]) == internal[index]
            for index in source_base[:3]
        )
        for matrix in matrices
    ) == 1
    assert sum(
        index not in source_base[:3]
        and tuple(rho(index, anchor) for anchor in source_base[:3]) == (3, 1, 9)
        for index in range(78)
    ) == 1
    rho_signatures = {
        tuple(
            -1 if vertex == anchor else rho(vertex, anchor)
            for anchor in source_base
        ): vertex
        for vertex in range(78)
    }
    assert len(rho_signatures) == 78

    source_signatures = {
        tuple(relation_color(vertex, base_vertex) for base_vertex in source_base):
        vertex
        for vertex in range(78)
    }
    assert len(source_signatures) == 78
    target_base: list[int] = []
    search_nodes: Counter[int] = Counter()
    automorphisms = 0

    def enumerate_automorphisms(depth: int) -> None:
        nonlocal automorphisms
        search_nodes[depth] += 1
        if depth == len(source_base):
            target_signatures = {
                tuple(
                    relation_color(vertex, base_vertex)
                    for base_vertex in target_base
                ): vertex
                for vertex in range(78)
            }
            if len(target_signatures) != 78:
                return
            permutation = [
                target_signatures[
                    tuple(
                        relation_color(vertex, base_vertex)
                        for base_vertex in source_base
                    )
                ]
                for vertex in range(78)
            ]
            assert all(
                relation_color(permutation[first], permutation[second])
                == relation_color(first, second)
                for first in range(78)
                for second in range(first)
            )
            automorphisms += 1
            return
        for image_vertex in range(78):
            if image_vertex in target_base:
                continue
            if all(
                relation_color(image_vertex, target_base[index])
                == relation_color(source_base[depth], source_base[index])
                for index in range(depth)
            ):
                target_base.append(image_vertex)
                enumerate_automorphisms(depth + 1)
                target_base.pop()

    enumerate_automorphisms(0)
    assert search_nodes == Counter({0: 1, 1: 78, 2: 1092, 3: 2184, 4: 2184})
    assert automorphisms == len(matrices) == 2184


def main() -> None:
    four_cliques = [
        clique
        for clique in itertools.combinations(VERTICES, 4)
        if all(
            adjacent(first, second)
            for first, second in itertools.combinations(clique, 2)
        )
    ]
    assert len(four_cliques) == 70
    assert Counter(
        tuple(sum(orbit == kind for orbit, _ in clique) for kind in range(3))
        for clique in four_cliques
    ) == Counter({(0, 2, 2): 14, (1, 1, 2): 28, (1, 2, 1): 28})

    five_cliques = set()
    for clique in four_cliques:
        common = [
            vertex
            for vertex in VERTICES
            if vertex not in clique
            and all(adjacent(vertex, member) for member in clique)
        ]
        assert len(common) == 1
        five_cliques.add(frozenset((*clique, common[0])))

    assert len(five_cliques) == 14
    assert all(
        not any(
            vertex not in clique
            and all(adjacent(vertex, member) for member in clique)
            for vertex in VERTICES
        )
        for clique in five_cliques
    )
    verify_distance()
    print(
        "q=13 tangent-code replay: PASS "
        "(omega = 5, d = 12, 364 minimum words, "
        "78 rows recovered, Aut = PGL(2,13))"
    )


if __name__ == "__main__":
    main()
