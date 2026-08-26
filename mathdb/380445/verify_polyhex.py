"""Exact-arithmetic checks for the proof of MathDB #380445.

This is evidence, not a substitute for the general proof.  It enumerates
translation classes of fixed polyhexes and checks the exact maximum and both
spanning-tree inequalities.
"""

from __future__ import annotations

from collections import deque
from fractions import Fraction


DIRECTIONS = ((1, 0), (0, 1), (-1, 1), (-1, 0), (0, -1), (1, -1))


def normalize(cells: frozenset[tuple[int, int]]) -> tuple[tuple[int, int], ...]:
    q0, r0 = min(cells)
    # Lexicographic minimum is not necessarily coordinatewise minimum; any
    # deterministic translation anchor suffices.
    return tuple(sorted((q - q0, r - r0) for q, r in cells))


def convex_hull(points: tuple[tuple[int, int], ...]) -> list[tuple[int, int]]:
    pts = sorted(set(points))
    if len(pts) <= 1:
        return pts

    def cross(o: tuple[int, int], a: tuple[int, int], b: tuple[int, int]) -> int:
        return (a[0] - o[0]) * (b[1] - o[1]) - (a[1] - o[1]) * (b[0] - o[0])

    lower: list[tuple[int, int]] = []
    for point in pts:
        while len(lower) >= 2 and cross(lower[-2], lower[-1], point) <= 0:
            lower.pop()
        lower.append(point)
    upper: list[tuple[int, int]] = []
    for point in reversed(pts):
        while len(upper) >= 2 and cross(upper[-2], upper[-1], point) <= 0:
            upper.pop()
        upper.append(point)
    return lower[:-1] + upper[:-1]


def doubled_area(poly: list[tuple[int, int]]) -> int:
    if len(poly) < 3:
        return 0
    return abs(
        sum(
            poly[i][0] * poly[(i + 1) % len(poly)][1]
            - poly[i][1] * poly[(i + 1) % len(poly)][0]
            for i in range(len(poly))
        )
    )


def three_width(cells: tuple[tuple[int, int], ...]) -> int:
    values = (
        [q + 2 * r for q, r in cells],
        [q - r for q, r in cells],
        [2 * q + r for q, r in cells],
    )
    return sum(max(row) - min(row) for row in values)


def edge_class(u: tuple[int, int], v: tuple[int, int]) -> int:
    dq, dr = v[0] - u[0], v[1] - u[1]
    if dr == 0:
        return 0
    if dq == 0:
        return 1
    return 2


def tree_counts(cells: tuple[tuple[int, int], ...]) -> tuple[int, int, int]:
    present = set(cells)
    root = min(present)
    seen = {root}
    queue = deque([root])
    counts = [0, 0, 0]
    while queue:
        u = queue.popleft()
        for dq, dr in DIRECTIONS:
            v = (u[0] + dq, u[1] + dr)
            if v in present and v not in seen:
                seen.add(v)
                queue.append(v)
                counts[edge_class(u, v)] += 1
    assert len(seen) == len(present)
    return tuple(counts)


def exact_maximum(n: int) -> Fraction:
    raw_floor = (3 * n * n + 14 * n + 3) // 3
    return Fraction(raw_floor - (1 if n % 3 == 0 else 0), 6)


def enumerate_and_check(limit: int = 9) -> None:
    animals = {((0, 0),)}
    total_checked = 0
    for n in range(1, limit + 1):
        observed = Fraction(-1)
        for cells in animals:
            hull = convex_hull(cells)
            area_p = Fraction(doubled_area(hull), 2)
            width = three_width(cells)
            area_cells = area_p + 1 + Fraction(width, 3)
            observed = max(observed, area_cells)

            a, b, c = tree_counts(cells)
            s = n - 1
            m = max(a, b, c) if s else 0
            assert area_p <= Fraction(a * b + a * c + b * c, 2)
            assert width <= 3 * s + m
            assert area_cells <= exact_maximum(n)
            total_checked += 1

        assert observed == exact_maximum(n), (n, observed, exact_maximum(n))
        print(f"n={n}: fixed translation classes={len(animals):,}, max={observed}")

        if n == limit:
            break
        next_animals: set[tuple[tuple[int, int], ...]] = set()
        for cells_tuple in animals:
            cells = frozenset(cells_tuple)
            for q, r in cells:
                for dq, dr in DIRECTIONS:
                    v = (q + dq, r + dr)
                    if v not in cells:
                        next_animals.add(normalize(cells | {v}))
        animals = next_animals

    print(f"all checks passed; {total_checked:,} polyhexes checked")


if __name__ == "__main__":
    enumerate_and_check()
