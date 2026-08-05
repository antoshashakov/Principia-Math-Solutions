#!/usr/bin/env python3
"""Exact rational verifier for the degree-9 endgame polynomial inequality.

No floating point arithmetic and no third-party packages are used.
"""
from fractions import Fraction as F
from math import comb
from typing import Dict, Tuple

Tri = Dict[Tuple[int, int, int], F]   # x^i y^j t^k
Bi = Dict[Tuple[int, int], F]         # x^i y^j


def tri_add(p: Tri, q: Tri) -> Tri:
    r = dict(p)
    for mon, c in q.items():
        r[mon] = r.get(mon, F(0)) + c
        if r[mon] == 0:
            del r[mon]
    return r


def tri_mul(p: Tri, q: Tri) -> Tri:
    r: Tri = {}
    for (i, j, k), a in p.items():
        for (i2, j2, k2), b in q.items():
            mon = (i + i2, j + j2, k + k2)
            r[mon] = r.get(mon, F(0)) + a * b
    return {m: c for m, c in r.items() if c}


def tri_pow(p: Tri, n: int) -> Tri:
    r: Tri = {(0, 0, 0): F(1)}
    b = p
    while n:
        if n & 1:
            r = tri_mul(r, b)
        b = tri_mul(b, b)
        n //= 2
    return r


def bi_add_term(p: Bi, i: int, j: int, c: F) -> None:
    if not c:
        return
    p[(i, j)] = p.get((i, j), F(0)) + c
    if p[(i, j)] == 0:
        del p[(i, j)]


# Q=(1-t)^2+x^2 t(19/10-y^2 t).
Q: Tri = {
    (0, 0, 0): F(1),
    (0, 0, 1): F(-2),
    (0, 0, 2): F(1),
    (2, 0, 1): F(19, 10),
    (2, 2, 2): F(-1),
}

# The coefficient for m=3 uses sqrt(2) < 99/70, hence
# 16 sqrt(2)/3 < 264/35.  All other coefficients are exact.
C = {2: F(4), 3: F(264, 35), 4: F(24),
     5: F(56), 6: F(28), 7: F(8), 8: F(1)}
r = {2: 3, 3: 2, 4: 2, 5: 1, 6: 1, 7: 0, 8: 0}

# Build Ebar(x,y) exactly.  For each t^n monomial, integrate to
# 1-x^2 using (1-x^2)^(n+1)/(n+1), expanded binomially.
Ebar: Bi = {}
for m in range(2, 9):
    integrand = tri_pow(Q, r[m])
    # multiply by t^m
    integrand = {(i, j, k + m): c for (i, j, k), c in integrand.items()}
    for (i, j, n), c in integrand.items():
        c *= C[m] / F(n + 1)
        i += m - 2
        j += m
        for h in range(n + 2):
            bi_add_term(Ebar, i + 2 * h, j,
                        c * ((-1) ** h) * comb(n + 1, h))

# P=1/9+y^2/18-1/1000-Ebar.
P: Bi = {(0, 0): F(1, 9) - F(1, 1000), (0, 2): F(1, 18)}
for (i, j), c in Ebar.items():
    bi_add_term(P, i, j, -c)

NX = max(i for i, _ in P)
NY = max(j for _, j in P)
assert (NX, NY) == (24, 8)

# Scale the rectangle x in [0,8/25], y in [0,7/5] to [0,1]^2.
X = F(8, 25)
Y = F(7, 5)
A: Bi = {(i, j): c * X**i * Y**j for (i, j), c in P.items()}

# Power-to-Bernstein conversion:
# u^i v^j = sum_{k>=i,l>=j} C(k,i)/C(NX,i) *
#             C(l,j)/C(NY,j) B_{k,NX}(u)B_{l,NY}(v).
bernstein: Bi = {}
for k in range(NX + 1):
    for ell in range(NY + 1):
        b = F(0)
        for i in range(k + 1):
            for j in range(ell + 1):
                c = A.get((i, j), F(0))
                if c:
                    b += (c * F(comb(k, i), comb(NX, i))
                          * F(comb(ell, j), comb(NY, j)))
        bernstein[(k, ell)] = b

key = min(bernstein, key=bernstein.get)
bmin = bernstein[key]
claimed = F(1, 100)
assert key == (24, 8)
assert bmin == F(
    139392070260030830922829855080988292511,
    11102230246251565404236316680908203125000,
)
assert bmin > claimed
assert all(b >= claimed for b in bernstein.values())

print(f"degree = ({NX},{NY})")
print(f"number of Bernstein coefficients = {len(bernstein)}")
print(f"minimum index = {key}")
print(f"minimum coefficient = {bmin}")
print(f"minimum coefficient - 1/100 = {bmin - claimed}")
print("CERTIFIED: P(x,y) >= 1/100 on [0,8/25] x [0,7/5].")
