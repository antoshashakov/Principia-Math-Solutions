#!/usr/bin/env python3
"""Exact rational certificate for Sendov's conjecture in degree 10.

This verifies the finite arithmetic in the following general reciprocal-integral
argument.  A hypothetical bad degree-10 polynomial gives nine reciprocal
critical-point variables Y_j with |Y_j|<1.  Centering at their mean reduces the
proof to positivity of explicit bivariate polynomials.

The script checks, using only integers, fractions, and binomial coefficients:
  * 309/500 < 2 sin(pi/10);
  * exact rational majorants for the centered elementary symmetric functions;
  * product/localization contradictions on 0 <= a <= 2/5;
  * 50 tensor-Bernstein certificates on intervals of width 1/100 covering
    2/5 <= a <= 9/10;
  * one rescaled tensor-Bernstein certificate covering 9/10 <= a <= 1.

No floating-point arithmetic or numerical quadrature is used.
"""

from collections import defaultdict
from fractions import Fraction as F
from math import comb


def add(P, Q):
    R = defaultdict(F)
    for key, val in P.items():
        R[key] += val
    for key, val in Q.items():
        R[key] += val
    return {key: val for key, val in R.items() if val}


def scale(P, c):
    c = F(c)
    return {key: val * c for key, val in P.items() if val * c}


def mul(P, Q):
    R = defaultdict(F)
    for (i, j), c in P.items():
        for (k, ell), d in Q.items():
            R[(i + k, j + ell)] += c * d
    return {key: val for key, val in R.items() if val}


def power(P, n):
    R = {(0, 0): F(1)}
    B = P
    while n:
        if n & 1:
            R = mul(R, B)
        B = mul(B, B)
        n //= 2
    return R


def monomial(i, j, c=1):
    return {(i, j): F(c)}


def affine_rectangle(P, x0, x1, y0, y1):
    """Substitute x=x0+(x1-x0)u and y=y0+(y1-y0)v."""
    x0, x1, y0, y1 = map(F, (x0, x1, y0, y1))
    dx, dy = x1 - x0, y1 - y0
    R = defaultdict(F)
    for (i, j), c in P.items():
        for k in range(i + 1):
            cx = F(comb(i, k)) * x0 ** (i - k) * dx ** k
            for ell in range(j + 1):
                cy = F(comb(j, ell)) * y0 ** (j - ell) * dy ** ell
                R[(k, ell)] += c * cx * cy
    return {key: val for key, val in R.items() if val}


def bernstein_coefficients(P, nx=None, ny=None):
    """Tensor Bernstein coefficients on [0,1]^2."""
    if nx is None:
        nx = max((i for i, _ in P), default=0)
    if ny is None:
        ny = max((j for _, j in P), default=0)
    B = {}
    for i in range(nx + 1):
        for j in range(ny + 1):
            total = F(0)
            for (k, ell), c in P.items():
                if k <= i and ell <= j:
                    total += (
                        c
                        * F(comb(i, k), comb(nx, k))
                        * F(comb(j, ell), comb(ny, ell))
                    )
            B[(i, j)] = total
    return B


def univariate_bernstein(coeffs, x0, x1, degree=None):
    """Bernstein coefficients on [x0,x1] of sum coeffs[k] x^k."""
    coeffs = list(map(F, coeffs))
    x0, x1 = F(x0), F(x1)
    if degree is None:
        degree = len(coeffs) - 1
    d = x1 - x0
    mono = defaultdict(F)
    for k, c in enumerate(coeffs):
        for j in range(k + 1):
            mono[j] += c * comb(k, j) * x0 ** (k - j) * d ** j
    B = []
    for i in range(degree + 1):
        total = F(0)
        for k, c in mono.items():
            if k <= i:
                total += c * F(comb(i, k), comb(degree, k))
        B.append(total)
    return B


def sigma_bound(M):
    """Convex extremal bound for sum r_k^{-2}; N=9, C=10."""
    M = F(M)
    N, C = 9, 10
    assert M ** N >= C
    nu = next(j for j in range(N + 1) if M ** j * M0 ** (N - j) >= C)
    value = (
        F(N - nu) / M0 ** 2
        + F(nu - 1) / M ** 2
        + (M ** (nu - 1) * M0 ** (N - nu) / C) ** 2
    )
    return nu, value


def integrated_v_m_q_power(m, ell, S):
    """Return integral_0^1 v^m q(a,y,v)^ell dv as a polynomial in (a,y).

    q=1-[2(9-S+S a^2)/9]v+a^2(1-y^2)v^2.
    """
    q = {
        0: {(0, 0): F(1)},
        1: {(0, 0): -F(2) * (9 - S) / 9, (2, 0): -F(2) * S / 9},
        2: {(2, 0): F(1), (2, 2): F(-1)},
    }
    D = {0: {(0, 0): F(1)}}
    for _ in range(ell):
        ND = {}
        for rv, P in D.items():
            for qv, Q in q.items():
                ND[rv + qv] = add(ND.get(rv + qv, {}), mul(P, Q))
        D = ND
    R = {}
    for rv, P in D.items():
        R = add(R, scale(P, F(1, m + rv + 1)))
    return R


def certificate_polynomial(S, lam):
    """Construct P(a,y) such that |I|-a/10 >= P on feasible pairs."""
    P = {(0, 0): F(1, 10), (1, 0): F(-1, 10), (0, 2): F(1, 20)}

    # h=(2S/9-1)(1-a^2)-a^2 y^2 bounds |1-a mu|^2.
    c = F(2) * S / 9 - 1
    h = {(0, 0): c, (2, 0): -c, (2, 2): F(-1)}
    P = add(P, scale(power(h, 5), -F(1, 10) / lam))

    for m in range(2, 10):
        ell = (9 - m) // 2
        V = integrated_v_m_q_power(m, ell, S)
        term = mul(V, monomial(m + 1, m, C_MAJ[m]))
        P = add(P, scale(term, -1))
    return P


def largest_grid_lambda(S, a0, a1, denominator=100000):
    """Largest k/denominator certified below L_S on [a0,a1]."""
    lo, hi = 0, denominator
    while lo < hi:
        mid = (lo + hi + 1) // 2
        lam = F(mid, denominator)
        # L_S(a)>=lam iff S a^2-9 lam a+9-S>=0.
        B = univariate_bernstein([9 - S, -9 * lam, S], a0, a1, 2)
        if min(B) >= 0:
            lo = mid
        else:
            hi = mid - 1
    return F(lo, denominator)


def smallest_grid_sqrt_upper(q, denominator=100000):
    """Smallest k/denominator with (k/denominator)^2 >= q."""
    lo, hi = 0, denominator
    while lo < hi:
        mid = (lo + hi) // 2
        if F(mid, denominator) ** 2 >= q:
            hi = mid
        else:
            lo = mid + 1
    return F(lo, denominator)


def boundary_substitute_div_delta(P):
    """Substitute a=1-x^2, y=xY and divide exactly by x^2."""
    R = defaultdict(F)
    for (i, j), c in P.items():
        for k in range(i + 1):
            R[(2 * k + j - 2, j)] += c * comb(i, k) * (-1) ** k
    negative = {key: val for key, val in R.items() if key[0] < 0 and val}
    assert not negative
    return {key: val for key, val in R.items() if val}


M0 = F(309, 500)
C_MAJ = {
    2: F(9, 2),
    3: F(9),
    4: F(2201, 100),
    5: F(2201, 100),
    6: F(877, 50),
    7: F(217, 20),
    8: F(481, 100),
    9: F(1),
}


def main():
    # 2 sin(pi/10)=(sqrt(5)-1)/2, so this is an exact lower check.
    assert (2 * M0 + 1) ** 2 < 5

    # Exact majorants for the Cauchy centered-ESP bounds in degrees 4,...,8.
    assert C_MAJ[4] ** 2 >= F(9 ** 9, 4 ** 4 * 5 ** 5)
    assert C_MAJ[5] ** 2 >= F(9 ** 9, 5 ** 5 * 4 ** 4)
    assert C_MAJ[6] ** 2 >= F(9 ** 9, 6 ** 6 * 3 ** 3)
    assert C_MAJ[7] ** 2 >= F(9 ** 9, 7 ** 7 * 2 ** 2)
    assert C_MAJ[8] ** 2 >= F(9 ** 9, 8 ** 8)

    # Product contradiction for 0<=a<=29/100.
    assert F(129, 100) ** 9 < 10

    # Localization contradiction on [29/100,2/5].
    nu_small, S_small = sigma_bound(F(7, 5))
    B_small = univariate_bernstein(
        [9 - S_small, -9, S_small], F(29, 100), F(2, 5), 2
    )
    assert min(B_small) > 0

    global_min = None
    global_where = None

    # Fifty exact interior certificates, [0.40,0.90].
    rows = []
    for i in range(40, 90):
        a0, a1 = F(i, 100), F(i + 1, 100)
        nu, S = sigma_bound(1 + a1)
        lam = largest_grid_lambda(S, a0, a1)
        Y = smallest_grid_sqrt_upper(1 - lam ** 2)

        assert min(univariate_bernstein([9 - S, -9 * lam, S], a0, a1, 2)) >= 0
        assert Y ** 2 >= 1 - lam ** 2
        assert 2 * lam >= a1
        hcoef = F(2) * S / 9 - 1
        assert hcoef >= 0
        assert hcoef * (1 - a0 ** 2) <= 1

        P = certificate_polynomial(S, lam)
        R = affine_rectangle(P, a0, a1, F(0), Y)
        B = bernstein_coefficients(R)
        where, minimum = min(B.items(), key=lambda item: item[1])
        assert minimum > 0
        rows.append((a0, a1, nu, lam, Y, where, minimum))
        if global_min is None or minimum < global_min:
            global_min = minimum
            global_where = (a0, a1, where)

    # Rescaled boundary certificate, [0.90,1].
    nu_boundary, S_boundary = sigma_bound(F(2))
    lam_boundary = F(22, 25)
    a0 = F(9, 10)
    assert min(
        univariate_bernstein(
            [9 - S_boundary, -9 * lam_boundary, S_boundary], a0, F(1), 2
        )
    ) > 0

    # If delta=1-a=x^2, then y_original=xY and Y^2 <= 2C_delta.
    C_delta = (S_boundary * (1 + a0) - 9) / (9 * a0)
    X, Y = F(8, 25), F(31, 20)
    assert X ** 2 >= F(1, 10)
    assert Y ** 2 >= 2 * C_delta
    hcoef = F(2) * S_boundary / 9 - 1
    assert hcoef >= 0
    assert hcoef * (1 - a0 ** 2) <= 1
    assert 2 * lam_boundary >= 1

    P = certificate_polynomial(S_boundary, lam_boundary)
    Q = boundary_substitute_div_delta(P)
    R = affine_rectangle(Q, F(0), X, F(0), Y)
    B = bernstein_coefficients(R)
    where_boundary, min_boundary = min(B.items(), key=lambda item: item[1])
    assert min_boundary > 0

    print("m0 and centered-ESP majorants: CERTIFIED")
    print("0 <= a <= 2/5: CERTIFIED")
    print(f"50 interior rectangles: CERTIFIED; least Bernstein coefficient={global_min}")
    print(f"least interior coefficient occurs at {global_where}")
    print(
        "boundary rectangle: CERTIFIED; "
        f"least Bernstein coefficient={min_boundary} at {where_boundary}"
    )
    print("CERTIFIED: all finite inequalities required by the degree-10 proof pass.")


if __name__ == "__main__":
    main()
