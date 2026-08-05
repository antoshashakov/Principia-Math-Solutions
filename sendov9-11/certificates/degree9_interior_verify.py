#!/usr/bin/env python3
"""Exact rational certificate for the interior part of Sendov, degree 9.

This verifies the finite arithmetic assertions used in the proof for 0 < a <= 9/10:

* m = 681/1000 is smaller than 2 sin(pi/9) (through the exact triple-angle test);
* on 0 < a <= 9/20 the reciprocal-square estimate forces Re(mu) > 1;
* on each of eighteen intervals of width 1/40 covering [9/20,9/10],
  an exact tensor-product Bernstein certificate proves P_i(a,y) > 0.

Only Python integers, fractions, and binomial coefficients are used.
No floating-point arithmetic or numerical quadrature occurs.
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


# Rational majorants for the elementary-symmetric-function bounds.
C = {
    2: F(4),
    3: F(264, 35),  # > 16 sqrt(2) / 3, since (99/70)^2 > 2
    4: F(24),
    5: F(56),
    6: F(28),
    7: F(8),
    8: F(1),
}
ELL = {2: 3, 3: 2, 4: 2, 5: 1, 6: 1, 7: 0, 8: 0}


def integrated_v_m_q_power(m, ell, S):
    """Return ∫_0^1 v^m q(a,y,v)^ell dv as a polynomial in (a,y).

    q(a,y,v) = 1 - ((8-S+S a^2)/4) v + a^2(1-y^2)v^2.
    A polynomial is represented by {(a_degree,y_degree): rational coefficient}.
    """
    q = {
        0: {(0, 0): F(1)},
        1: {(0, 0): -(F(8) - S) / 4, (2, 0): -S / 4},
        2: {(2, 0): F(1), (2, 2): F(-1)},
    }

    D = {0: {(0, 0): F(1)}}
    for _ in range(ell):
        ND = {}
        for rv, P in D.items():
            for qv, Q in q.items():
                key = rv + qv
                ND[key] = add(ND.get(key, {}), mul(P, Q))
        D = ND

    R = {}
    for rv, P in D.items():
        R = add(R, scale(P, F(1, m + rv + 1)))
    return R


def certificate_polynomial(S, lam):
    """Construct the exact polynomial P(a,y) used on one interval."""
    # (1-a)/9 + y^2/18
    P = {(0, 0): F(1, 9), (1, 0): F(-1, 9), (0, 2): F(1, 18)}

    # h(a,y) = (S/4-1)(1-a^2)-a^2 y^2.
    c = S / 4 - 1
    h = {(0, 0): c, (2, 0): -c, (2, 2): F(-1)}
    P = add(P, scale(power(h, 4), -F(1, 1) / (9 * lam)))

    # Error majorant.
    for m in range(2, 9):
        V = integrated_v_m_q_power(m, ELL[m], S)
        term = mul(V, monomial(m + 1, m, C[m]))
        P = add(P, scale(term, -1))
    return P


def affine_rectangle(P, a0, a1, Y):
    """Substitute a=a0+(a1-a0)u, y=Yv."""
    d = a1 - a0
    R = defaultdict(F)
    for (i, j), c in P.items():
        for k in range(i + 1):
            R[(k, j)] += c * comb(i, k) * a0 ** (i - k) * d ** k * Y ** j
    return {key: val for key, val in R.items() if val}


def bernstein_coefficients(P, nx, ny):
    """Convert a polynomial on [0,1]^2 to tensor Bernstein degree (nx,ny)."""
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


def univariate_bernstein_on_interval(coeffs, x0, x1, degree):
    """Exact Bernstein coefficients of Σ coeffs[k] x^k on [x0,x1]."""
    d = x1 - x0
    mono = defaultdict(F)
    for k, c in enumerate(coeffs):
        for j in range(k + 1):
            mono[j] += c * comb(k, j) * x0 ** (k - j) * d ** j
    B = []
    for i in range(degree + 1):
        value = F(0)
        for k, c in mono.items():
            if k <= i:
                value += c * F(comb(i, k), comb(degree, k))
        B.append(value)
    return B


m0 = F(681, 1000)


def sigma_extreme_bound(M):
    """Lemma-1 upper bound with N=8, m=m0, C=9 and upper endpoint M."""
    nu = next(j for j in range(9) if M ** j * m0 ** (8 - j) >= 9)
    value = (
        F(8 - nu, 1) / m0 ** 2
        + F(nu - 1, 1) / M ** 2
        + (M ** (nu - 1) * m0 ** (8 - nu) / 9) ** 2
    )
    return nu, value


# [a0,a1], S >= sigma, lambda <= L(a), Y >= sqrt(1-lambda^2).
INTERVALS = [
    (F(9, 20), F(19, 40), F(11043, 2000), F(49, 50), F(199, 1000)),
    (F(19, 40), F(1, 2), F(2783, 500), F(239, 250), F(587, 2000)),
    (F(1, 2), F(21, 40), F(2257, 400), F(1863, 2000), F(91, 250)),
    (F(21, 40), F(11, 20), F(1151, 200), F(1811, 2000), F(849, 2000)),
    (F(11, 20), F(23, 40), F(11819, 2000), F(879, 1000), F(477, 1000)),
    (F(23, 40), F(3, 5), F(764, 125), F(1699, 2000), F(66, 125)),
    (F(3, 5), F(5, 8), F(637, 100), F(817, 1000), F(577, 1000)),
    (F(5, 8), F(13, 20), F(13093, 2000), F(401, 500), F(239, 400)),
    (F(13, 20), F(27, 40), F(13113, 2000), F(81, 100), F(1173, 2000)),
    (F(27, 40), F(7, 10), F(3289, 500), F(409, 500), F(1151, 2000)),
    (F(7, 10), F(29, 40), F(529, 80), F(413, 500), F(141, 250)),
    (F(29, 40), F(3, 4), F(6661, 1000), F(1669, 2000), F(1103, 2000)),
    (F(3, 4), F(31, 40), F(1681, 250), F(843, 1000), F(269, 500)),
    (F(31, 40), F(4, 5), F(1701, 250), F(213, 250), F(131, 250)),
    (F(4, 5), F(33, 40), F(2761, 400), F(1723, 2000), F(127, 250)),
    (F(33, 40), F(17, 20), F(14041, 2000), F(109, 125), F(49, 100)),
    (F(17, 20), F(7, 8), F(7161, 1000), F(221, 250), F(187, 400)),
    (F(7, 8), F(9, 10), F(3663, 500), F(359, 400), F(883, 2000)),
]


def main():
    # Exact triple-angle check proving m0 < 2 sin(pi/9).
    Fm = 3 * m0 - m0 ** 3
    assert 0 < m0 < 1
    assert 0 < Fm
    assert Fm ** 2 < 3

    # Small range 0<a<=9/20.
    S0 = F(1101, 200)
    nu0, sig0 = sigma_extreme_bound(F(29, 20))
    assert nu0 == 7
    assert sig0 < S0
    # g(a)=S0 a^2-8a+8-S0 >0 on [0,9/20].
    gB = univariate_bernstein_on_interval([8 - S0, -8, S0], F(0), F(9, 20), 2)
    assert min(gB) > 0

    global_min = None
    global_where = None
    rows = []

    for index, (a0, a1, S, lam, Y) in enumerate(INTERVALS, 1):
        # Reciprocal-square upper bound.
        nu, sigma = sigma_extreme_bound(1 + a1)
        assert sigma <= S

        # L(a) >= lam is equivalent to
        # g(a)=S a^2 - 8 lam a + 8-S >= 0.
        LB = univariate_bernstein_on_interval([8 - S, -8 * lam, S], a0, a1, 2)
        assert min(LB) >= 0

        # Feasible y-range and the inequalities Q<=1 and h<=1.
        assert Y ** 2 >= 1 - lam ** 2
        assert 2 * lam >= a1
        c = S / 4 - 1
        assert c >= 0
        assert c * (1 - a0 ** 2) <= 1

        P = certificate_polynomial(S, lam)
        R = affine_rectangle(P, a0, a1, Y)
        nx = max(i for i, _ in R)
        ny = max(j for _, j in R)
        B = bernstein_coefficients(R, nx, ny)
        where, minimum = min(B.items(), key=lambda item: item[1])
        assert minimum > 0

        rows.append((index, a0, a1, nu, S, lam, Y, nx, ny, where, minimum))
        if global_min is None or minimum < global_min:
            global_min = minimum
            global_where = (index, where)

    print("m0 triple-angle test: CERTIFIED")
    print("small range 0<a<=9/20: CERTIFIED")
    print("interior Bernstein certificates:")
    for index, a0, a1, nu, S, lam, Y, nx, ny, where, minimum in rows:
        print(
            f"  {index:2d}. [{a0},{a1}] nu={nu} S={S} lambda={lam} "
            f"Y={Y} degree=({nx},{ny}) min@{where}={minimum}"
        )
    assert global_min > F(1, 2100)
    print(f"global minimum: interval/index {global_where} = {global_min}")
    print("global minimum > 1/2100")
    print("CERTIFIED: P_i(a,y)>0 on all 18 rectangles covering [9/20,9/10].")


if __name__ == "__main__":
    main()
