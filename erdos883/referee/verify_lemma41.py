# Independent referee check of erdos-883.tex Lemma 4.1 (upper-tail mean estimate).
# All arithmetic exact (integers over fixed common denominators).
from fractions import Fraction
import sys

S = [5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71]
n18 = len(S)
N = 1 << n18
P = 1
for p in S:
    P *= p
M0 = 100 * P  # common denominator for G values: 0.87 = 87/100, rho_S has denom | P

# g_int[mask] = G[mask] * M0, an exact integer.
# rho[mask] * P is an integer: rho_int[mask] = P * prod_{p in mask} (1-1/p)
rho_int = [0] * N
rho_int[0] = P
for mask in range(1, N):
    lb = mask & (-mask)
    i = lb.bit_length() - 1
    rho_int[mask] = rho_int[mask ^ lb] // S[i] * (S[i] - 1)
g = [0] * N
for mask in range(N):
    d = 87 * P - 100 * rho_int[mask]  # (0.87 - rho)*M0
    g[mask] = d if d > 0 else 0
del rho_int
print("G table done", flush=True)

# Moebius (finite-difference) transform: c[mask] = sum_{E subset D} (-1)^{|D|-|E|} G[E]
c = g  # in place
for i in range(n18):
    bit = 1 << i
    for mask in range(N):
        if mask & bit:
            c[mask] -= c[mask ^ bit]
print("coefficients done", flush=True)

# m_D for each mask, and P // m_D
Pdiv = [P] * N  # P / m_D  (integer since m_D | P)
mval = [1] * N
for mask in range(1, N):
    lb = mask & (-mask)
    i = lb.bit_length() - 1
    mval[mask] = mval[mask ^ lb] * S[i]
    Pdiv[mask] = Pdiv[mask ^ lb] // S[i]

# E_S = (1/(M0*P)) * sum c[mask] * (P/m)          [exact]
# C'_S = (1/(M0*P)) * sum_{mask!=0} |c[mask]| * (m+1) * (P/m)
ES_num = 0
Cp_num = 0
for mask in range(N):
    ES_num += c[mask] * Pdiv[mask]
    if mask:
        a = abs(c[mask])
        if a:
            Cp_num += a * (mval[mask] + 1) * Pdiv[mask]
E_S = Fraction(ES_num, M0 * P)
CpS = Fraction(Cp_num, M0 * P)
print("E_S  =", float(E_S), flush=True)
print("C'_S =", float(CpS), flush=True)

# tail: sum_{p > 71} 1/p^2 <= exact sum over primes in (71, 10^7]
#        + remainder over odd n > 10^7:  sum_{odd n > B} 1/n^2 < 1/(2(B-1)).
# The partial sum is bounded above by ceiling-accumulation at scale 10^40:
#   sum 1/p^2  <=  (sum ceil(SCALE/p^2)) / SCALE   — rigorous and fast.
B = 10**7
SCALE = 10**40
sieve = bytearray([1]) * (B + 1)
sieve[0:2] = b"\x00\x00"
for i in range(2, int(B**0.5) + 1):
    if sieve[i]:
        sieve[i * i :: i] = bytes(len(sieve[i * i :: i]))
acc = 0
for p in range(73, B + 1):
    if sieve[p]:
        acc += -(-SCALE // (p * p))  # ceil division
tail = Fraction(acc, SCALE) + Fraction(1, 2 * (B - 1))
print("tail(<=1e7) upper =", float(Fraction(acc, SCALE)), flush=True)
print("tail <=", float(tail), flush=True)

N_odd = 37_182_144
lhs = E_S + tail + CpS / N_odd
target = Fraction(4351, 150000)
print("hinge lhs =", float(lhs), " target 4351/150000 =", float(target),
      " OK:", lhs < target, flush=True)
beta_bound = Fraction(13, 100) + 3 * lhs
print("beta* bound =", float(beta_bound), " < 0.217020:",
      beta_bound < Fraction(21702, 100000), flush=True)
print("paper's C'_S < 8669 claim:", CpS < 8669, flush=True)
print("exact hinge margin (target - lhs) =", target - lhs,
      "=", float(target - lhs), flush=True)
