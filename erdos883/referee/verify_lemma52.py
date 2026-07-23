# Referee spot-check of erdos-883.tex Lemma 5.2 (distribution-function certificate):
#   for 1.089 <= delta <= 2:  D_n(1 - Theta(delta)) <= delta/3, margin > 0.0873,
# where Theta(delta) = (1/3)(1 - 2/(3(3-delta))) and D_n(theta) ~ (1/3q)#{v odd <= n : rho(v) < theta}.
# Independent-model main term: P(rho_S < theta) with p | v independently w.p. 1/p, p in S.
# Exact integer arithmetic over the common denominator P = prod S.
from fractions import Fraction

S = [5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71]
n18 = len(S)
N = 1 << n18
P = 1
for p in S:
    P *= p

# rho_int[mask] = P * rho_S(pattern), prob_num[mask] = P * P(pattern)
rho_int = [0] * N
rho_int[0] = P
prob_num = [0] * N
prob_num[0] = 1
for p in S:
    prob_num[0] *= (p - 1)
for mask in range(1, N):
    lb = mask & (-mask)
    i = lb.bit_length() - 1
    rho_int[mask] = rho_int[mask ^ lb] // S[i] * (S[i] - 1)
    prob_num[mask] = prob_num[mask ^ lb] // (S[i] - 1)
print("tables done", flush=True)

# sort masks by rho value; build cumulative probabilities (integers over P)
order = sorted(range(N), key=lambda m: rho_int[m])
rho_sorted = [rho_int[m] for m in order]
cum = [0] * (N + 1)
for j, m in enumerate(order):
    cum[j + 1] = cum[j] + prob_num[m]
assert cum[N] == P
import bisect

def P_rho_lt(theta_num, theta_den):
    # P(rho_S < theta) exactly: count mass of masks with rho_int/P < theta
    # rho_int * theta_den < theta_num * P
    lim = theta_num * P
    lo, hi = 0, N
    while lo < hi:
        mid = (lo + hi) // 2
        if rho_sorted[mid] * theta_den < lim:
            lo = mid + 1
        else:
            hi = mid
    return Fraction(cum[lo], P)

# D_infty(theta) vs delta/3 across the certificate range. The empirical D_n also
# carries q-normalization: #odd v <= n in the 3 classes / (3q) -> P(rho < theta)
# in the independent model (q ~ n/6, odds ~ n/2 => factor 1).  Margin check only.
print("delta   theta      P(rho_S<theta)  delta/3   margin", flush=True)
worst = None
for k in range(0, 1001):
    delta = Fraction(1089, 1000) + Fraction(911, 1000) * Fraction(k, 1000)
    theta = 1 - Fraction(1, 3) * (1 - Fraction(2, 1) / (3 * (3 - delta)))
    val = P_rho_lt(theta.numerator, theta.denominator)
    margin = Fraction(delta, 3) - val
    if worst is None or margin < worst[0]:
        worst = (margin, delta, theta, val)
    if k % 100 == 0:
        print(f"{float(delta):.4f}  {float(theta):.6f}  {float(val):.6f}  {float(delta/3):.6f}  {float(margin):.6f}", flush=True)
print("WORST margin over sweep:", float(worst[0]), "at delta =", float(worst[1]), flush=True)
print("paper claims margin > 0.0873 (after corrections):", worst[0] > Fraction(873, 10000), flush=True)
