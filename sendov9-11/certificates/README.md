# Exact certificates for degrees 9, 10, and 11

The primary verifiers use only Python's standard-library `fractions.Fraction`
and integer binomial coefficients.  The independent reconstructions use
SymPy and build the certificate polynomials separately.

Run from this directory:

```bash
python degree9_interior_verify.py
python degree9_interior_independent_check.py
python degree9_boundary_verify.py
python degree9_boundary_independent_check.py
python degree10_verify.py
python degree10_independent_check.py
python degree11_verify.py
python degree11_independent_check.py
```

The degree-11 programs are the slowest.  `degree11_verification_log.txt`
records a completed exact run of both implementations over all 530 interior
boxes and the boundary box.

Certified lower bounds for the least tensor-Bernstein coefficient are:

| degree | interior | boundary |
|---:|---:|---:|
| 9 | `> 1/2100` | `> 1/100` |
| 10 | `> 1/3100` | `> 7/100` |
| 11 | `> 1/2800` | `> 3/50` |

No verifier uses floating-point arithmetic or numerical quadrature to certify
positivity.  Floating-point conversions, where printed, are display-only.
