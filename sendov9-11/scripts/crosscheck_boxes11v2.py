#!/usr/bin/env python3
"""Independent exact-rational cross-check of the emitted boxes11v2/ files.

Trusts NOTHING from the emitter's polynomial construction: it parses each
emitted Lean file's integer data (Adata, Qdata, Dscale, Lscale, cnum) and
re-verifies, with Python integers/fractions only, exactly what the kernel will
check plus the margin bookkeeping:

  1. hQ:    C(nx,k) * C(ny,l) * Q[k][l] == L  for all k,l;
  2. hpos:  cnum > 0  (and D > 0, L > 0);
  3. hint:  every intTable entry
              sum_{k<=i, l<=j} A[k][l] * C(i,k) * C(j,l) * Q[k][l]
            is >= cnum, and the minimum equals cnum exactly;
  4. margin: cnum / (D*L) == the c4-experiment's exact best margin
            (`margin_cau_exact` in boxes11v2-tau.csv for interior boxes; the
            recorded boundary margin for the boundary box).

Usage:  python crosscheck_boxes11v2.py [file.lean ...]   (default: all of boxes11v2/)
"""
import csv, glob, os, re, sys
from fractions import Fraction as F
from math import comb

HERE = os.path.dirname(os.path.abspath(__file__))
BOXDIR = os.path.join(HERE, 'boxes11v2')
TAU_CSV = os.path.join(HERE, 'boxes11v2-tau.csv')

BOUNDARY_MARGIN_REF = F(
    58783677556526534894130458023382054597437967641316736415627899292265103487584055329979704400730870346517117975645536873614611721987,
    912101053412329291206924773004784115369169494407806670805684437303796151062630230259438944562244699909570044837892055511474609375000)

def parse_lean_box(path):
    text = open(path, encoding='utf-8').read()
    def get_table(name):
        m = re.search(r'def ' + name + r' : List \(List ℤ\) :=\s*(\[.*?\]\])', text, re.S)
        return eval(m.group(1))
    def get_int(name):
        m = re.search(r'def ' + name + r' : ℤ := (-?\d+)', text)
        return int(m.group(1))
    return dict(A=get_table('Adata'), Q=get_table('Qdata'),
                D=get_int('Dscale'), L=get_int('Lscale'), c=get_int('cnum'))

def check_file(path, margins):
    name = os.path.basename(path)
    d = parse_lean_box(path)
    A, Q, D, L, cnum = d['A'], d['Q'], d['D'], d['L'], d['c']
    nx, ny = len(A) - 1, len(A[0]) - 1
    assert all(len(r) == ny + 1 for r in A) and len(Q) == nx + 1 \
        and all(len(r) == ny + 1 for r in Q), (name, 'table shape')
    # 1. hQ
    for k in range(nx + 1):
        for l in range(ny + 1):
            assert comb(nx, k) * comb(ny, l) * Q[k][l] == L, (name, 'hQ', k, l)
    # 2. positivity of the scaling data
    assert cnum > 0 and D > 0 and L > 0, (name, 'hpos')
    # 3. hint: all Bernstein numerators >= cnum, min == cnum
    mn = None
    for i in range(nx + 1):
        for j in range(ny + 1):
            s = 0
            for k in range(i + 1):
                for l in range(j + 1):
                    a = A[k][l]
                    if a:
                        s += a * comb(i, k) * comb(j, l) * Q[k][l]
            assert s >= cnum, (name, 'hint FAILS', i, j, s, cnum)
            if mn is None or s < mn:
                mn = s
    assert mn == cnum, (name, 'cnum not tight', mn, cnum)
    # 4. margin agreement with the c4 experiment
    margin = F(cnum, D * L)
    m = re.match(r'Sendov911Box11_(\d+)_(\d+)\.lean', name)
    if m:
        ref = margins[(int(m.group(1)), int(m.group(2)))]
    else:
        assert name == 'Sendov911Box11Boundary.lean', name
        ref = BOUNDARY_MARGIN_REF
    assert margin == ref, (name, 'margin mismatch', margin, ref)
    return nx, ny, margin

def main():
    files = sys.argv[1:] or sorted(glob.glob(os.path.join(BOXDIR, '*.lean')))
    margins = {}
    with open(TAU_CSV, newline='') as f:
        for row in csv.DictReader(f):
            margins[(int(row['i']), int(row['j']))] = F(row['margin_cau_exact'])
    worst = None; worst_name = None
    for idx, path in enumerate(files):
        nx, ny, margin = check_file(path, margins)
        if worst is None or margin < worst:
            worst = margin; worst_name = os.path.basename(path)
        if (idx + 1) % 50 == 0 or idx + 1 == len(files):
            print(f'{idx+1}/{len(files)} checked', flush=True)
    print(f'ALL {len(files)} FILES PASS: hQ, cnum>0, every Bernstein numerator >= cnum '
          f'(min tight), margins match the c4 experiment exactly.')
    print(f'worst margin {float(worst):.6e} in {worst_name}')

if __name__ == '__main__':
    main()
