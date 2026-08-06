#!/bin/sh
# Resume-safe full build of the sendov9-11 degrees-10/11 corpus (local verification).
#
# PARALLELISM. Lake 5.0.0 (Lean 4.31.0) has NO `--jobs`/`-j` option -- `lake build -j 2`
# fails with "unknown short option '-j'". LEAN_NUM_THREADS is the only knob, and it governs
# lake's job count as well as each worker's internal threading: LEAN_NUM_THREADS=4 was
# observed running exactly four concurrent lean processes.
#
# It is set to 2 here as a MEMORY cap, not a CPU one. A single SendovNRed11_* elaboration
# was measured holding 10.5 GB of private commit; four concurrent workers put this machine
# at 92% of its commit limit with 1.2 GB of physical RAM free -- the same condition that
# killed an earlier degree-11 batch with bad_alloc. Two workers halve the peak.
#
# Cost of the cap: ~5-7 wall hours instead of ~2.5-3.5 (measured effective parallelism was
# 5.05x at LEAN_NUM_THREADS=4 over the first 403 modules; 14.72 CPU-hours in 2.92 wall
# hours). Lowering the count also lowers each file's internal parallelism, which is the
# unavoidable side effect of there being only one knob.
#
# Solution1011 is built explicitly. It is a separate lean_lib and is NOT pulled in by
# Sendov1011, yet it is the module every comparator config names as `solution_module`.
# Its only import is SendovNStatement, so once the corpus is up it costs seconds -- but
# without it the local evidence stops one module short of what CI checks.
cd "$(dirname "$0")/sendov9-11" || exit 1
export LEAN_NUM_THREADS=2
lake build Sendov1011 Solution Challenge IntegrationCheck --no-ansi >> ../sendov1011-build.log 2>&1
rc=$?
echo "EXIT_CORPUS $rc" >> ../sendov1011-build.log
if [ "$rc" -eq 0 ]; then
  lake build Solution1011 --no-ansi >> ../sendov1011-build.log 2>&1
  rc=$?
  echo "EXIT_SOLUTION1011 $rc" >> ../sendov1011-build.log
fi
echo "EXIT $rc" >> ../sendov1011-build.log
