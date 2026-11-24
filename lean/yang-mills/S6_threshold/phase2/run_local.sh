#!/bin/bash
# Local reruns of phase 2 (not a site post). Needs `lean` (4.35.0) and python3 on PATH. From this folder:
#   bash run_local.sh > transcript_local.txt 2>&1
# Builds scratch files in a temporary directory; changes nothing here.
set -u
T=$(mktemp -d)
S6=../../../../python/yang-mills/S6_threshold
now() { date +%s.%N; }
el() { echo "$2 - $1" | bc; }
echo "== machine"; date -u; lean --version; nproc; grep -m1 'model name' /proc/cpuinfo
echo "== hashes"; sha256sum $S6/G_affine_cert.py $S6/G_affine_reference.txt GAffineEval.lean GAffineEvalRef.lean \
  $S6/G_affine_reference_sc.py full_table_check.py make_lean.py ../pilot/GBoxPilot.lean
echo "== self-contained reference program, run alone, against G_affine_reference.txt"
mkdir $T/alone && cp $S6/G_affine_reference_sc.py $T/alone/ && (cd $T/alone && python3 -I G_affine_reference_sc.py > ref.out)
cmp $T/alone/ref.out $S6/G_affine_reference.txt && echo "identical, $(wc -l < $T/alone/ref.out) lines"
echo "== closed form of the full table"; python3 -I full_table_check.py
echo "== GAffineEvalRef.lean is the evaluator plus the 20 theorems, rebuilt from the sources"
cp GAffineEvalRef.lean $T/ref_before.lean && python3 make_lean.py ref && cmp $T/ref_before.lean GAffineEvalRef.lean && echo "rebuilt: unchanged"
cmp <(head -c $(wc -c < GAffineEval.lean) GAffineEvalRef.lean) GAffineEval.lean && echo "prefix identical to GAffineEval.lean"
echo "== #eval against the Python program on all 128 boxes (g; lo, hi of q and c; check): count, mismatches"
python3 make_lean.py evalcheck $T/evalcheck.lean && lean $T/evalcheck.lean
echo "== kernel: elaboration of the evaluator alone (start-up baseline), 3 runs"
for i in 1 2 3; do s=$(now); lean GAffineEval.lean; echo "GAffineEval.lean $(el $s $(now)) s"; done
echo "== kernel: one box (reference box), profiler, 3 runs; the pilot (one box) beside it"
python3 make_lean.py one $T/one.lean
{ head -n -3 $T/one.lean; echo 'set_option profiler true'; tail -n 3 $T/one.lean; } > $T/one_prof.lean
{ head -n -1 ../pilot/GBoxPilot.lean | grep -v '^set_option maxRecDepth'; echo 'set_option profiler true';
  echo 'set_option maxRecDepth 1000000 in'; tail -n 1 ../pilot/GBoxPilot.lean; } > $T/pilot_prof.lean
for i in 1 2 3; do
  echo "Eval:  $(lean $T/one_prof.lean 2>&1 | grep -m1 'type checking took')"
  echo "pilot: $(lean $T/pilot_prof.lean 2>&1 | grep -m1 'type checking took')"
done
echo "== whole files, wall clock: one box, the pilot"
for i in 1 2 3; do s=$(now); lean $T/one.lean; echo "one box $(el $s $(now)) s"; s=$(now); lean ../pilot/GBoxPilot.lean; echo "pilot $(el $s $(now)) s"; done
echo "== the 20 reference theorems (GAffineEvalRef.lean), wall clock"
s=$(now); lean GAffineEvalRef.lean && echo "all 20 pass: $(el $s $(now)) s"
echo "== all 128 boxes, check b = true by decide +kernel, one file, wall clock"
python3 make_lean.py all $T/all.lean; s=$(now); lean $T/all.lean && echo "all 128 pass: $(el $s $(now)) s"
echo "== mutation: the kernel refuses a wrong e (ref01, e - 1) and accepts check = false on the whole range as one box"
python3 make_lean.py one $T/m.lean; head -n -3 $T/m.lean > $T/mut.lean
cat >> $T/mut.lean <<'EOF'
theorem whole_range_box_fails : GAff.check ⟨0, 1, 4, 5, 0, 1, 4, 5, 0, 1, 1, 5⟩ = false := by decide +kernel
theorem ref01_wrong : GAff.form ⟨0, 1, 1, 10, 0, 1, 1, 10, 0, 1, 1, 10⟩ =
    (-1266790716429935892, 3557134024578336, 748344278582536, 1526502251810112, 82338656494932945) := by decide +kernel
EOF
lean $T/mut.lean 2>&1 | grep -E '^[^ ].*error' | sed "s|$T/||" | head -3
rm -rf $T
echo "== done"; date -u
