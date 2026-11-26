#!/bin/bash
# Usage: ./check.sh LongTable/File.lean   — elaborates the file, then prints axioms of every theorem in it.
set -e
cd /home/claude/leanT2b
export PATH=/home/claude/toolchain/lean-4.35.0-linux/bin:$PATH
F=$1; M=$(basename $F .lean)
echo "== building LongTable.$M"; lake build LongTable.$M 2>&1 | grep -E "error|warning|sorry|Built|✖" | head -60
cat > /tmp/ax_$M.lean <<EOT
import LongTable.$M
open Lean Elab Command
run_cmd liftTermElabM do
  let env ← getEnv
  let some idx := env.getModuleIdx? \`LongTable.$M | throwError "no module"
  let mut bad : Array String := #[]
  let mut n := 0
  for (nm, ci) in env.constants.map₁.toList do
    if env.getModuleIdxFor? nm != some idx then continue
    unless ci matches .thmInfo _ do continue
    n := n + 1
    let axs ← Lean.collectAxioms nm
    for a in axs do
      unless a == \`propext || a == \`Classical.choice || a == \`Quot.sound do bad := bad.push s!"{nm}: {a}"
  logInfo m!"theorems={n} nonstandard={bad}"
EOT
echo "== axioms"; lake env lean /tmp/ax_$M.lean 2>&1 | tail -3
