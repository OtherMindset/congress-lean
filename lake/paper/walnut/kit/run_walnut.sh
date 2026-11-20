#!/bin/sh
# Head-to-head: Walnut on the VN-library tables. Needs git, Java 17+ (java -version), ~6 GB free memory.
# Usage:  sh run_walnut.sh        (from inside this folder; takes about 5 min to build, then the runs)
set -u
KIT=$(cd "$(dirname "$0")" && pwd); cd "$KIT"
java -version 2>&1 | head -1
[ -d Walnut ] || git clone -q https://github.com/Walnut-Theorem-Prover/Walnut.git
cd Walnut
git checkout -q 3bf0ece983279f34cbf657481fa472c1f1ab3932 2>/dev/null || echo "note: pinned commit not found, using $(git rev-parse HEAD)"
echo "Walnut commit: $(git rev-parse HEAD)" | tee "$KIT/walnut_run.log"
[ -f target/Walnut-all.jar ] || bash build.sh >> "$KIT/walnut_build.log" 2>&1 || { echo "build failed; see walnut_build.log"; exit 1; }
cp "$KIT/Automata Library/"V*.txt "Automata Library/"
cp "$KIT/Command Files/"vn_*.txt "Command Files/"
run() {  # run <command file> <minutes>
  echo "==== $1 (limit $2 min) $(date)" | tee -a "$KIT/walnut_run.log"
  ( /usr/bin/time -l java -Xmx6g -jar target/Walnut-all.jar --global-session "$1" >> "$KIT/walnut_run.log" 2>&1 ) 2>> "$KIT/walnut_run.log" &
  pid=$!; ( sleep $(( $2 * 60 )); pkill -f "Walnut-all.jar --global-session $1" && echo "==== $1 STOPPED at the time limit" >> "$KIT/walnut_run.log" ) & killer=$!
  wait $pid; kill $killer 2>/dev/null
  echo "==== $1 done $(date)" | tee -a "$KIT/walnut_run.log"
}
run vn_compare.txt 60
run vn_750a.txt 30
run vn_750b.txt 30
cd "$KIT" && zip -qr walnut_results.zip walnut_run.log walnut_build.log Walnut/Result 2>/dev/null
echo "Done. Send back: $KIT/walnut_results.zip"
