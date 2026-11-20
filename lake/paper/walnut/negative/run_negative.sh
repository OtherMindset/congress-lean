#!/bin/sh
# Walnut negative controls. Run from inside walnut_kit/ after run_walnut.sh (it reuses the Walnut it built).
# Usage:  sh run_negative.sh        Takes well under a minute.
set -u
KIT=$(cd "$(dirname "$0")" && pwd); cd "$KIT"
[ -f Walnut/target/Walnut-all.jar ] || { echo "Run run_walnut.sh first (it builds Walnut)."; exit 1; }
cd Walnut
echo "Walnut commit: $(git rev-parse HEAD)" | tee "$KIT/walnut_negative.log"
cp "$KIT/Automata Library/"V*.txt "Automata Library/"
cp "$KIT/Command Files/"vn_negative.txt "Command Files/"
echo "==== vn_negative.txt $(date)" | tee -a "$KIT/walnut_negative.log"
( /usr/bin/time -l java -Xmx4g -jar target/Walnut-all.jar --global-session vn_negative.txt >> "$KIT/walnut_negative.log" 2>&1 ) 2>> "$KIT/walnut_negative.log"
echo "==== done $(date)" | tee -a "$KIT/walnut_negative.log"
cd "$KIT" && echo && echo "Answers (compare with expected.txt):" && grep -E '^(eval|TRUE|FALSE)' walnut_negative.log | sed -E 's/^eval ([A-Za-z0-9_]+) .*/\1:/' | paste - - 
zip -q walnut_negative_results.zip walnut_negative.log expected.txt
echo "Send back: $KIT/walnut_negative_results.zip"
