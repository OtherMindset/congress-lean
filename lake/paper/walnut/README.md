# walnut/: the Walnut comparison (paper, Section 8.3)

- `kit/`: the inputs as run. `Automata Library/` holds the tables for Rules 926 and 654 and the two wrong
  candidates for Rule 750 as Walnut automata reading (x, y, t) in base 2, least significant digit first;
  `Command Files/` the seed, step and counting sentences; `run_walnut.sh` builds Walnut at commit
  `3bf0ece983279f34cbf657481fa472c1f1ab3932` and runs them; `count_from_walnut.py` turns Walnut's linear
  representations into the closed forms (exact integers) and compares the first terms with `sim_n9.json`.
- `results/`: what came back from the run of 20 Nov 2026, 06:01-06:02 EST, on an Apple MacBook Air with
  OpenJDK 21.0.13.1 (as printed in the author's terminal session). Before that run the heap in `run_walnut.sh` was lowered from `-Xmx6g` to `-Xmx4g`
  (`sed -i '' 's/-Xmx6g/-Xmx4g/' run_walnut.sh`); the copy in `kit/` is the script before that edit.
  `walnut_run.log` has every answer with `/usr/bin/time -l` figures: the 926/654 file in 1.34 s and 311 MB,
  every answer TRUE; each Rule 750 step check out of memory after 32.40 s and 31.46 s.
- `count_from_walnut_output.txt`: `python3 -I kit/count_from_walnut.py results/Walnut/Result`. Rule 926:
  3c(n) = 4*4^n - 1 for n >= 0 (dimension 196); Rule 654: 48c(n) = 53*4^n - 80 for n >= 3 (dimension 137);
  both agree with the simulation for n <= 9.
- `count_negative.py`, `count_negative_output.txt`: the same post-processing with six changed closed forms
  (constant, coefficient, leading coefficient, starting index, denominator); each is rejected, and the two
  correct forms are accepted.
- `make_negative.py`, `negative/`: negative controls for Walnut itself: two tables with one transition
  changed, three wrong rules, a moved seed, and two sentences that must hold. `expected.txt` gives each
  expected answer, checked beforehand in Python on x, y < 32. Run: `sh negative/run_negative.sh` from a kit
  folder where `run_walnut.sh` has built Walnut, with `negative/`'s files copied in.
