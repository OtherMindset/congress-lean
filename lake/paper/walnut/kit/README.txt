Walnut head-to-head kit (VN library tables)
===========================================
What it runs (Walnut, commit 3bf0ece9, built from source):
  vn_compare.txt  Rule 926 (166 states) and Rule 654 (104 states):
                  seed check, step check (rule as a Boolean formula over the 5 neighbourhood values,
                  mirror at x = 0 and y = 0), the Rule 990 step check on the 926 table, and the four
                  counting automata S, X, Y, O with linear representations in g (Sage/Maple/... files).
  vn_750a.txt     Rule 750, the 367-state candidate (known wrong): seed and step checks.  30-min limit.
  vn_750b.txt     Rule 750, the 401-state candidate (known wrong): seed and step checks.  30-min limit.
Expected: TRUE for every 926/654 check; FALSE for the 750 step checks (if Walnut finishes).

Run on a Mac:   cd walnut_kit && sh run_walnut.sh
Needs: git, Java 17 or later ("java -version"; e.g. brew install openjdk@21), about 6 GB of free memory.
Send back:      walnut_results.zip  (the run log with Walnut's timings, the build log, Walnut/Result/)

Then:           python3 count_from_walnut.py Walnut/Result   (proves the closed forms from Walnut's
                linear representations, exact integer arithmetic; compares with sim_n9.json)
