Walnut negative controls (add to walnut_kit/)
==============================================
Unzip this into the walnut_kit folder (it adds files; it changes none of the existing ones), then:
    cd ~/Downloads/walnut_kit && sh run_negative.sh
It reuses the Walnut that run_walnut.sh built, runs Command Files/vn_negative.txt with a 4 GB heap,
prints each answer next to its name, and writes walnut_negative_results.zip to send back.
expected.txt lists the answer each sentence must give; every expectation was checked beforehand in
Python by evaluating the automata on x, y < 32 (FALSE cases: a counterexample exists there).
Mutated tables: Automata Library/V926m.txt and V654m.txt (one transition changed in each).
Made by make_negative.py from the kit's V926.txt and V654.txt.
