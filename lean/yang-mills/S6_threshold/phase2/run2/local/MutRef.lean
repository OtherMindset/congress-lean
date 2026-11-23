import GAffEval
/-!
# S6 phase 2: the reference file as theorems

One theorem per line of `python/yang-mills/S6_threshold/G_affine_reference.txt` (SHA-256 012e7361...):
`out b` is the five integers (c, a1, a2, a3, e) of the affine form of G that `GAff.gform` computes for
the box b, followed by the box test `check b`. Each right-hand side is copied from the reference file,
with `true` appended (every one of the 20 boxes passes in the Python program too). Proved by
`decide +kernel`, so Lean's kernel evaluates `gform` and compares integer for integer.
A box is mu in [mln/mld, mhn/mhd], r in [rln/rld, rhn/rhd], d in [dln/dld, dhn/dhd].
-/
open GAff

theorem ref01 : out ⟨0, 1, 1, 10, 0, 1, 1, 10, 0, 1, 1, 10⟩ =
    (-1266790716429935892, 3557134024578336, 748344278582536, 1526502251810112, 82338656494932946, true) := by decide +kernel
