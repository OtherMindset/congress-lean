# Coverage computation for the exact-arithmetic eps = 1e-8 certificate (eps1e-8_exact.py; port of
# #mwo53bqy-nzojc8).  Exact rational arithmetic only.  TREE below is the bisection tree that eps1e-8_exact.py
# builds, written as its symbol sequence in pop order (0 = box accepted, 1 = split at the k-midpoint, 2 = split
# at the phi-midpoint), four symbols per character (index = 27 s1 + 9 s2 + 3 s3 + s4 in ALPHA; padding zeros at
# the end are ignored).  This file decodes TREE with the same stack discipline as the certificate and proves:
#   the accepted boxes tile R = [0, 805/1024] x [0, 1609/1024] (k x phi).
# Argument: the decoder keeps the invariant "the boxes on the stack and the accepted boxes tile R" (true at
# the start; a split replaces one closed box by its two closed halves, which tile it).  At the end the stack is
# empty, so the accepted boxes tile R.  As a cross-check the exact areas are summed.  The base-3 fingerprint
# (mod 2^61-1) printed here must equal the one printed by eps1e-8_exact.py: that ties TREE to the
# certificate's own run (the certificate itself checks every box it accepts).
from fractions import Fraction as Fr

ALPHA = "".join(chr(c) for c in range(33, 127) if chr(c) not in '"\\\\')[:81]
NSYM = 29733
TREE = """
NTTR+b>b?>)b?>'>)%2b?>'>)%9>)%2%7+ib?>'>)%9>)%2%7+T>)%2%7+i%7+R+b>ib?>'>)%9>)%2%7+T>)%2%7+i%7+R+
b?T>)%2%7+i%7+R+b>i%7+R+b?R+b>b?>)ib?>'>)%9>)%2%7+T>)%2%7+i%7+R+b?T>)%2%7+i%7+R+b>i%7+R+b?R+b>b?
>'T>)%2%7+i%7+R+b>i%7+R+b?R+b>b4ib?>'>)%9>)%2%7+T>)#Z)b4OYii%7+R+b?R+b>b?=T=YZ)Z'(9R+b>b4i$=OYh4
OZOYZ'T(14h4OYh4OZOYZ)h4OZOYZ'OYZ)Z'(9T(14h4OYh4OZOYZ)h4OZOYZ'OYZ)Z'(2h4OZOYZ'OYZ)Z'(9OYZ)Z'(2Z'
(9(14iib?>'>)%9>)%2%7+T>)%2%7+i%7+R+b?T>)%2%7+i%7+R+b>i%7+R+b?R+b>b4TR+b>b7)b?=OYh4OZOYZ)h4OZOYZ
'OYZ)Z'(9T>)%2%7)Z'(2Z'(9(14iZ'(9(14T(14h4OYiZ'(9(14T(14h4OZT(14h4OYh4OZOYZ'TOYZ)Z'(2Z'(9(14iZ'(
9(14T(14h4OYiZ'(9(14T(14h4OZT(14h4OYh4OZOYZ)iZ'(9(14T(14h4OZT(14h4OYh4OZOYZ'T(14h4OYh4OZOYZ)h4OZ
OYZ'OYZ)Z'(2ih4OZOYZ'OYZ)Z'(9OYZ)Z'(2Z'(9(14TOYZ)Z'(2Z'$OY)h4OZOYZ'O+b?TOYZ)Z'(2Z'(9(14iZ'(9(14T
(14h4OYiZ'(9(+R+b?T(+b>b?>'T>)%2%7+i%7+R+b>i%7+R+b?R+b>b?>)i%7+R+b?R+b>b?>'R+b>b?>)b?>'>)%9TOYZ)
Z'(2Z'(9(1)h4OZOYZ'OY)Z%2b?>'>)%9>)%2%7+ih4OZOYZ'>)%9OYZ)Z%2%7+T>)%2%7+i%7+R+b>ib?>'>)%9>)%2%7+T
>)%2%7+i%7+R)$T>)%2%7+i%7+R+b>i%7+R(9>)%14iib?>'>)$R+b>b4T(14h4OZT>)#Z)b4OYh4OZOYZ'T(14h4OYh4OZO
YZ)h4OZOYZ'OYZ)Z'(9T(14h4OYh4OZOYZ)h4OZOYZ'OYZ)Z'(2h4OZOYZ'OYZ)Z'(9OYZ)Z'(2Z%9#'TOYZ)Z'(2Z'(9(14
iZ'(9(14T(1)X>iZ'(9(14T(14h'$R+b>b?>)iZ%7+R+b?R+b>b?>'R+b>b?>)b?>'>)%9iiZ'(9(14T(14h4OZT(14h4OYh
4OZOYZ'T(14h4OYh4OZOYZ)h4OZOYZ'OYZ)Z'(9T(14h4OYh4OZOYZ)h4OZOYZ'OYZ)Z'(2h4OZOYZ'OYZ)Z'(9OYZ)Z'(2Z
'(9(14TT(14h4OYh4OZOYZ)h4OZOYZ'OYZ)Z'(2h4OZOYZ'OYZ)Z'(9OYZ)Z'(2Z'(9(14ih4OZOYZ'OYZ)Z'(9OYZ)Z'(2Z
'(9(14TOYZ)Z'(2Z'(9(14iZ'(9(14T(+h4?TT(+h4>b?>)b?>'>)%2b?>'>)%9>)%2%7+ib?>'>)%9>)%2%7+T>)%2%7+i%
7+R+b>ib?>'>)%9>)%2%7+T>)#Z)b7'(9R+b>b?>)b?>'>)%2b7'(9=b14ipOYZ)Z'(2Z'(9(14iZ'(9(14T(14h4OZVZ'(9
(14j(:4U4kYp(14h4OZU4kYkZZ'iZ'(9(14T(14h4OZT(14h4OYh4?OY)p(14h4OZU4kYkZZ'h4OZOY)kZZ'Xk9T>)%2%7+i%
7+R+b>i%7+R+b?R+b>b?>)i%7+R+b?R+b>b?>'R+b>b?>)b?>'>)%2i%7+R+b?R+b>b?>'R+b>b7)b?>'=b9R+b>b?>)b?>'
>)%2b?>'=b9>)%2$=Ti%7+R+b?R+b>b?>)n+b?OYZ'b?>)Z'(3R+b>b?>)b7'(9b?>)Z'(3=Z>)iZ'(9(14T(14h4OZT(14h
4OYh4OZOYZ'T(14h4OYb?>)h4OZOYZ'>)%3TOYZ)Z'(2Z'(9(14iZ'(9(14T(14h4OYiZ'(9(1'>)%9OY)Z%2%7+ib?>'>)%
9>)%2%7+T>)%2%7+i%7+R+b?Th4OZOYZ)kZ>'Z)%3O+b?OYZ)i%7+R+b?R+b>b?>'OYZ)Z'(2n+b?OYZ'b?>)Z'(9OYZ)Z'(
2Z'(9(14NTT>)%2%7+i%7+R+b>i%7+R+b?R+b>b?>)i%7+R+b?R+b>b?>'R+b>b?>)b?>'>)%2i%7+R+b?R+b>b?>'R+b>b7
)b?>'=b9R+b>b?>)b?>'>)%2b?>'=b9>)%2$=ii%7+R+b?R+b>b?>'R+b>b?>)b?>'>)%9R+b>b?>)b?>'>)%2b?>'>)%9>)%
2%7+TR+b>b?>)b?>'>)%2b?>'=b9>)%2$=ib?>'>)%9>)%2%7+T>)%2$>)b?>'>)%2iZ'(9(14T(14h4OZT(14h4OYh4OZOY
Z'T(14h4OYb?>)h4OZOYZ'>)%9T(14h4OYh4OZOYZ)h4OZOYZ'OYZ)Z'(2h4OZOYZ'>)%9OYZ)Z'(2%7+ii%7+R+b?R+b>b?
>'OYZ)Z'(9R+b>b?>)b?>'>)%2b7'(9=b14TOYZ)Z'(2Z'(9(14iZ'(9(14T(14h4OZVib?>'>)%9>)%2%7+T>)%2%7+i%7+
R+b?T>)%2%7+i%7+R+b>i%7+R+b?R+b>b?>'T>)%2%7+i%7+R+b>i%7+R+b?R+b>b?>)i%7+R+b?R+b>b?>'R+b>b?>)b?>'
>)%9T(14i$=OYh4OZOYZ)i$=OZR)%14T(14h4OYiZ'(9(14R+b?T(14h4OYb?>)pR+b>b?>)b?>'>)%2b?>'>)%9>)%2%7+i
b?>'>)%9>)%2%7+T>)%2%7+i%7+R+b?Vb?>'>)%9>)%2%7+iZ=OZR+b>Z=T(14h4OYp>)%2%7+i%7+R+b?T(14h4OYh4OZOY
Z'ib?>'(9>)%2$=T(14h4OZT(14h4OYb?C+jR+b>b7+h4OZT(14h4OYb?>'h4OZOY)b?>'=b3T>)%2%7+i%7+R+b>i$>'(9>
)%17)h4OZOYZ'OYZ)Z'(9i%7+R+b?R+b>b7+j>)%9(14V%7+h4OYp(14h4OZV$)Z%3(7+TTT>)%2%7+i%7+R+b>h4OZR)#Z)
i%7+R+b?R+b>b?>'R)%14i%7+Ob2h4OZOYZ'OYZ)Z'(9OYZ)Z'(2Z'(9(14ii%7+R+b?R+b>b?>'R+b>b7)b?>'>)%9R+b>b
?>)b?>'>)%2b?>'>)%9>)%2%7+TOYZ)Z'(2Z'(9(14ib7'(9=b>Z'OYZ)Z'(2iZ'(9(14R+b?T(14h4OYb?C+T>)%2$>)b?>
'>)%9T(14h4OYh4?OY)h4OZOYZ'OY)Z%2b?>'>)%9>)%2%7+iib?>'>)%9>)%2%7+T>)%2%7+i%7+R+b?T>)%2%7+i%7+R+b
>i%7+R+b?R+b>b?>'T>)%17)b?>'=b2Z'(9(14ib?>'>)%9>)%2%7+T(14i$=OYpR+b>b?>)b?>'>)%2b?>'>)%9>)%2%7+i
b?>'>)%9>)%2%7+T>)%14i%7+R)$Vb?>'>)%9>)%2%7+p>)%2%7+i%7+R+b>p>)%2%7+i%7+R+b?i%7+R+b?R+b>b?>'TOYZ
)Z'(2Z%9(-)h4OZOYZ'OYZ)Z'(2b?>'>)%9>)%2%7+Vh4OZOYZ'OYZ)Z'(9>)4>b?>)p(14h4OZi$=OZOYZ'h4?>*OY)%2iZ
'(9(14T(14h4OZT)#Z)b7'(2Z'(9(14TOY)Z%2%7+iZ'(9(14R+d%9T>)%14i%7+R)#h4OZOYZ'i%7+R+b?OYZ)n+b?b?>'b
4n+YiZ'(9(14T(14h4OYp(14h4OZU4kYkZZ'TTOYZ)Z'(2Z'(9(14iZ'(9(14T(14h4OYiZ'(9(14T(14h4OZT(14h4OYh4O
ZOYZ)iZ'(9=b>Z=T(14h4OZT>)%2%7+i%7+R+b>h7'(9=b>Z'T(14h4OYh4OZOYZ)h4OZOYZ'OYZ)Z'(2iZ%9(+R+b?T(+h4
>b?>'R+b>Z)b?>'(9T(+h4OYb?>)h4OZOYZ'>)%2b?>'=b9>)%2$>)ii%7+R+b?R+b>b?>'R+b>b7)b?>'>)%9R+b>b?>)b?
>'>)%2b?>'>)%9>)%2%7+TOYZ)Z=OYh4OZOYZ)i$>'(9>)%17'OYZ)Z'(9T>)%2%7+i%7+R+b>i%7+R+b?R+b>b?>)i%7+R+
b?R+b>b?>'R+b>b?>)b?>'>)%2i%7+R)%9>)%2%7+T(14i$=OZT>)%2%7+i%7+R+b>i%7+OZR+b>b7+TT(14h4OYb?C+iZ'(
9(14T(+h4>i%7+R+b?R+b>b?>)iZ'(9(14T(+h4OZT(14h4OYh4OZOYZ'R+b>b?>)b?C+R+b>ih4OZOYZ'OY)Z'(9OYZ)Z'(
2Z'(9(14T>)%2%7+i%7Y'>)%9T)#Z)b7+OYh4OZOYZ)i%7+Ob9>)%2%7+T(14h7'(2h4?OYZ'>)4?T(14h4OYh4OZOYZ'TTO
YZ)Z'(2Z'(9(14iZ'(9(14T(14h4OYiZ'(9(14T(14h4OZT(14h4OYh4OZOYZ)iZ'(9(14T(14h4OZT(14i%7+Ob2Z'(9(14
TOYZ)Z'(2Z'(9(14iZ'(9(14T(14h4OYib?>'>)%9C+h4>b?>'R)#Z)b7+OZTOY)Z%2%7+iZ%9(-'>)%2b?>'(9>)%2$=iib
?>'>)%9>)%2%7+T=b14i%7+Ob9R+b>b?>)b?>'>)%2b?>'>)%9>)%2%7+TOYZ)Z'(2Z'(9(14iZ'(9=b>Z'OYZ)Z'(9T>)%2%
7+i%7+R+b>i%7+R+b?R+b>b?>)i%7+R+b?R+b>b?>'R+b>b?>)b?>'>)%2i%7+Ob9>)%2%7+T(14h4OZT>)%2%7+i%7+R+b>
i$>'(9>)%17'TOYZ)Z'(2%7+iZ'(9(14R+h4>i%7+R+b?R+b>b?>)iZ'(9(14T(+h4?T(14h4OYh4OZOYZ'R+b>b?>)b?>'>
)%2iZ'(9(14T(+h4?T(14h4OYh4C9(14T>)%2%7+i%7+R+b?TOYZ)b7'(2Z'(9(14ib?>'(9>)%2$>'OYZ)Z'(2d%9(-'>)%
9OYZ)Z'(2Z%ZOYZ'TTb?>)Z'(3>)%9(14iZ'(9(14T(14h4OYj>)%9(14V%7+h4OZT(14h4OYh4OZOYZ)iZ'(9(14T(14h4O
ZT(14h4OYh4OZOYZ'T(14h4OYh4OZOYZ)h4OZOYZ'OYZ)Z'(2j(7+U4b?R+b>b?>'U)#Z)b7'(9T(+h4>b?>)h4?OY'>)%2b
?>'(9>)%17)ii%7+R)%9>)%2%7+T(14i$>'(9R+b>b?>)b?>'>)%2b?>'=b?R+b>b?>'T(14h4OYh4OZOYZ)h4OZOb14T(14
h4OZTR+b>b?>)b?>'>)%2b?>'>)%9>)%2%7+ib?>'>)%9>)%2%7+T>)%2%7+i%7+R+b>ib?>'(9>)%2$>'OYZ)Z'(9R+b>b?
>)b?>'>)%2Z=OZR+b>Z'TOY4h4OYb?>)h4OZOYZ'>)%2b?>'=b?R+b>b?>)iZ'(9(14T(+h4?T(14h4OYh4C9(14T>)%2%7+
i%7+R+b>ih4OZOYZ'C+h4?T(14h4OYh4?OY4T>)%2%7+i%7+R+b?TOYZ)Z=OYh4OZOYZ)i$>'(9>)%2$>'OYZ)Z'(2b?OY'>
)%9OYZ)Z'(24?OYZ'TTb?>)Z'(3>)%9(14iZ'(9(14T(14h4OYj>)%9(14V%7)Z'(9OYZ)Z'(2Z'(9(14ih4OZOYZ'OYZ)Z'
(9OYZ)Z'(2Z'(9(14TOYZ)Z'(2Z'(9(14iZ'(9(14T(14h4OYikZ>'Z)%9>)%2%7+T)#Z)b7'(9R+h4>b?>)h4?OY'>)%2b?
>'(9>)%17)ih7+OZR+b>b?>'OYZ)Z=OZT>)%2%7+i%7+R+b>i%7+Ob9>)%2$>'T(14h4OYh4OZOYZ)h4OZOYZ'OYZ)Z'(9T>
)%2%7+i%7+R+b>i%7+R+b?R+b>b?>)i%7+R+b?R+b>b?>'R+b>b?>)b?>'>)%2i$>'(9>)%17'OYZ)Z'(9R+b>b?>)b?>'>)%
2Z'(9=b>Z'TOY)Z'(2%7+iZ'(9(14R+b>i%7+R)%9>)%2%7+ih4OZOYZ'C+h4?T(14h4OYh4?OYZ'R+b>b?>)b?>'>)%2iZ'
(9(14R+h4?T(14h4OYh4?OY4T>)%2%7+i%7+R+b?TOYZ)Z=OYh4OZOYZ)i$>'(9>)%2$>'OYZ)Z'(2b?OY'>)%9OYZ)Z'(24
?OYZ'TTb?>)Z'(3>)%9(14iZ'(9(14T(14h4OYj>)%9(14V%4h4?T(14h4OYh4OZOYZ)iZ'(9(14T(14h4OZT(14h4OYh4OZ
OYZ'T(14h4OYh4OZOYZ)h4OZOYZ'OYZ)Z'(2j(7+U4b?R+b>b?>'OYZ)b7'(9R+b>b?>)b?OY'>)%2b7+OZR+b>Z)ih4OZOY
Z'OYZ)Z'(9Ob>Z=i%7+R+b>h4OZOb14TOYZ)Z'(2Z'(9(14iZ'(9(14T(14h4OZTR+b>b?>)b?>'>)%2b?>')$R+b>b?>)i%
7+R+b?R+b>b?>'R+b>b?>)b?>'>)%2h4OZOb14T(14h4OZT=b>Z)b?>'=b2Z'(9(14TT(+h4>b?>)h4?OYZ'>)%2b?>'=b9>
)%2%7+ih4OZOYZ'>)%9OYZ)Z'(2Z%9(+T>)%2%7+i%7+R+b>ih4OZOYZ'>)4?T(14h4OYh4?OY'R+b>b?>)b?>'>)%9T(14h
4OYh4OZOYZ)i$=OZR+b>Z=T(14h4OYi%7Y'>)%9OY4h4OYb?OY4TTV%7+h4OYn+b?OYZ)h4OZOYZ'OYZ)Z'(2n+b?OYZ'Z)%
9OYZ)Z'(2%7+ih4OZOYZ'OYZ)Z'(9OYZ)Z'(2Z'(9(14TOYZ)Z'(2Z%9(+iZ'(9(14T(+h4>ikZ>'Xb?R+b>b?>'OYZ)Z'(9
R+b>b?>)b?>'>)%2Z=OZR)#Z)ih4OZOYZ'OYZ)Z'(9OYZ)Z'(2Z'(9(14TOYZ)Z'(2Z%9(+iZ'(9(14T(+h4?TOYZ)Z'(2Z'
(9(14iZ'(9(14T(14h4OYiZ'(9(14T(-)Z'(9OYZ)Z'(2Z'(9(14TR+b>b?>)b?>'>)%2b7+OZR+b>Z)i%7+R+b?R+b>b?>'
R+b>b7)b?>'>)%2iZ'(9(14R+b?T(14h4OYb?C+T>)%2%7+i%7+R+b?TOYZ)Z'(2Z%9(+iZ'(9(14T(14h4OYi%7+R+b?R+d%
2%7+TTU4b>kZ>)b?>'>)%2kZ>'Z)%9>)%2%7+ib?>'>)%9>)%2%7+T>)%2%7+i%7+R+b>iZ'(9(14T(14h4OZT(14h4OYh4O
ZOYZ)ib?>'>)%9>)%2%7+T>)%2$=i%7+R(9R+b>b?>)b?>'>(2b?=OZOYZ'T(14h4OYh4OZOYZ)h4OZOYZ'OYZ)Z%2i%7+R+
b?R+b>b?>'R)%14i%7+R)%9R+b>b?>)b?>'>)%2b?>'>)%9>)%2%7+TT>)%2%7+i%7+R+b>i%7+R(9=YZ)i$'(9(1'OYZ)X>
iZ'(9(14T(14h4O9OYXb>b?>'T(1)%2XO7+O!
"""


def need(ok, msg):
    if not ok:
        print("FAILED:", msg)
        raise SystemExit(1)


letters = "".join(TREE.split())
syms = []
for ch in letters:
    v = ALPHA.index(ch)
    syms += [v // 27, (v // 9) % 3, (v // 3) % 3, v % 3]
need(len(syms) >= NSYM and not any(syms[NSYM:]), "length/padding")
syms = syms[:NSYM]
K0, KMAX, PMAX = Fr(0), Fr(805, 1024), Fr(1609, 1024)
stack = [(K0, KMAX, Fr(0), PMAX)]
leaves, area, fp, depth = 0, Fr(0), 0, 0
for i, sym in enumerate(syms):
    need(len(stack) > 0, "stack empty before the end of TREE (symbol %d)" % i)
    kl, kh, pl, ph = stack.pop()
    kc, pc = (kl + kh) / 2, (pl + ph) / 2
    if sym == 0:
        leaves += 1
        area += (kh - kl) * (ph - pl)
    elif sym == 1:
        stack += [(kl, kc, pl, ph), (kc, kh, pl, ph)]
    else:
        stack += [(kl, kh, pl, pc), (kl, kh, pc, ph)]
    fp = (fp * 3 + sym) % ((1 << 61) - 1)
need(len(stack) == 0, "boxes left undecided")
need(area == (KMAX - K0) * PMAX, "area")
print("symbols:", NSYM, "; accepted boxes:", leaves, "; splits:", NSYM - leaves)
print("exact total area =", area, "= 805/1024 * 1609/1024")
print("split-tree fingerprint =", fp)
print("CERTIFIED: the %d accepted boxes of the tree tile [0, 805/1024] x [0, 1609/1024] (k x phi)" % leaves)
