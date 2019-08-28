structure Test =
struct
    structure U = Unlambda
    structure UY = Unlambdaify
    structure L = Lambda

    fun mix ul l =
        (UY.EApp (UY.load ul, L.load l))

    val PR = "^n`r``$n.*i"
    fun ntest s = (UnlambdaInterp.eval (UY.convert ((mix PR s))))



    val fibo = "```s``s``sii`ki  `k.*``s``s`ks" ^
               "``s`k`s`ks``s``s`ks``s`k`s`kr``s`k`sikk" ^
               "`k``s`ksk"

    val count2 = "``r`cd`.*`cd"

    val trivial1 =
        "```sii``si``s" ^
        "`k`d`r`.!`.l`.a`.i`.v`.i`.r`.t`. `.t`.s`.e`.'`.c`. `.,`.a`.d`.b`.m`.a`.l`.n.U" ^
        "i"

    val trivial2 =
        "```si``s" ^
        "`k`d`r`.!`.l`.a`.i`.v`.i`.r`.t`. `.t`.s`.e`.'`.c`. `.,`.a`.d`.b`.m`.a`.l`.n.U" ^
        "i`c``sii"

    val trivial3 =
        "```sii``si``s" ^
        "``s`kr``s`k.!``s`k.l``s`k.a``s`k.i``s`k.v``s`k.i``s`k.r``s`k.t" ^
        "``s`k. ``s`k.t``s`k.s``s`k.e``s`k.'``s`k.c``s`k. ``s`k.," ^
        "``s`k.a``s`k.d``s`k.b``s`k.m``s`k.a``s`k.l``s`k.n`k.U" ^
        "i"


    val N0 = "(^sz.z)"
    val S = "(^wyx.y(wyx))"
    val N1 = "(" ^ S ^ N0 ^ ")"
    val N2 = "(" ^ S ^ N1 ^ ")"
    val N3 = "(" ^ S ^ N2 ^ ")"

    val ADDN = "(^mn.m"^S^"n)"
    val MULTN = "(^xyz.x(yz)"

    val T = "(^xy.x)"
    val F = "(^xy.y)"

    val AND = "(^xy.xy"^F^")"
    val OR = "(^xy.x"^T^"y)"
    val NOT = "(^x.x"^F^T^")"

    val Z = concat [ "(^x.x", F, NOT, F, ")" ]

    val PHI = "(^pz.z("^S^"(p"^T^"))(p"^T^"))"

    val P = "(^n.n"^PHI^"(^z.z"^N0^N0^")"^F^")"

    (* val P = "(^n.n<PHI>(^z.z<NO><NO>)<F>)" *)

    val G = "(^xy."^Z^"(x"^P^"y))"
    val E = "(^xy."^AND^"("^Z^"(x"^P^"y))"^"("^Z^"(y"^P^"x)))"

    val Y = "(^y.(^x.y(xx))(^x.y(xx)))"

    val B2N = "(^p.p"^N1^N0^")"

    val SUM = "("^Y^"(^rn."^Z^"n"^N0^"(n"^S^"(r("^P^"n)))))"

end
