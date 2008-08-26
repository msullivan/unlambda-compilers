structure Test =
struct
    structure U = Unlambda
    structure UY = Unlambdaify

    val ` = "`"
    val `` = "``"
    val ``` = "```"

    val N0 = "^s^z$z"
    val S = "^w^y^x`$y``$w$x$y"
    val N1 = "`" ^ S ^ N0
    val N2 = "`" ^ S ^ N1
    val N3 = "`" ^ S ^ N2

    val ADDN = "^m^n``$m" ^ S ^ "$n"
    val MULTN = "^x^y^z`$x`$y$z"



    val PR = "^n`r``$n.*i"

end
