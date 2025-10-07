structure Test =
struct
    structure U = Unlambda
    structure UY = Unlambdaify
    structure L = Lambda

    fun mix ul l =
        (UY.EApp (UY.load ul, L.load l))

    val PR = "^n`r``$n.*i"
    fun ntest s = (UnlambdaInterp.eval (UY.convert ((mix PR s))))

    fun run_captured' f e limit =
        let
            val (get, putc) = Output.captured_int_output limit
            val () = (ignore (f e putc) handle Output.Done => ())
        in get () end
    fun run_captured f e = run_captured' f e (SOME 10)

    fun run_print_captured f e = print (run_captured f e)

    fun lines s = String.concatWith "\n" s ^ "\n"

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

    (* Huh, it's missing the leading U!! *)
    val trivial_result = "nlambda, c'est trivial!\nUnlambda, c'est trivial!\nUnlambda, c'est trivial!\nUnlambda, c'est trivial!\nUnlambda, c'est trivial!\nUnlambda, c'est trivial!\nUnlambda, c'est trivial!\nUnlambda, c'est trivial!\nUnlambda, c'est trivial!\nUnlambda, c'est trivial!\n"

    fun check expected actual =
        if expected = actual then "OK" else (
            "ERROR:\nExpected:\n" ^ expected ^ "\nActual:\n" ^ actual
        )

    fun run_test (fname, func) (tname, prog, expected) =
        let
            (* val () = print (prog ^ "\n") *)
            val () = print (fname ^ ", " ^ tname ^ ": ")
            val res = run_captured func prog
            val () = print (check expected res ^ "\n")
        in () end

    val ite = "``s`kc``s`k`s`k`k`ki``ss`k`kk"

    val tests = [
        (
          "d1",
          "` ` d `.Bi `.Ai",
          "AB"
        ),
        (
          "d2",
          "` ` `id `.Bi `.Ai",
          "AB"
        ),
        (
          "d3",
          "` ` `dd `.Bi `.Ai",
          "BA"
        ),
        (* This one I screwed up! ```si.Ad -> ` `id `.Ad -> `d`.Ad -> don't print *)
        (* s needs to potentially delay *)
        (
          "d4",
          "```si.Ad",
          ""
        ),
        (
          "c1",
          "````" ^ ite ^ "i.T.Fi",
          "T"
        ),
        (
          "c2",
          "````" ^ ite ^ "v.T.Fi",
          "F"
        ),
        (
          "c3",
          UY.stransform "``c ^k`$k.A i",
          "A"
        ),
        (
          "c3'",
          UY.stransform "``c ^k``$k.A`.Bi i",
          "A"
        ),
        (
          "c3''",
          UY.stransform "```c ^k``$k.A`.Bi .Ci",
          "AC"
        ),
        (
          "c3'''",
          UY.stransform "````i c ^k``$k.A`.Bi .Ci",
          "AC"
        ),
        (
          "c4",
          UY.stransform "``c ^k.A i",
          "A"
        ),

        (
          "fibo",
          fibo,
          "\n" ^ (lines o map Int.toString) [1, 1, 2, 3, 5, 8, 13, 21, 34]
        ),
        (
          "count2",
          count2,
          "\n" ^ (lines o map Int.toString) [1, 2, 3, 4, 5, 6, 7, 8, 9]
        ),
        (
          "trivial",
          trivial1,
          trivial_result
        ),
        (
          "trivial2",
          trivial2,
          trivial_result
        ),
        (
          "trivial3",
          trivial3,
          trivial_result
        )
    ]

    fun i2 f x = ignore (f x)

    val impls = [
        ("basic", i2 o UnlambdaInterp.eval_with_output o Unlambda.load),
        (
          "lambda",
          i2 o Unlambdaify.eval_with_output o LowerUnlambda.cps_program o LowerUnlambda.delay_program o LowerUnlambda.expand_unlambda o Unlambda.load
        ),
        ("micro-unlambda", i2 o UnlambdaInterp.eval_with_output o Unlambda.load o UnlambdaToMicroUnlambda.translate),

        (
          "lazyk",
          i2 o LazyK.runCombNoInput o LazyK.convExp o LazyK.parseExp o Unlambda.unparse o UnlambdaifyLazy.convert o LowerUnlambda.cps_program_lazyk o LowerUnlambda.delay_program o LowerUnlambda.expand_unlambda o Unlambda.load
        ),

        ("SML delay", i2 o UnlambdaDelay.eval_with_output o Unlambda.load),
        ("SML cps", i2 o UnlambdaCps.eval_with_output o Unlambda.load)

    ]

    fun run_tests () =
        List.app (fn impl => List.app (run_test impl) tests) impls

    fun run_timed f =
        let val t0 = Time.now ()
            val x = f ()
            val t1 = Time.now ()
        in (Time.toReal (Time.- (t1, t0)), x) end

end
