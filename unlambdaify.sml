structure StringDict = SplayMapFn(
    struct
        type ord_key = string
        val compare = String.compare
    end)

structure UnlambdaifySyntax =
struct
    type ident = string
    datatype function = datatype Unlambda.value
    datatype expr = EApp of (expr * expr) | EFunc of function
                  | ELambda of (ident * expr) | EVar of ident

end

functor UnlambdaifyFn(val strict : bool) =
struct
    exception LexError
    exception ParseError of string

    structure U = Unlambda

    type ident = string

    datatype token = TApp | TK | TS | TI | TV | TC | TD |
                     TE | TAt | TPipe |
                     TDot of char | TQuest of char |
                     TLambda of char | TVar of char

    fun skip_line nil = nil
      | skip_line (#"\n"::s) = s
      | skip_line (_::s) = skip_line s

    fun lex nil = nil
      | lex (#"`"::s) = TApp::(lex s)
      | lex (#"k"::s) = TK::(lex s)
      | lex (#"s"::s) = TS::(lex s)
      | lex (#"i"::s) = TI::(lex s)
      | lex (#"v"::s) = TV::(lex s)
      | lex (#"c"::s) = TC::(lex s)
      | lex (#"d"::s) = TD::(lex s)
      | lex (#"e"::s) = TE::(lex s)
      | lex (#"@"::s) = TAt::(lex s)
      | lex (#"|"::s) = TPipe::(lex s)
      | lex (#"."::c::s) = (TDot c)::(lex s)
      | lex (#"?"::c::s) = (TQuest c)::(lex s)
      | lex (#"r"::s) = (TDot #"\n")::(lex s)
      | lex (#" "::s) = lex s
      | lex (#"^"::c::s) = (TLambda c)::(lex s)
      | lex (#"$"::c::s) = (TVar c)::(lex s)
      | lex (#"\t"::s) = lex s
      | lex (#"\n"::s) = lex s
      | lex (#"#"::s) = lex (skip_line s)
      | lex _ = raise LexError

    datatype function = datatype UnlambdaifySyntax.function
    datatype expr = datatype UnlambdaifySyntax.expr

    fun parse l =
        let
            fun str c = implode [c]

            fun parse' nil = raise ParseError "ran out of input"
              | parse' (TApp::l) =
                let
                    val (e1, l') = parse' l
                    val (e2, l'') = parse' l'
                in
                    (EApp (e1, e2), l'')
                end
              | parse' ((TLambda c)::l) =
                let
                    val (e, l') = parse' l
                in
                    (ELambda (str c, e), l')
                end
              | parse' (TK::l) = (EFunc VK, l)
              | parse' (TS::l) = (EFunc VS, l)
              | parse' (TI::l) = (EFunc VI, l)
              | parse' (TV::l) = (EFunc VV, l)
              | parse' (TC::l) = (EFunc VC, l)
              | parse' (TD::l) = (EFunc VD, l)
              | parse' (TE::l) = (EFunc VE, l)
              | parse' (TAt::l) = (EFunc VAt, l)
              | parse' (TPipe::l) = (EFunc VPipe, l)
              | parse' ((TDot c)::l) = (EFunc (VDot c), l)
              | parse' ((TQuest c)::l) = (EFunc (VQuest c), l)
              | parse' ((TVar c)::l) = (EVar (str c), l)
            val (exp, rest) = parse' l
        in
            if (not (null rest)) then raise ParseError "trailing garbage"
            else exp
        end

    fun unparse (EApp (e1, e2)) = "`" ^ (unparse e1) ^ (unparse e2)
      | unparse (ELambda (s, e)) = "^" ^ s ^ unparse e
      | unparse (EVar s) = "$" ^ s
      | unparse (EFunc f) =
        (case f
          of VK => "k" | VS => "s" | VI => "i" | VV => "v" | VC => "c"
           | VD => "d" | VE => "e" | VAt => "@" | VPipe => "|"
           | VDot #"\n" => "r"
           | VDot c => (implode [#".", c])
           | VQuest c => (implode [#"?", c])
        )

    local
        fun kapp e = EApp (EFunc VK, e)
        fun sapp (x, y) = (EApp(EApp(EFunc VS, x), y))

        fun safe_to_apply e =
            (case e of
                 EFunc VI => true
               | EFunc VK => true
               | EFunc VS => true
               | EApp (EFunc VS, _) => true

               | _ => false)

        val always_safe = not strict

        fun elim x e =
            (case e of
                 EFunc f => (kapp (EFunc f), true, false)
               | EVar x' =>
                 if x = x'
                 then (EFunc VI, true, true)
                 else (kapp (EVar x'), true, false)
               | ELambda (y, e) =>
                 let val (e', ysafe, hasy) = elim y e
                     val (e'', xsafe, hasx) = elim x e'
                 in
                     (* XXX: or should it be xsafe??? *)
                     ((*if (ysafe orelse always_safe) andalso not hasx*)
                       (* this should always be safe, right??? *)
                       if not hasx

                      then (kapp e') else e'',
                      true,
                      hasx)
                 end
               | EApp (e1, e2) =>
                 let val (e1', safe1, has1) = elim x e1
                     val (e2', safe2, has2) = elim x e2
                     val has = has1 orelse has2
                     val safe = safe1 andalso safe2 andalso safe_to_apply e1
                 in
                     (if (safe orelse always_safe) andalso not has
                      then kapp e
                      else sapp (e1', e2'),
                      safe,
                      has)
                 end

            )

    in
    fun convert (EApp (e1, e2)) = (U.EApp (convert e1, convert e2))
      | convert (ELambda (x, e)) =
        let val (e', _, _) = elim x e
        in convert e' end
      | convert (EFunc f) = (U.EFunc f)
      | convert (EVar s) = raise Fail ("variable: " ^ s)

    fun shrink (U.EApp (e1, e2)) =
        (case (shrink e1, shrink e2) of
            (* ``s`kki => k *)
            (U.EApp (
                  U.EFunc U.VS,
                  U.EApp (U.EFunc U.VK, U.EFunc U.VK)),
             U.EFunc U.VI
            ) => U.EFunc U.VK
          (* ``skX => i *)
          | ((U.EApp (U.EFunc U.VS, U.EFunc U.VK),
              U.EFunc _)
            ) => U.EFunc U.VI
          | (U.EFunc U.VI, e) => e
         | (e1', e2') => U.EApp (e1', e2'))
      | shrink f = f


    fun remove_is (U.EApp (e1, e2)) = U.EApp (remove_is e1, remove_is e2)
      | remove_is (U.EFunc U.VI) =
        (* i => ``skk *)
        U.EApp (U.EApp (U.EFunc U.VS, U.EFunc U.VK), U.EFunc U.VK)
      | remove_is e = e

    end

    structure Ctx = StringDict

    datatype result = RFun of result -> result
                    | RDelay
    exception Done of result
    fun unRFun (RFun f) z = f z
      | unRFun RDelay z = z

    fun apply v1 e2t =
        (case v1 of
             RFun f1 => f1 (e2t ())
           | RDelay => RFun (fn r => unRFun (e2t ()) r))

    fun eval_func (out as ((pipef, cur), outp)) f =
        (case f of
             VI => RFun (fn x => x)
           | VK => RFun (fn x => RFun (fn _ => x))
           | VS => RFun (fn x => RFun (fn y => RFun (fn z =>
                     apply (unRFun x z) (fn () => unRFun y z))))
           | VV => RFun (fn _ => eval_func out VV)
           | VDot c => RFun (fn x => (outp c; x))
           | VD => RDelay
           | VC => RFun (
                      fn x =>
                         Cont.callcc (fn k => unRFun x (
                                                 RFun (fn y => Cont.throw k y))))
           | VE => RFun (fn x => raise Done x)
           | VAt => RFun (fn x => unRFun x (eval_func out ((if pipef () then VI else VV))))
           | VPipe =>
             RFun (
                 fn x => unRFun x (
                            eval_func out (case !cur of SOME x => VDot x | NONE => VV)
                        )
             )
           | VQuest c =>
             RFun (
                 fn x => unRFun x (eval_func out (if !cur = SOME c then VI else VV))
             )
        )

    fun eval out env e =
        (case e of
             EVar v => valOf (Ctx.find (env, v))
           | EApp (e1, e2) =>
             (case eval out env e1 of
                  RFun f1 => f1 (eval out env e2)
                | RDelay => RFun (fn r => unRFun (eval out env e2) r))
           | ELambda (v, e) =>
             RFun (fn r => eval out (Ctx.insert (env, v, r)) e)
           | EFunc k => eval_func out k
        )

    (* val evalTop = eval Ctx.empty *)

    val load = (parse o lex o explode)
    (* val exec' = evalTop o load *)
    val transform = (convert o load)
    val stransform = (U.unparse o transform)
    (* val exec = (UnlambdaInterp.eval o transform) *)

    fun eval' out ctx e = eval out ctx e handle Done v => v
    fun eval_with_io e (out : char -> unit) (inp : unit -> char option)
        = eval' (Output.make_io inp, out) Ctx.empty e
    fun eval_with_output e (out : char -> unit) = eval_with_io e out Output.getc
    fun eval e = eval_with_output e (Output.int_output Output.putc)

end

structure Unlambdaify = UnlambdaifyFn(val strict = true)
structure UnlambdaifyLazy = UnlambdaifyFn(val strict = false)
