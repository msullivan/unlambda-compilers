structure Unlambdaify =
struct
    exception LexError
    exception ParseError of string

    structure U = Unlambda

    type ident = string

    datatype token = TApp | TK | TS | TI | TV | TC | TD |
             TDot of char | TLambda of char | TVar of char

    fun lex nil = nil
      | lex (#"`"::s) = TApp::(lex s)
      | lex (#"k"::s) = TK::(lex s)
      | lex (#"s"::s) = TS::(lex s)
      | lex (#"i"::s) = TI::(lex s)
      | lex (#"v"::s) = TV::(lex s)
      | lex (#"c"::s) = TC::(lex s)
      | lex (#"d"::s) = TD::(lex s)
      | lex (#"."::c::s) = (TDot c)::(lex s)
      | lex (#"r"::s) = (TDot #"\n")::(lex s)
      | lex (#" "::s) = lex s
      | lex (#"^"::c::s) = (TLambda c)::(lex s)
      | lex (#"$"::c::s) = (TVar c)::(lex s)
      | lex (#"\t"::s) = lex s
      | lex (#"\n"::s) = lex s
      | lex _ = raise LexError

    datatype expr = EApp of (expr * expr) | EFunc of function
                  | ELambda of (ident * expr) | EVar of ident
         and function = VK | VS | VI | VV | VC | VD | VDot of char

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
              | parse' ((TDot c)::l) = (EFunc (VDot c), l)
              | parse' ((TVar c)::l) = (EVar (str c), l)
            val (exp, rest) = parse' l
        in
            if (not (null rest)) then raise ParseError "trailing garbage"
            else exp
        end

    local
        fun depends x e =
            let
                fun depends' (EFunc _) = false
                  | depends' (EVar x') = x = x'
                  | depends' (ELambda (x', e)) =
                    x <> x' andalso depends' e
                  | depends' (EApp (e1, e2)) =
                    depends' e1 orelse depends' e2
            in depends' e end

        fun kapp e = EApp (EFunc VK, e)
        fun sapp (x, y) = (EApp(EApp(EFunc VS, x), y))

        fun elim x e =
            let
                fun elim' x (EFunc f) = kapp (EFunc f)
                  | elim' x (EVar x') =
                    if x = x' then (EFunc VI) else kapp (EVar x')
                  | elim' x (EApp (e1, e2)) =
                    sapp (elim x e1, elim x e2)
                  | elim' x (ELambda (x', e')) =
                    elim x (elim x' e')
            in
                (*if depends x e then elim' x e else kapp e*)
                elim' x e
            end

        val fconv =
            (fn VK => U.VK | VS => U.VS | VI => U.VI | VV => U.VV
              | VC => U.VC | VD => U.VD | (VDot c) => (U.VDot c))
    in
    fun convert (EApp (e1, e2)) = (U.EApp (convert e1, convert e2))
      | convert (ELambda (x, e)) = convert (elim x e)
      | convert (EFunc f) = (U.EFunc (fconv f))
      | convert (EVar s) = raise Fail ("variable: " ^ s)
    end

    val load = (parse o lex o explode)
    val transform = (convert o load)
    val stransform = (U.unparse o transform)
    val exec = (UnlambdaInterp.eval o transform)
end
