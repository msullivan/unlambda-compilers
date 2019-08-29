structure Unlambda =
struct
    exception LexError
    exception ParseError of string

    datatype token = TApp | TK | TS | TI | TV | TC | TD |
             TDot of char

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
      | lex (#"."::c::s) = (TDot c)::(lex s)
      | lex (#"r"::s) = (TDot #"\n")::(lex s)
      | lex (#" "::s) = lex s
      | lex (#"\t"::s) = lex s
      | lex (#"\n"::s) = lex s
      | lex (#"#"::s) = lex (skip_line s)
      | lex (_::s) = raise LexError

    datatype expr = EApp of (expr * expr) | EFunc of value
         and value = VK | VS | VI | VV | VC | VD | VDot of char

    fun unparse (EApp (e1, e2)) = "`" ^ (unparse e1) ^ (unparse e2)
      | unparse (EFunc f) =
        (case f
          of VK => "k" | VS => "s" | VI => "i" | VV => "v" | VC => "c"
           | VD => "d" | VDot #"\n" => "r"
           | VDot c => (implode [#".", c])
        )

    fun parse l =
        let
            fun parse' nil = raise ParseError "ran out of input"
              | parse' (TApp::l) =
                let
                    val (e1, l') = parse' l
                    val (e2, l'') = parse' l'
                in
                    (EApp (e1, e2), l'')
                end
              | parse' (TK::l) = (EFunc VK, l)
              | parse' (TS::l) = (EFunc VS, l)
              | parse' (TI::l) = (EFunc VI, l)
              | parse' (TV::l) = (EFunc VV, l)
              | parse' (TC::l) = (EFunc VC, l)
              | parse' (TD::l) = (EFunc VD, l)
              | parse' ((TDot c)::l) = (EFunc (VDot c), l)

            val (exp, rest) = parse' l
        in
            if (not (null rest)) then raise ParseError "trailing garbage"
            else exp
        end

    val load = (parse o lex o explode)
end

structure UnlambdaInterp =
struct
    structure U = Unlambda
    structure CC = SMLofNJ.Cont


    datatype expr = EApp of (expr * expr) | EFunc of value
         and value = VK | VK1 of value | VS | VS1 of value
                   | VS2 of (value * value) | VI | VV
                   | VC | VCont of (value CC.cont) | VD | VPromise of expr
                   | VDot of char

    fun convert_value v = (
        case v of
            U.VK => VK | U.VS => VS | U.VI => VI | U.VV => VV
          | U.VC => VC | U.VD => VD | U.VDot c => VDot c)
    fun convert (U.EApp (e1, e2)) = EApp (convert e1, convert e2)
      | convert (U.EFunc v) = EFunc (convert_value v)

    fun eval (EApp (e1, e2)) =
        let
            val v1 = eval e1
        in
            case v1 of VD => (VPromise e2)
                     | _ => (apply (v1, eval e2))
        end
      | eval (EFunc f) = f
    and apply (VK, x) = VK1 x
      | apply (VK1 x, y) = x
      | apply (VS, x) = VS1 x
      | apply (VS1 x, y) = VS2 (x, y)
      | apply (VS2 (x, y), z) =
        apply(apply(x, z), apply(y, z))
      | apply (VI, x) = x
      | apply (VV, _) = VV
      | apply (VDot c, x) = (Output.putc c; x)
      | apply (VC, x) =
        CC.callcc (fn cont => apply (x, VCont cont))
      | apply (VCont cont, x) = CC.throw cont x
      | apply (VD, x) = VPromise (EFunc x)
      | apply (VPromise eg, h) = (apply (eval eg, h))


    val eval' = eval
    fun eval e = (Output.reset();
                  eval' (convert e))
    val exec = eval o Unlambda.load
end
