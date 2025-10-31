structure Unlambda =
struct
    exception LexError of string
    exception ParseError of string

    datatype token = TApp | TK | TS | TI | TV | TC | TD | TE | TAt | TPipe |
             TDot of char | TQuest of char

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
      | lex (#"\t"::s) = lex s
      | lex (#"\n"::s) = lex s
      | lex (#"#"::s) = lex (skip_line s)
      | lex (c::s) = (print ("asdf: " ^ str c ^ "\n"); raise (LexError (str c)))

    datatype expr = EApp of (expr * expr) | EFunc of value
         and value = VK | VS | VI | VV | VC | VD | VE | VAt | VPipe | VDot of char | VQuest of char

    fun unparse (EApp (e1, e2)) = "`" ^ (unparse e1) ^ (unparse e2)
      | unparse (EFunc f) =
        (case f
          of VK => "k" | VS => "s" | VI => "i" | VV => "v" | VC => "c"
             | VD => "d" | VE => "e" | VAt => "@" | VPipe => "|"
             | VDot #"\n" => "r"
             | VQuest c => (implode [#"?", c])
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
              | parse' (TE::l) = (EFunc VE, l)
              | parse' (TAt::l) = (EFunc VAt, l)
              | parse' (TPipe::l) = (EFunc VPipe, l)
              | parse' ((TDot c)::l) = (EFunc (VDot c), l)
              | parse' ((TQuest c)::l) = (EFunc (VQuest c), l)

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
    structure CC = Cont


    datatype expr = EApp of (expr * expr) | EFunc of value
         and value = VK | VK1 of value | VS | VS1 of value
                   | VS2 of (value * value) | VI | VV
                   | VC | VCont of (value CC.cont) | VD | VPromise of expr
                   | VE | VAt | VPipe | VDot of char | VQuest of char

    exception Done of value

    fun convert_value v = (
        case v of
            U.VK => VK | U.VS => VS | U.VI => VI | U.VV => VV
            | U.VC => VC | U.VD => VD
            | U.VE => VE | U.VAt => VAt | U.VPipe => VPipe
            | U.VDot c => VDot c | U.VQuest c => VQuest c)
    fun convert (U.EApp (e1, e2)) = EApp (convert e1, convert e2)
      | convert (U.EFunc v) = EFunc (convert_value v)

    fun eval out (EApp (e1, e2)) =
        let
            val v1 = eval out e1
        in
            case v1 of VD => (VPromise e2)
                     | _ => (apply out v1 (eval out e2))
        end
      | eval _ (EFunc f) = f
    and apply _ VK x = VK1 x
      | apply _ (VK1 x) y = x
      | apply _ VS x = VS1 x
      | apply _ (VS1 x) y = VS2 (x, y)
      | apply out (VS2 (x, y)) z =
        (* eval out (EApp (EApp (EFunc x, EFunc z), EApp (EFunc y, EFunc z))) *)
        (* Key optimization here: we could *always* construct a full application
         * and hand it back to eval, but that winds up slowing the whole thing down
         * by about 2x. *)
        (case apply out x z of
             f as VD => eval out (EApp (EFunc f, EApp (EFunc y, EFunc z)))
           | f => apply out f (apply out y z)
        )

      | apply _ VI x = x
      | apply _ VV _ = VV
      | apply (_, outp) (VDot c) x = (outp c; x)
      | apply out VC x =
        CC.callcc (fn cont => apply out x (VCont cont))
      | apply _ (VCont cont) x = CC.throw cont x
      | apply _ VD x = VPromise (EFunc x)
      | apply out (VPromise eg) h = (apply out (eval out eg) h)

      | apply _ VE v = raise Done v
      | apply (out as ((pipef, _), _)) VAt v =
        apply out v (if pipef () then VI else VV)
      | apply (out as ((_, cur), _)) VPipe v =
        apply out v (
            case !cur of SOME x => VDot x | NONE => VV
        )
      | apply (out as ((_, cur), _)) (VQuest c) v =
        apply out v (if !cur = SOME c then VI else VV)


    fun eval' out e = eval out e handle Done v => v
    fun eval_with_io e (out : char -> unit) (inp : unit -> char option)
        = eval' (Output.make_io inp, out) (convert e)
    fun eval_with_output e (out : char -> unit) = eval_with_io e out Output.getc
    fun eval e = eval_with_output e (Output.int_output Output.putc)
end
