functor UnlambdaSelfifier(R : UNLAMBDA_REPR) =
struct
local
    open R
    structure U = Unlambda
in
    (* An unlambda "compiler" *)
    (* We could also output source code instead of just
     * constructing the objects, which we do below *)
    fun selfify_value out v = (
        case v of
           U.VI => ul_I
         | U.VK => ul_K
         | U.VS => ul_S
         | U.VV => ul_V
         | U.VDot c => ul_Dot out c
         | U.VC => ul_C
         | U.VD => ul_D)
    fun selfify out (U.EApp (x, y)) = ap (selfify out x, selfify out y)
      | selfify out (U.EFunc f) = func (selfify_value out f)

    fun eval_with_output c out = run (selfify out c)
    fun eval c = eval_with_output c (Output.int_output Output.putc)
end
end

structure UnlambdaToSMLCompiler =
struct
local
    structure U = Unlambda
in
    (* An unlambda compiler that outputs SML source *)
    fun compile_func v = (
        case v of
           U.VI => "I"
         | U.VK => "K"
         | U.VS => "S"
         | U.VV => "V"
         | U.VDot c => "Dot Output.putc #\"" ^ Char.toString c ^ "\""
         | U.VC => "C"
         | U.VD => "D")
    fun compile' (U.EApp (x, y)) = "ap (" ^ compile' x ^ ", " ^ compile' y ^ ")"
      | compile' (U.EFunc f) = "func (" ^ "ul_" ^ compile_func f ^ ")"

    fun compile impl e = "let open " ^ impl ^ " in run (" ^ compile' e  ^ ") end;\n"

    val compile_delay = compile "UnlambdaDelayRepr"
    val compile_cps = compile "UnlambdaCpsRepr"
    val compile_case = compile "UnlambdaCaseRepr"
end
end

structure UnlambdaToSMLCompilerInlined =
struct
local
    structure U = Unlambda
in
    (* An unlambda compiler that outputs SML source *)
    fun compile_func v = (
        case v of
           U.VI => "I"
         | U.VK => "K"
         | U.VS => "S"
         | U.VV => "V"
         | U.VDot c => "Dot Output.putc #\"" ^ Char.toString c ^ "\""
         | U.VC => "C"
         | U.VD => "D")

    (* fun apv v1 e2 = *)
    (*     (case v1 of *)
    (*          F f1 => f1 (e2 ()) *)
    (*        | Delay => F (fn v => unF (e2 ()) v)) *)

    (* todo: there is an optimization available *)

    fun compile' (U.EApp (x, y)) =
        "let val f = (fn () => " ^ compile' y ^ ") in " ^
        "(case " ^ compile' x ^ " of " ^
        "F g => g (f ()) | Delay => F (fn v => unF (f ()) v)) end"
      | compile' (U.EFunc f) = "ul_" ^ compile_func f

    fun compile impl e = "let open " ^ impl ^ " in (" ^ compile' e  ^ ") end;\n"

    val compile_case = compile "UnlambdaCaseReprRaw"
end
end


structure UnlambdaDelay = UnlambdaSelfifier(UnlambdaDelayRepr)
structure UnlambdaCps = UnlambdaSelfifier(UnlambdaCpsRepr)
structure UnlambdaCase = UnlambdaSelfifier(UnlambdaCaseRepr)
