structure UnlambdaSelfify =
struct
    structure CC = SMLofNJ.Cont

    structure U = Unlambda

    datatype F = F of unit -> F -> F
    fun unF (F x) = x
    fun ap (x, y) = F (fn () => unF ((unF x) () y) ())
    infix $$
    val (op $$) = ap

    fun go (F x) = let val x' = x () in F (fn () => x') end
    fun G f = F (fn () => fn x => f (go x))

    (* Direct implementations of unlambda stuff *)
    val ul_I = G (fn x => x)
    val ul_K = G (fn x => G (fn _ => x))
    val ul_S = G (fn x => G (fn y => G (fn z => (x $$ z) $$ (y $$ z))))
    fun ul_V' _ = G (ul_V')
    val ul_V = G (ul_V')
    fun ul_Dot c = G (fn x => (U.putc c; x))
    val ul_C = G (
            fn x =>
               CC.callcc (fn k => x $$ G (fn y => CC.throw k y)))
    val ul_D = F (fn () => fn x => F (fn () => fn y => x $$ y))



    (* An unlambda "compiler" *)
    (* We could also output source code instead of just
     * constructing the objects, which I leave as a simple exercise for the reader. *)
    fun selfify_value v = (
        case v of
           U.VI => ul_I
         | U.VK => ul_K
         | U.VS => ul_S
         | U.VV => ul_V
         | U.VDot c => ul_Dot c
         | U.VC => ul_C
         | U.VD => ul_D
         | _ => raise Fail "internal representation")
    fun selfify (U.EApp (x, y)) = (selfify x) $$ (selfify y)
      | selfify (U.EFunc f) = selfify_value f

    val exec = ignore o go o selfify o U.load
end
