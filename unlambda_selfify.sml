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


structure UnlambdaSelfify2 =
struct
    structure CC = SMLofNJ.Cont

    structure U = Unlambda

    datatype bot = Bot of bot
    fun abort (Bot x) = abort x
    type 'a cont = 'a -> bot

    fun delay (f : unit -> 'a) (k : 'a cont) = k (f ())
    fun return x = delay (fn () => x)
    fun bind (x: 'a cont cont) (f : 'a -> 'b cont cont) : 'b cont cont =
        fn k: 'b cont => x (fn vx => f vx k)
    fun triple_neg (x: 'a cont cont cont) : 'a cont = fn a => x (return a)

    datatype F = F of (F * F cont) cont cont cont
    fun unF (F x) = x
    fun ap (F x, y) = F (
            bind x (
                fn kx: (F * F cont) cont =>
                   fn k': (F * F cont) cont cont =>
                      kx (y, fn (F z) => return k' z)
            )
        )
    infix $$
    val (op $$) = ap

    (* This is really bad. *)
    fun go (F x) =
        let exception E of F
        in (x (fn k: (F * F cont) cont => raise E (F (return k))); raise Fail "")
           handle E a => a
        end

                     (*
    fun G f = F (delay (fn () => fn (x, k): (F * F cont) => k (f (go x))))
                     *)

    fun G f = F (fn k: (F * F cont) cont cont =>
                    k (fn (x, k') => k' (f (go x))))

(*            delay (fn () => fn (x, k): (F * F cont) => k (f (go x))))                *)
    (* Direct implementations of unlambda stuff *)
    val ul_I = G (fn x => x)
    val ul_K = G (fn x => G (fn _ => x))
    val ul_S = G (fn x => G (fn y => G (fn z => (x $$ z) $$ (y $$ z))))
    fun ul_V' _ = G (ul_V')
    val ul_V = G (ul_V')
    fun ul_Dot c = G (fn x => (U.putc c; x))
(*
    val ul_C = G (
            fn x =>
               CC.callcc (fn k => x $$ G (fn y => CC.throw k y)))
    val ul_D = F (fn () => fn x => F (fn () => fn y => x $$ y))

*)

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
(*
         | U.VC => ul_C
         | U.VD => ul_D
*)
         | _ => raise Fail "internal representation")
    fun selfify (U.EApp (x, y)) = (selfify x) $$ (selfify y)
      | selfify (U.EFunc f) = selfify_value f

    fun run (F x) =
        let exception Done
        in abort (x (fn _ => raise Done))
           handle Done => ()
        end

    val exec = run o selfify o U.load

end
