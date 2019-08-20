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
    fun ul_Dot c = G (fn x => (Output.putc c; x))
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
    structure U = Unlambda

    datatype bot = Bot of bot
    fun abort (Bot x) = abort x
    type 'a cont = 'a -> bot

    fun delay (f : unit -> 'a) (k : 'a cont) = k (f ())
    fun return x = delay (fn () => x)
    fun bind (x: 'a cont cont) (f : 'a -> 'b cont cont) : 'b cont cont =
        fn k: 'b cont => x (fn vx => f vx k)

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

    fun go (F x) k = x (fn k' => k (F (return k')))
    fun G (f: (F * F cont) cont) : F =
        F (fn k: (F * F cont) cont cont =>
              k (fn (x, k''): (F * F cont) => go x (fn xv => f (xv, k''))))


    (* Direct implementations of unlambda stuff *)
    val ul_I = G (fn (x, k) => k x)
    val ul_K = G (fn (x, k) => k (G (fn (_, k') => k' x)))
    val ul_S = G (fn (x, k) =>
                     k (G (fn (y, k') =>
                              k' (G (fn (z, k'') => k'' ((x $$ z) $$ (y $$ z)))))))

    fun ul_V' (_, k') = k' (G (ul_V'))
    val ul_V = G (ul_V')
    fun ul_Dot c = G (fn (x, k) => (Output.putc c; k x))
    val ul_C = F (return
            (fn (x, k) =>
                k (x $$ F (return (fn (y, _) => k y)))))


    val ul_D = F (return (fn (x, k) =>
                             k (F (return (fn (y, k') => k' (x $$ y))))))


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

    fun run (F x) =
        let exception Done
        in abort (x (fn _ => raise Done))
           handle Done => ()
        end
    val exec = run o selfify o U.load
end
