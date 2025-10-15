signature UNLAMBDA_REPR =
  sig
    type V
    type F
    val func : V -> F
    val ap : F * F -> F
    val ul_I : V
    val ul_K : V
    val ul_S : V
    val ul_V : V
    val ul_Dot : (char -> unit) -> char -> V
    val ul_C : V
    val ul_D : V

    val run : F -> unit
  end

structure UnlambdaCaseReprRaw =
struct
    structure CC = Cont


    datatype V = F of V -> V
               | Delay
    type F = unit -> V

    fun unF (F f) z = f z
      | unF Delay z = z

    fun apv v1 e2 =
        (case v1 of
             F f1 => f1 (e2 ())
           | Delay => F (fn v => unF (e2 ()) v))

    fun func v () = v
    fun ap (e1, e2) () = apv (e1 ()) e2

    infix $$
    val (op $$) = ap

    (* Direct implementations of unlambda stuff *)
    val ul_I = F (fn x => x)
    val ul_K = F (fn x => F (fn _ => x))
    (* can optimize two of the applications; well one at least. *)
    val ul_S = F (fn x => F (fn y => F (fn z => apv (unF x z) (fn () => unF y z))))
    fun ul_V' _ = F (ul_V')
    val ul_V = F (ul_V')
    fun ul_Dot out c = F (fn x => (out c; x))
    val ul_C = F (
            fn x =>
               CC.callcc (fn k => unF x (F (fn y => CC.throw k y))))
    val ul_D = Delay

    fun run e = ignore (e ())
end
structure UnlambdaCaseRepr : UNLAMBDA_REPR = UnlambdaCaseReprRaw



structure UnlambdaDelayRepr : UNLAMBDA_REPR =
struct
    structure CC = Cont

    datatype F = F of unit -> F -> F

    type V = F
    fun func x = x

    fun unF (F x) = x
    fun ap (x, y) = F (fn () => unF ((unF x) () y) ())
    infix $$
    val (op $$) = ap

    fun go (F x) = let val x' = x () in F (fn () => x') end

    fun go (F x) = (fn x' => F (fn () => x')) (x ())
    fun G f = F (fn () => fn x => f (go x))

    (* Direct implementations of unlambda stuff *)
    val ul_I = G (fn x => x)
    val ul_K = G (fn x => G (fn _ => x))
    val ul_S = G (fn x => G (fn y => G (fn z => (x $$ z) $$ (y $$ z))))
    fun ul_V' _ = G (ul_V')
    val ul_V = G (ul_V')
    fun ul_Dot out c = G (fn x => (out c; x))
    val ul_C = G (
            fn x =>
               CC.callcc (fn k => x $$ G (fn y => CC.throw k y)))
    val ul_D = F (fn () => fn x => F (fn () => fn y => x $$ (go y)))

    val run = ignore o go
end


structure UnlambdaCpsRepr : UNLAMBDA_REPR =
struct
    datatype bot = Bot of bot
    fun abort (Bot x) = abort x
    type 'a cont = 'a -> bot

    fun return x = fn k: 'a cont => k x
    fun bind (x: 'a cont cont) (f : 'a -> 'b cont cont) : 'b cont cont =
        fn k: 'b cont => x (fn vx => f vx k)

    (* Fun fact: the CPS equivalent of `unit -> A` is `A cont cont` *)
    (* |A -> B| = (|A| * |B| cont) cont *)
    (* |unit -> A| = (unit * |A| cont) cont, at which point we drop the unit *)
    datatype F = F of (F * F cont) cont cont cont

    type V = F
    fun func x = x

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
        F (return (fn (x, k''): (F * F cont) => go x (fn xv => f (xv, k''))))


    (* Direct implementations of unlambda stuff *)
    val ul_I = G (fn (x, k) => k x)
    val ul_K = G (fn (x, k) => k (G (fn (_, k') => k' x)))
    val ul_S = G (fn (x, k) =>
                     k (G (fn (y, k') =>
                              k' (G (fn (z, k'') => k'' ((x $$ z) $$ (y $$ z)))))))

    fun ul_V' (_, k') = k' (G (ul_V'))
    val ul_V = G (ul_V')
    fun ul_Dot out c = G (fn (x, k) => (out c; k x))
    val ul_C = F (return
            (fn (x, k) =>
                k (x $$ F (return (fn (y, _) => k y)))))


    val ul_D = F (return (fn (x, k) =>
                             k (F (return (fn (y, k') =>
                                              go y (fn y' => k' (x $$ y')))))))

    fun run (F x) =
        let exception Done
        in abort (x (fn _ => raise Done))
           handle Done => ()
        end
end;
