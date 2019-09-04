signature UNLAMBDA_REPR =
  sig
    type F
    val ap : F * F -> F
    val ul_I : F
    val ul_K : F
    val ul_S : F
    val ul_V : F
    val ul_Dot : char -> F
    val ul_C : F
    val ul_D : F
    val run : F -> unit
  end

structure UnlambdaCallccRepr : UNLAMBDA_REPR =
struct
    structure CC = SMLofNJ.Cont

    structure U = Unlambda

    datatype F = F of unit -> F -> F
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
    fun ul_Dot c = G (fn x => (Output.putc c; x))
    val ul_C = G (
            fn x =>
               CC.callcc (fn k => x $$ G (fn y => CC.throw k y)))
    val ul_D = F (fn () => fn x => F (fn () => fn y => x $$ y))

    val run = ignore o go
end

structure LowerUnlambda =
struct
    structure L = Unlambdaify
    structure U = Unlambda

    val ` = L.ELambda
    infix $$
    val (op $$) = L.EApp
    val % = L.EVar

    val (x, x', y, z, u_) = ("x", "x'", "y", "z", "_")

    fun expand_unlambda_value v =
        (case v of
             U.VI => `(x, %x)
           | U.VK => `(x, `(y, %x))
           | U.VS => `(x, `(y, `(z, (%x $$ %z) $$ (%y $$ %z))))
           | U.VV => let val v = `(x, `(y, %x $$ %x)) in v $$ v end

           (* d is left unexpanded *)
           | U.VD => L.EFunc L.VD
           | (U.VDot c) => `(x, (L.EFunc (L.VDot c) $$ %x))
           | (U.VC) => `(x, L.EFunc L.VC $$ %x)
        )
    fun expand_unlambda (U.EApp (e1, e2)) =
        L.EApp (expand_unlambda e1, expand_unlambda e2)
      | expand_unlambda (U.EFunc v) = expand_unlambda_value v

    local
        open L
        val unit = EFunc VI
        fun go e = `(x', `(u_, %x')) $$ (e $$ unit)
        val (dx, dy) = ("____dx", "____dy")
    in
    fun delay (EVar k) = EVar k
      | delay (EApp (e1, e2)) =
        `(u_, delay e1 $$ unit $$ delay e2 $$ unit)
                              (*
      | delay (EApp (e1, e2)) =
        `(dx, `(dy, `(u_, %dx $$ unit $$ %dy $$ unit))) $$ delay e1 $$ delay e2
                              *)
      | delay (ELambda (x, e)) =
        `(u_, `(dy, `(x, delay e) $$ (go (%dy)) ))
      | delay (EFunc VD) =
        `(u_, `(dx, `(u_, `(dy, `(u_, %dx $$ unit $$ %dy $$ unit)))))
      | delay (EFunc VC) =
        `(u_, `(x, L.EFunc L.VC $$ `(y, %x $$ unit $$ `(u_, %y))))
      | delay (EFunc v) = `(u_, EFunc v)

    fun delay_top e = delay e $$ unit
    end
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

    fun run (F x) =
        let exception Done
        in abort (x (fn _ => raise Done))
           handle Done => ()
        end
end

functor UnlambdaSelfifier(R : UNLAMBDA_REPR) =
struct
local
    open R
    structure U = Unlambda
in
    (* An unlambda "compiler" *)
    (* We could also output source code instead of just
     * constructing the objects, which we do below *)
    fun selfify_value v = (
        case v of
           U.VI => ul_I
         | U.VK => ul_K
         | U.VS => ul_S
         | U.VV => ul_V
         | U.VDot c => ul_Dot c
         | U.VC => ul_C
         | U.VD => ul_D)
    fun selfify (U.EApp (x, y)) = ap (selfify x, selfify y)
      | selfify (U.EFunc f) = selfify_value f

    fun exec count c =
        (Output.reset();
         run (selfify c))
end
end

structure UnlambdaCompiler =
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
         | U.VDot c => "Dot #\"" ^ Char.toString c ^ "\""
         | U.VC => "C"
         | U.VD => "D")
    fun compile' (U.EApp (x, y)) = "ap (" ^ compile' x ^ ", " ^ compile' y ^ ")"
      | compile' (U.EFunc f) = "ul_" ^ compile_func f

    fun compile impl e = "let open " ^ impl ^ " in " ^ compile' e  ^ " end\n"

    val compile_callcc = compile "UnlambdaCallccRepr"
    val compile_cps = compile "UnlambdaCpsRepr"
end
end


structure UnlambdaCallcc = UnlambdaSelfifier(UnlambdaCallccRepr)
structure UnlambdaCps = UnlambdaSelfifier(UnlambdaCpsRepr)
