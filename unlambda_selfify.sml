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
           (* | U.VD => L.EFunc L.VD *)
           (* XXX: do we need either of these? must explain why *)
           (* if VDot isn't expanded, we print backward??? *)
           (* | (U.VDot c) => `(x, (L.EFunc (L.VDot c) $$ %x)) *)
           (* | (U.VC) => `(x, L.EFunc L.VC $$ %x) *)
           | v => L.EFunc v
        )
    fun expand_unlambda (U.EApp (e1, e2)) =
        L.EApp (expand_unlambda e1, expand_unlambda e2)
      | expand_unlambda (U.EFunc v) = expand_unlambda_value v

    (* HACK: capital letters are placeholders not variables *)
    fun is_placeholder x = x >= "A" andalso x < "["

    (* val unit = EFunc VI *)
    val unit = `(x', %x')

    local
        open L
        fun go e = `(x', `(u_, %x')) $$ (e $$ unit)
        (* fun go e = (EFunc VK) $$ (e $$ unit) *)
        val (dx, dy) = ("d", "e")
    in

    fun delay (EVar k) = EVar k
      | delay (EApp (e1, e2)) =
        `(u_, delay e1 $$ unit $$ delay e2 $$ unit)

      | delay (ELambda (x, e)) =
        `(u_, `(dy, `(x, delay e) $$ (go (%dy)) ))

      | delay (EFunc VD) =
        `(u_, `(dx, `(u_, `(dy, `(u_,
                                  `(dy, %dx $$ unit $$ %dy $$ unit)
                                   $$ go (%dy)
         )))))
      (* XXX: is this needed? oh, probably, since we need to delay the cont *)
      | delay (EFunc VC) =
        `(u_, `(x, L.EFunc L.VC $$ `(y, %x $$ unit $$ `(u_, %y))))

      (* Note that we need to force the RHS *)
      (* We could also have accomplished this by eta-expanding in expand_unlambda *)
      | delay (e as (EFunc (VDot _))) = `(u_, `(dy, e $$ (go (%dy))))

      | delay e = raise Fail ("unexpanded combinator " ^ L.unparse e)

    fun delay_program e = delay e $$ unit
    end

    val (delayt, delayt_program) = (delay, delay_program)

    (* CASE BASED! *)
    local
        open L
        val (dx, dy, l, r) = ("d", "e", "l", "r")

        fun inl e = `(l, `(r, %l $$ e))
        fun inr e = `(l, `(r, %r $$ e))
        fun let_ x v body = `(x, body) $$ v
        (* fun go e = (EFunc VK) $$ (e $$ unit) *)

        fun unF e v = e $$ `(dx, %dx $$ v) $$ `(u_, v)

    in

    fun delayc (EVar k) = EVar k
      (* if the RHS is a variable, then delay means nothing *)
      | delayc (EApp (e1 as EVar _, e2 as EVar x)) =
        if is_placeholder x then eapp e1 e2
        else unF (delayc e1) e2

      | delayc (EApp (e1, e2)) = eapp e1 e2


      | delayc (ELambda (x, e)) =
        inl (`(x, delayc e))

      | delayc (EFunc VD) = inr unit

      (* XXX: is this needed? oh, probably, since we need to delayc the cont *)
      | delayc (EFunc VC) =
        inl (`(x, L.EFunc L.VC $$ `(y, unF (%x) (inl (%y)))))

      | delayc (e as (EFunc (VDot _))) = inl e

      | delayc e = raise Fail ("unexpanded combinator " ^ L.unparse e)

    and eapp e1 e2 =
        let_
            dx
            (`(u_, delayc e2))
            (
              (delayc e1)
                  $$ `(x, %x $$ (%dx $$ unit))
                  $$ `(u_, inl (`(y, unF (%dx $$ unit) (%y))))
            )

    fun delayc_program e = delayc e
    end

    (* XXX: functorize or something -- need to test both!! *)
    (* val delay = delayc *)
    (* val delay_program = delayc_program *)


    local
        open L
        val S = EFunc VS
        val K = EFunc VK
        val I = EFunc VI
        fun iterate 0 _ x = []
          | iterate n f x = x :: iterate (n-1) f (f x)
    in
    fun cons x xs = S $$ (S $$ I $$ (K $$ x)) $$ (K $$ xs)
    fun churchIncrement c = S $$ (S $$ (K $$ S) $$ K) $$ c

    (* TODO: we could have a table of more compact numerals *)
    val churchNumeralTable = Vector.fromList (iterate 257 churchIncrement (K $$ I))

    end

    local
        open L

        val (dx, dy, df, du) = ("dx", "dy", "df", "du")
        val k = "k"

        fun return e = `(k, %k $$ e)
        fun bind action f =
            `(k, action $$ `(du, f $$ %du $$ %k))
    in

    fun cps_convert' is_lazyk e =
        let
            fun cps e =
                (case e of
                     EVar x =>
                     if is_placeholder x then (%x)
                     else return (%x)
                   | ELambda (x, e) => return (`(x, cps e))
                   (* Inline the binds *)
                   | EApp (e1, e2) =>
                     (* bind (cps e1) *)
                     (*      (`(dx, *)
                     (*         bind (cps e2) *)
                     (*              (`(dy, %dx $$ %dy)))) *)
                     (* Inline the binds *)
                     `(k,
                       cps e1 $$
                           (`(dx,
                              cps e2 $$
                                  (`(dy, %dx $$ %dy $$ %k)))))

                   | EFunc (VDot c) =>
                     if is_lazyk then
                         return (`(dy, `(k,
                                         cons
                                             (Vector.sub (churchNumeralTable, ord c))
                                             (%k $$ %dy)
                         )))
                     else
                         return (`(dy, `(k, %k $$ (EFunc (VDot c) $$ %dy))))

                   (* (* We support this one just for its use as unit *) *)
                   (* | EFunc VI => return e *)
                   (* The point of all this *)
                   | EFunc VC =>
                     (* This was my original implementation; it seems wrong
                      * but I can't write a test case that breaks it??? *)
                     (* Actually now I understand why this one works --
                      * the unwrapping is to turn k into a
                      * (term -> cont -> term) function...
                      * So now I don't totally understand why the other one
                      * works... *)
                     return (`(df, `(k, %df $$ `(dy, `(u_, %k $$ %dy)) $$ %k)))

                     (* return (`(df, `(k, %df $$ %k $$ %k))) *)

                   | (e as EFunc _) =>
                     raise Fail ("func unsupported in cps " ^ unparse e)
                )

        in cps e end

    val cps_convert = cps_convert' false

    fun cps_program e = cps_convert e $$ unit
    fun cps_program_lazyk e =
        EFunc VK $$
              (cps_convert' true e $$
                            (* final continuation outputs 256 *)
                            `(u_,
                              cons (Vector.sub (churchNumeralTable, 256)) unit))

    (* fun cps_and_delay e = cps_prefix_app $$ cps_convert (delay e) $$ cps_convert (EFunc VI) $$ EFunc VI *)
    end
end


structure UnlambdaToMicroUnlambda =
struct
local
    structure U = Unlambda
    structure UL = Unlambdaify

    val combs = ["s", "k", "i", "d", "c", "v", "r", ".!"]

    (* val maybe_cps_conv = (fn x => x) *)

    val maybe_cps_conv = LowerUnlambda.cps_convert

    val convert =
        Unlambda.unparse
        (* o Unlambdaify.remove_is  (* do we really want this?? *) *)
        o Unlambdaify.shrink o Unlambdaify.convert
    val delay = maybe_cps_conv o LowerUnlambda.delay
        o LowerUnlambda.expand_unlambda
    val load_and_convert = convert o delay o Unlambda.load

    (* Apply a placeholder to another one, then bind them with lambdas
     * and convert it *)
    fun make_app_prefix_str f =
        let val expr = f (UL.EApp (UL.EVar "N", UL.EVar "M"))
            val s = convert (UL.ELambda ("N", UL.ELambda ("M", expr)))
        in "``" ^ s end

    val prefix_app_str =
        make_app_prefix_str (maybe_cps_conv o LowerUnlambda.delay )

    val cps_prefix_app = make_app_prefix_str LowerUnlambda.cps_convert
    val vi_cps = convert (LowerUnlambda.cps_convert LowerUnlambda.unit)

    (* when using delayt, the result is usually "Inl f", which can tolerate
     * the extra `i` we apply to it via vi_cps *)
    (* val (prefix, suffix) = ("`", "i") *)
    val (prefix, suffix) = ("`" ^ cps_prefix_app, vi_cps ^ "i")

    fun get [] x = raise Fail ("missing: " ^ x)
      | get ((k:string, v)::xs) k' =
        if k = k' then v else get xs k'
in

val compiled =
    ("`", prefix_app_str) ::
    map (fn c => (c, load_and_convert c)) combs

fun print_table' f table =
    List.app
        (fn (c, s) => if c = "r" then () else print (c ^ "\t" ^ f s ^ "\n"))
        table
fun print_size_table () = print_table' (Int.toString o String.size) compiled
fun print_translation_table () = print_table' (fn x => x) compiled


fun skip_line nil = nil
  | skip_line (#"\n"::s) = s
  | skip_line (_::s) = skip_line s

fun translate' [] = []
  (* Annoying lexing stuff *)
  | translate' (#" "::xs) = translate' xs
  | translate' (#"\t"::xs) = translate' xs
  | translate' (#"\n"::xs) = translate' xs
  | translate' (#"#"::xs) = translate' (skip_line xs)

  (* .<X> - use .!, and replace any !s with <X> *)
  | translate' (#"."::c::xs) =
    String.translate (
        fn c' => if c' = #"!" then str c else str c') (get compiled ".!")
    :: translate' xs
  (* Main case - just lookup the combinator *)
  | translate' (c::xs) = get compiled (str c) :: translate' xs

fun translate s =
    prefix ^ String.concat (translate' (explode s)) ^ suffix

end
end
