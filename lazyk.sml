signature LAZY =
sig
  type 'a susp
  val force : 'a susp -> 'a
  val delay : (unit -> 'a) -> 'a susp
  val no_delay : 'a -> 'a susp
end

structure LazyThunk :> LAZY =
struct
  type 'a susp = (unit -> 'a) ref
  fun force (ref f) = f ()
  fun no_delay x = ref (fn () => x)

  fun delay f =
      let val r = ref (fn () => raise Fail "hono")
          fun thunk () =
              let val x = f ()
                  val () = r := (fn () => x)
              in x end
          val () = r := thunk
      in r end
end

(* I've always wondered if the self-updating thing was actually faster...
 * It is here, at least! *)
structure LazyTag :> LAZY =
struct
  datatype 'a body = Val of 'a | Susp of (unit -> 'a)
  type 'a susp = 'a body ref

  fun force (ref (Val x)) = x
    | force (r as ref (Susp f)) =
      let val v = f ()
          val () = r := Val v
      in v end
  fun no_delay x = ref (Val x)

  fun delay f = ref (Susp f)
end

structure LazyK =
struct
  structure T = LazyThunk

  val % = T.delay
  val %% = T.no_delay

  datatype comb' = Func of comb -> comb
                 | Num of int
  withtype comb = comb' T.susp

  infix $$
  fun f $$ g = % (
          fn () =>
             case T.force f of
                 Func f' => T.force (f' g)
               | _ => raise Fail "Num on LHS of app"
      )
  fun getNum f = (
      case T.force f of
          Num n => n
        | _ => raise Fail "Func when Num expected"
  )

  (* Implementation of the combinators *)
  val I : comb = % (fn () => Func (fn x => x))
  val K : comb = % (fn () => Func (
                             fn x => % (fn () => Func (fn _ => x))))
  val S : comb = % (fn () => Func (fn x =>
                  % (fn () => Func (fn y =>
                   % (fn () => Func (fn z =>
                                        (x $$ z) $$ (y $$ z)))))))
  (* The hacky bullshit combinator - used to extract useful numbers from church numerals *)
  val inc : comb = % (fn () => Func (fn x =>
                    % (fn () => Num (getNum x + 1))))
  val zero : comb = % (fn () => Num 0)


  (* Useful functions for constructing and destructing combinators *)
  fun car e = e $$ K
  fun cdr e = e $$ (K $$ I)
  fun cons x xs = S $$ (S $$ I $$ (K $$ x)) $$ (K $$ xs)

  fun churchIncrement c = S $$ (S $$ (K $$ S) $$ K) $$ c
  fun fromChurchNumeral c = getNum (c $$ inc $$ zero)

  fun iterate 0 _ x = []
    | iterate n f x = x :: iterate (n-1) f (f x)

  val churchNumeralTable = Vector.fromList (iterate 257 churchIncrement (K $$ I))
  fun getChurchNumeral n =
      if n < 0 orelse n > 256 then Vector.sub (churchNumeralTable, 256)
      else Vector.sub (churchNumeralTable, n)

  fun readChar () =
    case TextIO.input1 TextIO.stdIn of
        SOME char => ord char
      | NONE => 256

  fun inputStream' getc =
      % (
          fn () =>
             let val c = getc ()
             in T.force (cons (getChurchNumeral c) (inputStream' getc)) end
      )

  fun runComb' e putc =
      let
          val hd = fromChurchNumeral (car e)
          (* val _ = print ("!! " ^ Int.toString hd ^"\n") *)
      in
          if hd < 256 then (putc (chr hd); runComb' (cdr e) putc)
          else hd - 256
      end
  fun runComb e getc putc = runComb' (e $$ inputStream' getc) putc
  fun runCombNoInput e = runComb e (fn () => 256)

  (* parser *)
  datatype expr = EI | EK | ES | EApp of expr * expr

  fun convExp (EApp (e1, e2)) = (convExp e1) $$ (convExp e2)
    | convExp ES = S
    | convExp EK = K
    | convExp EI = I

  fun parseExp' (#"`"::r0) =
      let val (e1, r1) = parseExp' r0
          val (e2, r2) = parseExp' r1
      in (EApp (e1, e2), r2) end
    | parseExp' (#"s"::r) = (ES, r)
    | parseExp' (#"i"::r) = (EI, r)
    | parseExp' (#"k"::r) = (EK, r)
    | parseExp' _ = raise Fail "parse error"

  fun parseExp s =
      case parseExp' (List.filter (fn c => c <> #" " andalso c <> #"\n") (explode s))
       of (c, []) => c
        | (c, gunk) => raise Fail ("parse error - trailing gunk: '" ^ implode gunk ^ "'")


  fun parseFile name =
      let val f = TextIO.openIn name
          val s = TextIO.inputAll f
          val _ = TextIO.closeIn f
      in parseExp s end

  fun runFile s =
      let val c = convExp (parseFile s)
      in runComb c readChar Output.putc end

end
