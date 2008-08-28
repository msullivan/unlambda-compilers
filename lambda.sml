structure Lambda =
struct
    exception LexError
    exception ParseError of string

    structure U = Unlambda
    structure UY = Unlambdaify

    type ident = string

    type expr = UY.expr
                            
    datatype token = TLambda | TLParen | TRParen | TDot | TVar of char

    fun lex nil = nil
      | lex (#"^"::s) = TLambda::(lex s)
      | lex (#"("::s) = TLParen::(lex s)
      | lex (#")"::s) = TRParen::(lex s)
      | lex (#"."::s) = TDot::(lex s)
      | lex (c::s) = (TVar c)::(lex s)

    fun parse l =
        let
            fun str c = implode [c]

            fun getnames TDot::l = (nil, l)
              | getnames ((TVar v)::l) = 
                let val (names, l') = getnames l
                in ((TVar v)::names, l') end
              | getnames _ = raise ParseError "error reading names"

            fun parse' nil = raise ParseError "ran out of input"
              | parse' (TLambda::l) =
                let
                    val (names, l') = getnames l
                    val (e, l'') = parse l'
                in
                    (foldr ELambda e names, l'')
                end
              | parse' (TLParen::l) = 
                (case parse l
                  of (e, (TRParen::l')) => (e, l')
                   | _ => raise ParseError "expected )")
              | parse' (l as ((TVar x)::l')) = raise Fail "hono"


              | parse' _ = raise ParseError "garbage"
            and parseterm (l as (TLParen::_)) = parse' l
              | parseterm 

        in
            if (not (null rest)) then raise ParseError "trailing garbage"
            else exp
        end

end
