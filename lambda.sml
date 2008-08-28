structure Lambda =
struct
    structure LambdaLrVals =
    LambdaLrValsFun(structure Token = LrParser.Token)

    structure LambdaLex =
    LambdaLexFun(structure Tokens = LambdaLrVals.Tokens);

    structure LambdaParser =
    Join(structure LrParser = LrParser
    structure ParserData = LambdaLrVals.ParserData
    structure Lex = LambdaLex)

    (* what the fuck annoying *)
    fun str_once s =
        let
            val foo = ref s
            fun strdiq' _ =
                let
                    val s' = !foo
                    val () =  foo := ""
                in
                    s'
                end
        in
            strdiq'
        end

    fun parse s =
        let
            val stream = LambdaParser.makeLexer(str_once s)
            fun print_error (s,i:int,_) =
                TextIO.output(TextIO.stdOut,
                              "Error, line " ^ 
                              (Int.toString i) ^ ", " ^ s ^ "\n")
            val (res, _) = LambdaParser.parse(0,stream,print_error,())
        in 
            res
        end

end
