structure Lambda =
struct
    exception LexError
    exception ParseError of string

    structure U = Unlambda
    structure UY = Unlambdaify

    type ident = string
                            
    datatype token = TLambda | TVar of char | TLParen | TRParen
                   | TK | TS | TI | TV | TC | TD | TDot of char
             


end
