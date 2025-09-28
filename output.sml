structure Output =
struct
    fun putc c = print (str c)
    fun puts f s = List.app putc (explode s)

    fun int_output putc =
        let
            val cnt = ref 0
        in
            fn c =>
               if c = #"\n" andalso !cnt > 0 then
                   (puts putc((Int.toString (!cnt)) ^ "\n"); cnt := 0)
               else if c = #"*" then
                   cnt := (!cnt + 1)
               else
                   putc c
        end

end
