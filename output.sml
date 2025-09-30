structure Output =
struct
    exception Done

    fun putc c = print (str c)
    fun puts f s = List.app f (explode s)

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

    fun captured_output max_opt =
        let
            val out = ref []
            val lines = ref 0
            fun get () = implode (rev (!out))
            fun putc c = (
                out := c :: (!out);
                if c = #"\n" then lines := (!lines) + 1 else ();
                (case max_opt of
                     NONE => ()
                   | SOME max => if (!lines) >= max then raise Done else ())
            )
        in (get, putc) end

    fun captured_int_output max_opt =
        let
            val (get, putc) = captured_output max_opt
        in (get, int_output putc) end

end
