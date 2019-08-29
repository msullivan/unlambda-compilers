structure Output =
struct
    local
        val cnt = ref 0
    in
    fun peek () = !cnt
    fun reset () = cnt := 0
    fun putc c =
        if c = #"\n" andalso !cnt > 0 then
            (print ((Int.toString (!cnt)) ^ "\n"); cnt := 0)
        else if c = #"*" then
            cnt := (!cnt + 1)
        else
            print (implode [c])

    end
end
