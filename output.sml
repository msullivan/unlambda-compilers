structure Output =
struct
    val count = ref true

    fun real_putc c = print (implode [c])

    local
        val cnt = ref 0
    in
    fun peek () = !cnt
    fun reset () = cnt := 0
    fun count_putc c =
        if c = #"\n" then
            (print ((Int.toString (!cnt)) ^ "\n"); cnt := 0)
        else
            cnt := (!cnt + 1)
    end

    fun putc c = if !count then count_putc c else real_putc c
end
