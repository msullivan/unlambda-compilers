structure Util =
struct
  fun readFile name =
      let val f = TextIO.openIn name
          val s = TextIO.inputAll f
          val _ = TextIO.closeIn f
      in s end

  fun writeFile name data =
      let val f = TextIO.openOut name
          val _ = TextIO.output (f, data)
          val _ = TextIO.closeOut f
      in () end

end
