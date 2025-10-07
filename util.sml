structure Util =
struct
  fun readFile name =
      let val f = TextIO.openIn name
          val s = TextIO.inputAll f
          val _ = TextIO.closeIn f
      in s end
end
