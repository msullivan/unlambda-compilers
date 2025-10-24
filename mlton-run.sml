structure Run =
struct
  val () = OS.Process.exit (Main.main_inner (CommandLine.name (), CommandLine.arguments ()))
end
