structure Main =
struct

  fun i2 f (x : char -> unit) = ignore (f x)

  (* LOL! there was a bug in unlambda_interp and lambda_interp but not in the compiler ones!! *)
  val unlambda_interp = i2 o UnlambdaInterp.eval_with_output o Unlambda.load
  val lambda_interp = i2 o Unlambdaify.eval_with_output o Unlambdaify.load

  val lambda_cps = i2 o Unlambdaify.eval_with_output o LowerUnlambda.cps_program o LowerUnlambda.delay_program o LowerUnlambda.expand_unlambda o Unlambda.load
  val lambda_delay = i2 o Unlambdaify.eval_with_output o LowerUnlambda.delay_program o LowerUnlambda.expand_unlambda o Unlambda.load
  val lambda_cps_only = i2 o Unlambdaify.eval_with_output o LowerUnlambda.cps_program o LowerUnlambda.expand_unlambda o Unlambda.load
  val micro_unlambda = i2 o UnlambdaInterp.eval_with_output o Unlambda.load o UnlambdaToMicroUnlambda.translate

  val sml_delay = i2 o UnlambdaDelay.eval_with_output o Unlambda.load
  val sml_cps = i2 o UnlambdaCps.eval_with_output o Unlambda.load
  val sml_case = i2 o UnlambdaCase.eval_with_output o Unlambda.load

  val default = unlambda_interp

  fun getMethod args = (
      case args of
          "--interp"::s => (unlambda_interp, s)
        | "--interp-unlambda"::s => (unlambda_interp, s)
        | "--interp-lambda"::s => (lambda_interp, s)
        | "--lambda-cps"::s => (lambda_cps, s)
        | "--lambda-delay"::s => (lambda_delay, s)
        | "--lambda-cps-only"::s => (lambda_cps_only, s)
        | "--micro-unlambda"::s => (lambda_delay, s)
        | "--sml-delay"::s => (sml_delay, s)
        | "--sml-cps"::s => (sml_cps, s)
        | "--sml-case"::s => (sml_case, s)

        | s => (default, s)

  )

  fun parse args =
      let val (func, rest) = getMethod args in
          case rest of [s] => (func, s)
                     | _ => raise Fail "no file specified"
      end

  fun main_inner (name, args) =
      let val (func, file) = parse args
          val contents = Util.readFile file
          val _ = func contents Output.putc
      in OS.Process.success end

  fun main (name, args) =
      main_inner (name, args)
      handle e => (print ("Exception " ^ exnMessage e ^ "\n");
                   OS.Process.failure)


end
