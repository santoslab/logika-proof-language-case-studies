::/*#! 2> /dev/null                                   #
@ 2>/dev/null # 2>nul & echo off & goto BOF           #
if [ -z "${SIREUM_HOME}" ]; then                      #
  echo "Please set SIREUM_HOME env var"               #
  exit -1                                             #
fi                                                    #
exec "${SIREUM_HOME}/bin/sireum" slang run "$0" "$@"  #
:BOF
setlocal
if not defined SIREUM_HOME (
  echo Please set SIREUM_HOME env var
  exit /B -1
)
"%SIREUM_HOME%\bin\sireum.bat" slang run %0 %*
exit /B %errorlevel%
::!#*/
// #Sireum

import org.sireum._

val home = Os.slashDir.up.canon
val sireumHome = Os.sireumHomeOpt.get
val sireum = sireumHome / "bin" / (if (Os.isWin) "sireum.bat" else "sireum")

println(s"home=$home")
println(s"sireumHome=$sireumHome")
println(s"sireum=$sireum")

Sireum.initRuntimeLibrary()

var ok = T
var passing = 0
var failing = ISZ[Os.Path]()

println(s"exists?=${(home / "src").exists}")

val x = Os.Path.walk(home / "src", F, F, (p: Os.Path) => p.ext == "sc" || p.ext == "logika")

for (file <- Os.Path.walk(home / "src", F, F, (p: Os.Path) => p.ext == "sc" || p.ext == "logika")) {
  val reporter = message.Reporter.create
  println(s"Verifying $file ...")
  reporter.printMessages()
  val results = proc"$sireum logika verifier ${file.string}".echo.console.run()
  println(results.exitCode)
  println(results.out)
  println(results.err)
  /*}
  if (Sireum.runWithReporter(ISZ("logika", "verifier", file.string), reporter)._1 != 0) {
    ok = F
    failing = failing :+ file
  } else {
    passing = passing + 1
  }
  */
  println()
}

println(s"Number of verified examples: $passing")
if (!ok) {
  eprintln(s"Number of erroneous tests: ${failing.size}:")
  for (f <- failing) {
    eprintln(s"* $f")
  }
  Os.exit(-1)
}
