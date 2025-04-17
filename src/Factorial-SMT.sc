// #Sireum #Logika
import org.sireum._
import org.sireum.justification._

// Definition by cases, equational
// Specification of the factorial function
@abs def fac(n: Z): Z = n match {
  case 0 => 1
  case m if m > 0 => m * fac(m - 1)
  case _ => halt("Negative factorial")
}

// SMT proof of the iterative factorial function
@pure def fac_it(n: Z): Z = {
  Contract(
    Requires(n >= 0),
    Ensures(Res == fac(n))
  )
  var x: Z = 1; var m: Z = 0;
  while (m < n) {
    Invariant(Modifies(x, m),
              0 <= m, m <= n, x == fac(m))
    m = m + 1
    var y: Z = 0; var k: Z = 0
    while (k < m) {
      Invariant(Modifies(y, k),
              0 <= k, k <= m, y == k * x)
      y = y + x; k = k + 1
    }
    x = y
  }
  return x
}