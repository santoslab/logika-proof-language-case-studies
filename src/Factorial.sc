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

@pure def fac_base(): Unit = {
  Contract(Ensures(1 == fac(0)))
}

@pure def fac_step(n: Z): Unit = {
  Contract(
    Requires(n > 0),
    Ensures(n * fac(n-1) == fac(n))
  )
}

@pure def fac_nsucc(n: Z): Unit = {
  Contract(
    Requires(n >= 0),
    Ensures((n+1) * fac(n) == fac(n+1))
  )
}

// SHA: I did not succeed to prove this with Auto without the final Rewrite step.
// There was no way (that I could see) how to force this issue in 'fac_it'.
@pure def fac_rev(n: Z): Unit = {
  Contract(
    Requires(n > 0),
    Ensures(fac(n-1) == fac(n) / n)
  )
  fac_step(n) // Apply lemma. Makes 'n * fac(n-1) == fac(n)' available. See step 7.
  Deduce(
    1 (n > 0) by Premise,
    2 Let ((m: Z) => SubProof( // Introduce 'm' so that in step Algebra can be used
      3 Assume(m == fac(n-1)),
      4 ((n * m) / n == m) by Algebra,
      5 ((n * fac(n-1)) / n == fac(n-1)) by Rewrite(RS(), 4) and 3
    )),
    6 ((n * fac(n-1)) / n == fac(n-1)) by Auto and (1, 2), // This is a nat ded step
    7 (n * fac(n-1) == fac(n)) by Premise,
    8 (fac(n) / n== fac(n-1)) by Rewrite(RS(), 6) and 7
  )
}

// Implementation using while loop
// Proof approach:
// 1. Use rewriting (and simplification) as much as possible; it's fast.
// 2. Use SMT on trivial statements, and when there are not too many hypothesis
// 3. Avoid destructive assignments.
//    This make the code a little longer but it's very easy to prove properties
//    using the additionally introduced 'val' variables.
//    (Robby suggested this to deal with a current limitation
//     when using 'At' and 'Old'. But it's actually quite a nice method.
// The proof contains more steps than necessary to demo Logika proof.
@pure def fac_it(n: Z): Z = {
  Contract(
    Requires(n >= 0),
    Ensures(Res == fac(n))
  )
  var x: Z = 1
  var m: Z = 0;
  while (m < n) {
    Invariant(
      Modifies(x, m),
      0 <= m, m <= n,
      x == fac(m)
    )
    Deduce(
      1 (m >= 0) by Algebra,
      2 (x == fac(m)) by Premise,
      3 ((m+1) * x == (m+1) * fac(m)) by Simpl and 2,
      4 ((m+1) * x == fac(m+1)) by Rewrite(RS(fac_nsucc _), 3) and 1
    )
    val mn = m + 1
    Deduce(
      1 (mn > 0) by Auto,
      2 (m + 1 == mn) by Auto,
      3 ((m+1) * x == fac(m+1)) by Premise,
      4 (mn * x == fac(mn)) by Rewrite(RS(), 3) and 2,
      5 (x == fac(mn-1)) by Auto and (1, 4))
    m = mn
    Deduce(
      1 (m == mn) by Premise,
      2 (x == fac(mn-1)) by Premise,
      3 (x == fac(m-1)) by Rewrite(RS(), 2) and 1
    )
    var y: Z = 0
    var k: Z = 0
    while (k < m) {
      Invariant(
        Modifies(y, k),
        0 <= k, k <= m,
        y == k * x
      )
      Deduce(
        1 (y == k * x) by Premise,
        2 (y + x == k * x + x) by Simpl and 1
      )
      val yn = y + x
      Deduce(
        1 (yn == y + x) by Premise,
        2 (y == yn - x) by Algebra and 1,
        3 (y + x == k * x + x) by Premise,
        4 ((yn - x) + x == k * x + x) by Rewrite(RS(), 3) and 2,
        5 (yn == k * x + x) by Algebra and 4,
        6 (yn == (k + 1) * x) by Algebra and 5
      )
      y = yn
      k = k + 1
    }
    Deduce(
      1 (k <= m) by Premise,
      2 (!(k < m)) by Premise,
      3 (k == m) by Algebra and (1, 2),
      4 (y == k * x) by Premise,
      5 (x == fac(m-1)) by Premise,
      6 (y == m * fac(m-1)) by Rewrite(RS(), 4) and (3, 5))
    x = y
    Deduce(
      1 (x == y) by Premise,
      2 (y == m * fac(m-1)) by Premise,
      3 (m > 0) by Auto,
      4 (y == fac(m)) by Rewrite(RS(fac_step _), 2) and 3,
      5 (x == fac(m)) by Simpl and (1, 4))
  }
  Deduce(
    1 (m == n) by Auto,
    2 (x == fac(m)) by Premise,
    3 (x == fac(n)) by Simpl and (1, 2))
  return x
}