// #Sireum #Logika

import org.sireum._

// Define the sum of the integer elements contained in a sequence from
// index 'j' on wards by:
@strictpure def sum_rec(a: ISZ[Z], j: Z): Z = {
  if (a.isInBound(j)) {
    a(j) + sum_rec(a, j + 1)
  } else {
    0
  }
}

// Then the sum of all the sequence's elements is:
@strictpure def sum(a: ISZ[Z]): Z = sum_rec(a, 0)

// With the two definitions above we have the sum 'sum' of a sequence
// defined recursively. Applying the equation 'sum(a) = sum_rec(a, 0)'
// in simplification, the recursive function 'sum_rec' can be used
// in invariance proofs in imperative implementations.
// Function 'sum_seq' implements 'sum' as specified by the post-condition
// 'Res == sum(a)'; it is a refinement of 'sum'.
@pure def sum_seq(a: ISZ[Z]): Z = {
  Contract(
    Ensures(Res == sum(a))
  )
  var k: Z = 0
  var s: Z = 0
  while (k < a.size) {
    Invariant(
      Modifies(k, s),
      0 <= k, k <= a.size,
      s + sum_rec(a, k) == sum(a)
    )
    s = s + a (k)
    k = k + 1
  }
  return s
}

// Abstract properties of 'sum' can be proved with the same approach as above
// using while loops with invariants. This corresponds to a proof by induction
// with programmatic means, not need dedicated proof notation.
// Function 'pos_sum' is a theorem about the abstract function 'sum'.
@pure def pos_sum(a: ISZ[Z]): Unit = {
  Contract(
    Requires(All(a.indices)(j => a(j) >= 0)),
    Ensures(sum(a) >= 0)
  )
  var k: Z = 0
  var s: Z = 0
  while (k < a.size) {
    Invariant(
      Modifies(k, s),
      0 <= k, k <= a.size,
      s + sum_rec(a, k) == sum(a),
      s >= 0
    )
    s = s + a(k)
    k = k + 1
  }
}

// The theorem 'pos_sum' about the abstraction 'sum' can be propagated
// to the implementation 'sum_seq' by calling the theorem 'pos_sum' in
// a spec block.
@pure def pos_sum_seq(a: ISZ[Z]): Unit = {
  Contract(
    Requires(All(a.indices)(j => a(j) >= 0)),
    Ensures(sum_seq(a) >= 0)
  )
  Spec {
    pos_sum(a)
  }
}
