// #Sireum #Logika

import org.sireum._

// The maximum of an unsorted sequence is found by traversing the sequence
// and remembering the largest element encountered so far. At least one
// element 'a(0)' is available because of the precondition 'a.size > 0'.
@pure def max_seq(a: ISZ[Z]): Z = {
  Contract(
    Requires(a.size > 0),
    Ensures(
      Exists(a.indices)(j => a(j) == Res),
      All(a.indices)(j => a(j) <= Res)
    )
  )
  var k: Z = 1
  var m: Z = a(0)
  while (k < a.size) {
    Invariant(
      Modifies(k, m),
      0 <= k, k <= a.size,
      Exists(0 until k)(j => a(j) == m),
      All(0 until k)(j => a(j) <= m)
    )
    if (a(k) > m) {
      m = a(k)
    }
    k = k + 1
  }
  return m
}

// Function 'sorted' is a predicate as specified in the ensures clause
// as well as an algorithm for checking that a sequence is sorted in
// ascending order. It is suitable for use in formulas and proofs
// referring to the ensures clause and can be called at runtime to check
// the condition.
@pure def sorted(a: ISZ[Z]): B = {
  Contract(
    Ensures(Res == All(1 until a.size)(i => a(i-1) <= a(i)))
  )
  var res: B = true
  var k: Z = 1
  while (k < a.size) {
    Invariant(
      Modifies(k, res),
      k >= 1,
      k-1 <= a.size,
      a.size <= 1 ___>: res == All(1 until a.size)(i => a(i-1) <= a(i)),
      a.size > 1 ___>: k <= a.size,
      a.size > 1 ___>: res == All(1 until k)(i => a(i-1) <= a(i))
    )
    if (a(k - 1) > a(k)) {
      res = false
    }
    k = k + 1
  }
  return res
}

// If it is known that a sequence is sorted in ascending order, the
// maximum of the sequence is found in its last element. Function
// 'max_sorted_seq' implements this with the trivial body
// 'return a(a.lastIndex)'. The algorithm in the spec block preceding
// the return statement confirms that 'a(a.lastIndex)' is the largest
// element contained in the sequence. It is a programmatic proof of
// this fact. The user does not involve the proof notation of Slang
// at all.
@pure def max_sorted_seq(a: ISZ[Z]): Z = {
  Contract(
    Requires(
      a.size > 0,
      sorted(a)
    ),
    Ensures(
      Exists(a.indices)(j => a(j) == Res),
      All(a.indices)(j => a(j) <= Res)
    )
  )
  Spec {
    var k: Z = 1
    var v: Z = a(0)
    while (k < a.size) {
      Invariant(
        Modifies(k, v),
        0 < k, k <= a.size,
        v == a(k - 1),
        All(0 until k)(j => a(j) <= v)
      )
      v = a(k)
      k = k + 1
    }
  }
  return a(a.lastIndex)
}
