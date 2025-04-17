// #Sireum #Logika

import org.sireum._
import org.sireum.justification._

Deduce(|- (All{ (x: Z) => x + x == x ___>: x == 0}))

Deduce(|- (All(2 until 4)(x => x * x < 10)))

Deduce(|- (Exists{ (x: Z) => x + x == 0 }))

Deduce(|- (Exists(-1 until 1)(x => x * x <= 0)))

val empty: ISZ[Z] = ISZ()  // Empty sequence
val s1: ISZ[Z] = ISZ(1)    // Sequence with only element 1
val s2: ISZ[Z] = ISZ(2)    // Sequence with only element 1
val s3: ISZ[Z] = ISZ(1, 2) // Sequence with element 1 followed by 2
val s4: ISZ[Z] = ISZ(2, 1) // Sequence with element 2 followed by 1
val s5: ISZ[Z] = s1 :+ 2   // Element 2 appended to sequence s1
val s6: ISZ[Z] = 1 +: s2   // Element 1 prepended to sequence s2
val s7: ISZ[Z] = s1 ++ s2  // Sequence s1 concatenated with sequence s2
val s8: ISZ[Z] = s3(0 ~> s3(1), 1 ~> s3(0)) // Sequence with elements at 0 and 1 swapped

val seq: ISZ[Z] = ISZ(1, 2, 3)

Deduce(|- (All(seq.indices)(k => seq(k) < 4)))
Deduce(|- (All(0 until seq.size)(k => seq(k) < 4)))
Deduce(|- (Exists(seq.indices)(k => seq(k) > 2)))
Deduce(|- (Exists(0 until seq.size)(k => seq(k) > 2)))

val emptz: MSZ[Z] = MSZ()
val t1: MSZ[Z] = MSZ(1)
val t2: MSZ[Z] = MSZ(2)
val t3: MSZ[Z] = MSZ(1, 2)
val t4: MSZ[Z] = MSZ(2, 1)
val t5: MSZ[Z] = t1 :+ 2
val t6: MSZ[Z] = 1 +: t2
val t7: MSZ[Z] = t1 ++ t2
val t8: MSZ[Z] = t3(0 ~> t3(1), 1 ~> t3(0))

val mseq: MSZ[Z] = MSZ(1)
mseq(0) = 0

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

@strictpure def sum_rec(a: ISZ[Z], j: Z): Z = {
  if (a.isInBound(j)) {
    a(j) + sum_rec(a, j + 1)
  } else {
    0
  }
}

@strictpure def sum(a: ISZ[Z]): Z = sum_rec(a, 0)

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

@pure def pos_sum_seq(a: ISZ[Z]): Unit = {
  Contract(
    Requires(All(a.indices)(j => a(j) >= 0)),
    Ensures(sum_seq(a) >= 0)
  )
  Spec {
    pos_sum(a)
  }
}

@pure def sorted_check_0(a: ISZ[Z]): B = {
  Contract(
    Ensures(Res == All(1 until a.size)(i => a(i - 1) <= a(i)))
  )
  if (a.size == 0) {
    return true
  } else {
    var res: B = true;
    var k: Z = 1;
    while (k < a.size) {
      Invariant(
        Modifies(k, res),
        k >= 1,
        k <= a.size,
        res == All(1 until k)(i => a(i - 1) <= a(i))
      )
      if (a(k - 1) > a(k)) {
        res = false
      }
      k = k + 1
    }
    return res
  }
}

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

@pure def max_sorted_seq(a: ISZ[Z]): Z = {
  Contract(
    Requires(  a.size > 0, sorted(a)  ),
    Ensures(  Exists(a.indices)(j => a(j) == Res), All(a.indices)(j => a(j) <= Res)  )
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

def swap(a: MSZ[Z], i: Z, j: Z): Unit = {
  Contract(
    Requires(a.isInBound(i), a.isInBound(j)),
    Modifies(a),
    Ensures(
      a(i) == In(a)(j),
      a(j) == In(a)(i),
      All(a.indices)(k => k != i & k != j ___>: a(k) == In(a)(k)))
  )
  val ai: Z = a(i)
  a(i) = a(j)
  a(j) = ai
}