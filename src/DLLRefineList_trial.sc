// #Sireum #Logika
import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._
import org.sireum.justification.natded.pred._

// List trait with some basic list functionality implemented.
@datatype trait List[T] {

  @strictpure def hd: T = this match {
    case List.Cons(value, _) => value
    case _ => halt("hd")
  }

  @strictpure def tl: List[T] = this match {
    case List.Cons(_, next) => next
    case _ => List.Nil()
  }

  @strictpure def drop(n: Z): List[T] = if (n > 0) {
    this match {
      case List.Cons(_, next) => next.drop(n - 1)
      case _ => List.Nil()
    }
  } else {
    this
  }
}

object List {

  @datatype class Nil[T] extends List[T]

  @datatype class Cons[T](val value: T, val next: List[T]) extends List[T]

  // This was supposed to be an nd/rewriting proof;
  // I have already replaced the rewrite commands with Auto
  @pure def drop_st_rewr[T](l: List[T]): Unit = {
    Contract(
      Ensures(All { n: Z => n > 0 ___>: l.tl.drop(n) == l.drop(n + 1) })
    )
    (l: @induct) match {
      case Nil() =>
        Deduce(|-(All { n: Z => l.tl.drop(n) == l.drop(n + 1) }))
      case Cons(value, next) =>
        Deduce(
          1(All { n: Z => n > 0 ___>: next.tl.drop(n) == next.drop(n + 1) }) by Premise,
          2 Let ((k: Z) => SubProof(
            3 SubProof(
              4 Assume (k > 0),
              5(l ≡ Cons(value, next)) by Premise,
              6(k - 1 > 0 ___>: next.tl.drop(k - 1) == next.drop(k - 1 + 1)) by AllE[Z](1),
              7(k > 0 ___>: next.drop(k) == next.tl.drop(k - 1)) by Auto and (4, 6),
              8(next.drop(k) == next.tl.drop(k - 1)) by SImplyE(7, 4),
              9(l.tl.drop(k) == next.tl.drop(k - 1)) by Auto and (5, 8),
              10(l.tl.drop(k) == l.drop(k + 1)) by Auto
            ),
            11(k > 0 ___>: l.tl.drop(k) == l.drop(k + 1)) by SImplyI(3)
          )),
          12(All { n: Z => n > 0 ___>: l.tl.drop(n) == l.drop(n + 1) }) by AllI[Z](2)
        )
        Deduce(|-(All { n: Z => n > 0 ___>: l.tl.drop(n) == l.drop(n + 1) }))
    }
  }

  //
  @pure def drop_st[T](l: List[T]): Unit = {
    Contract(
      Ensures(All{ n: Z => n > 0 ___>: l.tl.drop(n) == l.drop(n + 1) })
    )
    (l: @induct) match {
      case Nil() =>
      case Cons(value, next) =>
        Deduce(
          1 (All{ n: Z => n > 0 ___>: next.tl.drop(n) == next.drop(n + 1) }) by Premise,
          2 Let((k: Z) => SubProof(
            3 (l ≡ Cons(value, next)) by Premise,
            4 (k > 0 ___>: next.tl.drop(k - 1) == next.drop(k)) by Auto and 1,
            5 (k > 0 ___>: l.tl.drop(k) == next.tl.drop(k - 1)) by Auto,
            6 (k > 0 ___>: l.drop(k + 1) == l.tl.drop(k)) by Auto,
            7 (k > 0 ___>: l.tl.drop(k) == l.drop(k + 1)) by Auto
          )),
          8 (All{ n: Z => n > 0 ___>: l.tl.drop(n) == l.drop(n + 1) }) by AllI[Z](2)
        )
    }
  }
}
