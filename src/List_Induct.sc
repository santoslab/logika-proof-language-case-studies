// #Sireum #Logika
import org.sireum._
import org.sireum.justification._

// List trait with some basic list functionality implemented.
@datatype trait List[T] {

  @strictpure def length: Z = this match {
    case List.Cons(_, next) => 1 + next.length
    case _ => 0
  }

  @strictpure def hd: T = this match {
    case List.Cons(value, _) => value
    case _ => halt("Trying to access hd on an empty list")
  }

  @strictpure def tl: List[T] = this match {
    case List.Cons(_, next) => next
    case _ => List.Nil()
  }

  @strictpure def ++(l2: List[T]): List[T] = this match {
    case List.Cons(value, next) => List.Cons(value, next ++ l2)
    case _ => l2
  }

  @strictpure def drop(n: Z): List[T] = if (n > 0) {
    this match {
      case List.Cons(_, next) => next.drop(n - 1)
      case _ => List.empty
    }
  } else {
    this
  }

  @strictpure def take(n: Z): List[T] = if (n > 0) {
    this match {
      case List.Cons(value, next) => List.Cons(value, next.take(n - 1))
      case _ => List.empty
    }
  } else {
    List.empty
  }

  // Implementation of "reverse" using ++ to avoid introducing
  // an accumulator argument.
  @strictpure def rev: List[T] = this match {
    case List.Cons(value, next) => next.rev ++ List.make(value)
    case _ => this
  }
}

object List {

  @datatype class Nil[T] extends List[T]

  @datatype class Cons[T](val value: T, val next: List[T]) extends List[T]

  @strictpure def make[T](value: T): List[T] = Cons(value, Nil())

  @strictpure def empty[T]: List[T] = Nil()

  @pure def lengthAtLeastZero[T](l: List[T]): Unit = {
    Contract(
      Ensures(l.length >= 0)
    )
    (l: @induct) match {
      case Cons(value, next) =>
        return
      case Nil() =>
        return
    }
  }

  // Lemma: Appending the empty list to a list yields that list.
  @pure def appNil[T](x: List[T]): Unit = {
    Contract(
      Ensures((x ++ Nil[T]()) ≡ x)
    )
    (x : @induct) match {
      case Cons(value, next) => return
      case Nil() => return
    }
  }

  // Lemma: Appending lists is associative.
  @pure def appAssoc[T](x: List[T], y: List[T], z: List[T]): Unit = {
    Contract(
      Ensures(((x ++ y) ++ z) ≡ (x ++ (y ++ z)))
    )

    (x: @induct) match {
      case Cons(value, next) =>
        Deduce(
          1 ((Cons(value, next) ++ y) ≡ Cons(value, next ++ y)) by Simpl,
          2 (((Cons(value, next) ++ y) ++ z) ≡ (Cons(value, next ++ y) ++ z)) by Simpl,
          3 ((Cons(value, next ++ y) ++ z) ≡ Cons(value, next ++ y ++ z)) by Simpl,
          4 Assert((Cons(value, next ++ y) ++ z) ≡ Cons(value, next ++ (y ++ z)), SubProof(
            5 ((next ++ y ++ z) ≡ (next ++ (y ++ z))) by Premise,
            6 ((Cons(value, next ++ y) ++ z) ≡ Cons(value, next ++ (y ++ z))) by Subst_<(5, 3)
          )),
          7 (Cons(value, next ++ (y ++ z)) ≡ (Cons(value, next) ++ (y ++ z))) by Simpl,
          8 (x ≡ Cons(value, next)) by Premise,
          9 (((Cons(value, next) ++ y) ++ z) ≡ (Cons(value, next) ++ (y ++ z))) by Auto,
          10 (((x ++ y) ++ z) ≡ (x ++ (y ++ z))) by Subst_>(8, 9)
        )
        return
      case Nil() =>
        Deduce(
          1 (  x ≡ Nil[T]()                       ) by Premise,
          2 (  (Nil[T]() ++ y) ≡ y                ) by Simpl,
          3 (  (x ++ y) ≡ y                       ) by Subst_>(1, 2),
          4 (  (Nil[T]() ++ (y ++ z)) ≡ (y ++ z)  ) by Simpl,
          5 (  (x ++ (y ++ z)) ≡ (y ++ z)         ) by Subst_>(1, 4)
        )
        return
    }
  }

  // Variant of preceding lemma with unstructured proof.
  // 'Assert' makes proof easier to write and read.
  // Not used. Only stated for didactic reasons.
  @pure def appAssoc1[T](x: List[T], y: List[T], z: List[T]): Unit = {
    Contract(
      Ensures(((x ++ y) ++ z) == (x ++ (y ++ z)))
    )

    (x: @induct) match {
      case Cons(value, next) =>
        Deduce(
          1 (Cons(value, next) ++ y == Cons(value, next ++ y)) by Simpl,
          2 ((Cons(value, next) ++ y) ++ z == Cons(value, next ++ y) ++ z) by Simpl,
          3 (Cons(value, next ++ y) ++ z == Cons(value, next ++ y ++ z)) by Simpl,
          4 (next ++ y ++ z == next ++ (y ++ z)) by Auto, // Why isn't this Premise?
          5 (Cons(value, next ++ y) ++ z == Cons(value, next ++ (y ++ z))) by Subst_<(4, 3),
          6 (Cons(value, next ++ (y ++ z)) == Cons(value, next) ++ (y ++ z)) by Simpl,
          7 (x == Cons(value, next)) by Auto, // Why isn't this Premise?
          8 ((Cons(value, next) ++ y) ++ z == Cons(value, next) ++ (y ++ z)) by Auto and (2, 3, 5, 6),
          9 ((x ++ y) ++ z == x ++ (y ++ z)) by Subst_>(7, 8)
        )
        return
      case Nil() =>
        Deduce(
          1 (x == Nil[T]()) by Auto, // Why isn't this Premise?
          2 (Nil[T]() ++ y == y) by Simpl,
          3 (x ++ y == y) by Subst_>(1, 2),
          4 (Nil[T]() ++ (y ++ z) == (y ++ z)) by Simpl,
          5 (x ++ (y ++ z) == y ++ z) by Subst_>(1, 4)
        )
        return
    }
  }

  // Lemma: Skewed distributivity of ++ and rev.
  // Uses lemmas appNil and appAssoc.
  @pure def revApp[T](x: List[T], y: List[T]): Unit = {
    Contract(
      Ensures((x ++ y).rev ≡ (y.rev ++ x.rev))
    )

    (x: @induct) match {
      case Cons(value, next) =>
        Deduce(
          1 ((next ++ y).rev ≡ (y.rev ++ next.rev)) by Premise,
          2 (x ≡ List.Cons(value, next)) by Premise,
          3 (List.Cons(value, next).rev ≡ (next.rev ++ List.make(value))) by Simpl,
          4 (List.Cons(value, next ++ y).rev ≡ ((next ++ y).rev ++ List.make(value))) by Simpl,
          5 ((List.Cons(value, next) ++ y) ≡ List.Cons(value, next ++ y)) by Simpl,
          6 ((x ++ y) ≡ List.Cons(value, next ++ y)) by Subst_>(2, 5),
          7 ((x ++ y).rev ≡ List.Cons(value, next ++ y).rev) by Simpl and (6),
          8 (List.Cons(value, next ++ y).rev ≡ ((y.rev ++ next.rev) ++ List.make(value))) by Subst_<(1, 4),
          9 (List.Cons(value, next ++ y).rev ≡ (y.rev ++ (next.rev ++ List.make(value)))) by Rewrite(RS(appAssoc _), 8),
          10 ((y.rev ++ (next.rev ++ List.make(value))) ≡ (y.rev ++ Cons(value, next).rev)) by Auto,
          11 ((x ++ y).rev ≡ (y.rev ++ x.rev)) by Auto
        )
        return
      case Nil() =>
        Deduce(
          1 (x ≡ Nil[T]()) by Premise,
          2 ((x ++ y) ≡ y) by Simpl,
          4 ((x ++ y).rev ≡ y.rev) by Simpl,
          5 (x.rev ≡ Nil[T]()) by Simpl,
          6 ((y.rev ++ Nil[T]()) ≡ y.rev) by RSimpl(RS(appNil _)),
          7 ((y.rev ++ x.rev) ≡ y.rev) by Subst_>(5, 6),
          8 ((x ++ y).rev ≡ (y.rev ++ x.rev)) by Subst_>(7, 4)
        )
        return
    }
  }

  // Theorem: Idempotence of rev.
  // This is the actual objective.
  // All other properties are only proved to obtain this result.
  // Uses lemma revApp.
  @pure def rev_prop[T](l: List[T]): Unit = {
    Contract(
      Ensures(l.rev.rev ≡ l)
    )
    (l: @induct) match {
      case Cons(value, next) =>
        Deduce(
          1 (l ≡ List.Cons(value, next)) by Premise,
          2 (next.rev.rev ≡ next) by Premise,
          3 (List.Cons(value, next).rev ≡ (next.rev ++ List.make(value))) by Simpl,
          4 ((next.rev ++ List.make(value)).rev ≡ (List.make(value).rev ++ next.rev.rev)) by RSimpl(RS(revApp _)),
          5 (List.make(value).rev ≡ List.make(value)) by Auto,
          6 (l.rev.rev ≡ l) by Auto
        )
        return
      case Nil() =>
        return
    }
  }
}