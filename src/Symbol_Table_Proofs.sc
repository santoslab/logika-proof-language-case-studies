// #Sireum #Logika
import org.sireum._
import org.sireum.justification._

// This small development deals with a symbol table implemented as a sequence
// of identifiers. Each identifier is composed of a name (that may occur more
// than once in the symbol table) and a number that makes the identifier
// different from all other identifiers (with the same name).
//
// For the identifiers in the symbol table we require that
// (1) they are unique: Each identifier occurs at most once, and
// (2) they are natural: Each identifier's number is at least 0.
//
// We prove that inserting an identifier with a given name as implemented
// in function fresh_ident preserves uniqueness and naturalness, and ensures
// that a corresponding new identifier is contained in the updated symbol table.

// Identifiers are represented the (immutable) datatype Ident.
@datatype class Ident (val name: String, val n: Z)

// A symbol table is represented as a (mutable) record SymTab.
@record class SymTab(var decls: ISZ[Ident])

// Observe the following property of inequality on a matrix of values.
// Because we know that for all i, j: seq(i) != seq(j) implies seq(j) != seq(i),
// it is sufficient to do only half the comparisons in one half of the
// diagonally split matrix. This means, we can implement a more efficient form
// of checking uniqueness based on this property.
// Logika proves this automatically.
@pure def symm_prop[T](seq: ISZ[T]): Unit = {
  Contract(
    Requires(All(seq.indices)(i => All(0 until i)(j => (seq(i) != seq(j))))),
    Ensures(All(seq.indices)(i => All(seq.indices)(j => (i != j) ->: (seq(i) != seq(j)))))
  )
}

// We define the (strong) uniqueness property as a boolean function unique_S.
// This gives access to this property to the simplifier.
@strictpure def unique_S[T](seq: ISZ[T]): B =
  All(seq.indices)(i => All(seq.indices)(j => (i != j) ->: (seq(i) != seq(j))))

// Based on the observed property above we implement it more efficiently.
// We only perform half of the inequality test because of the symmetry of !=.
@pure def unique[T](seq: ISZ[T]): B = {
  Contract(
    Ensures(Res == unique_S(seq))
  )
  var h: Z = 0
  while (h < seq.size) {
    Invariant(
      Modifies(h),
      0 <= h, h <= seq.size,
      All(0 until h)(i => All(0 until i)(j => (seq(i) != seq(j))))
    )
    var k: Z = 0
    while (k < h) {
      Invariant(
        Modifies(k),
        0 <= k, k <= seq.size,
        All(0 until k)(j => (seq(h) != seq(j)))
      )
      if (seq(h) == seq(k)) {
        return false
      }
      k = k + 1
    }
    h = h + 1
  }
  return true
}

// Unused proposition: Introduction of unique_S from the (weak) uniqueness property.
// This proposition is only stated for didactic reasons,
@pure def unique_I[T](seq: ISZ[T]): Unit = {
  Contract(
    Requires(All(seq.indices)(i => All(0 until i)(j => (seq(i) != seq(j))))),
    Ensures(unique_S(seq))
  )
  Deduce(
    1 (All(seq.indices)(i => All(0 until i)(j => (seq(i) != seq(j))))) by Premise,
    2 (All(seq.indices)(i => All(seq.indices)(j => (i != j) ->: (seq(i) != seq(j))))) by Auto,
    3 (unique_S(seq)) by Auto and 2
  )
}

// Unused proposition. Logika can do this fully automatic.
// This proposition is only stated for didactic reasons,
// The structured proof constructs of Logika provide means to drive
// the SMT solver by adding (relevant) and removing (irrelevant)
// facts, so that the proofs become more robust with potential timeouts.
// This is an important technique to manage large proofs that exceed
// the SMT solvers capabilities or require a lot of resources.
@pure def unique_extend(seq: ISZ[Ident], x: Ident): Unit = {
  Contract(
    Requires(unique(seq), All(seq.indices)(i => seq(i) != x)),
    Ensures(unique(seq :+ x))
  )
  Deduce(
    1 (unique(seq)) by Auto,
    2 (All(seq.indices)(i => seq(i) != x)) by Auto,
    3 (All(seq.indices)(i => All(seq.indices)(j => (i != j) ->: (seq(i) != seq(j))))) by Auto and 1,
    4 Let ((seqx: ISZ[Ident]) => SubProof(
      5 Assume(seqx == seq :+ x),
      6 Let ((i: Z) => SubProof(
        7 Assume(0 <= i & i < (seq :+ x).size),
        8 Let ((j: Z) => SubProof(
          9 Assume(0 <= j & j < i),
          10 SubProof(
            11 Assume(i < seq.size),
            12 (seqx(i) != seqx(j)) by Auto
          ),
          13 SubProof(
            14 Assume(i >= seq.size),
            15 (i == seq.size) by Auto,
            16 (seqx(i) != seqx(j)) by Auto
          ),
          17 (seqx(i) != seqx(j)) by Auto
        ))
      )),
      18 (All((seqx).indices)(i => All(0 until i)(j => ((seqx)(i) != (seqx)(j))))) by Auto,
      19 (All(seqx.indices)(i => All(seqx.indices)(j => (i != j) ->: (seqx(i) != seqx(j))))) by Auto and 18,
      20 (unique(seqx)) by Auto
    ))
  )
}

// Implementation of boolean function contains for containment of
// an element in a list.
@pure def contains[T](seq: ISZ[T], x: T): B = {
  Contract(
    Ensures(Res == Exists(seq.indices)(i => seq(i) == x))
  )
  var k: Z = 0
  while (k < seq.size) {
    Invariant(
      Modifies(k),
      0 <= k, k <= seq.size,
      All(0 until k)(i => seq(i) != x)
    )
    if (seq(k) == x) {
      return true
    }
    k = k + 1
  }
  return false
}

// Implementation of boolean function natural to determine naturalness
// of a symbol table.
@pure def natural(decls: ISZ[Ident]): B = {
  Contract(
    Ensures(Res == All(decls.indices)(i => decls(i).n >= 0))
  )
  var k: Z = 0
  while (k < decls.size) {
    Invariant(
      Modifies(k),
      0 <= k, k <= decls.size,
      All(0 until k)(i => decls(i).n >= 0)
    )
    if (decls(k).n < 0) {
      return false
    }
    k = k + 1
  }
  return true
}

// Function unbound is part of the implementation of fresh_ident.
// It computes an upper bound of the numbers stored with identifiers
// associated with the given name.
// If the name does not occur in the symbol table, -1 is returned.
// Because -1 + 1 equals 0, the value return by ubound ensures
// naturalness in the implementation of fresh_ident. Because it is an
// upper bound, uniqueness is ensured.
// ubound actually computes the maximum, if the name is contained in the
// symbol table. But this property would be stronger than what is needed
// to prove the two properties just discussed.
@pure def ubound(decls: ISZ[Ident], name: String): Z = {
  Contract(
    Ensures(Res[Z] >= -1, All(decls.indices)(i => (decls(i).name == name) ->: (decls(i).n <= Res)))
  )
  var b: Z = -1
  var k: Z = 0
  while (k < decls.size) {
    Invariant(
      Modifies(k, b),
      0 <= k, k <= decls.size,
      b >= -1,
      All(0 until k)(i => (decls(i).name == name) ->: (decls(i).n <= b))
    )
    if (decls(k).name == name && decls(k).n > b) {
      b = decls(k).n
    }
    k = k + 1
  }
  return b
}

// Implementation of insertion of a new identifier with a given name
// in the symbol table. It returns the corresponding number of the identifier,
// so that the pair (name, fresh_ident(symtab, name)) describes the new
// identifier in the updates symbol table symtab.
// The function preserves uniqueness and naturalness, and it ensures that
// the new identifier is contained in the updated symbol table.
def fresh_ident(symtab: SymTab, name: String): Z = {
  Contract(
    Requires(unique(symtab.decls), natural(symtab.decls)),
    Modifies(symtab),
    Ensures(unique(symtab.decls), natural(symtab.decls), contains(symtab.decls, Ident(name, Res)))
  )
  // The deductions below are commented out to show that Logika can perform
  // everything automatically at this stage. In practice, they should remain
  // in the code. During development, they were used to debug the proof.
  // When looking at failed proof obligations (by clicking on the light bulb),
  // one can formulate hypotheses about what information is missing for the proof
  // to succeed. Inserting the deductions eventually makes Logika verify the
  // indented claim (here: the ensures clause of the function). Only some of the
  // stated deductions remain unproved. These have to be dealt with locally, e.g.,
  // stating bnd >= -1 below the call of ubound, required this condition to be
  // added to the ensures clause of ubound. It is very common to omit corner cases
  // in properties. Logika can be used to find them following this approach.
  // If the Deduce statements are left in the code, the code becomes easier to
  // modify as modifications that violate these conditions are signalled right away.
  // Of course, this is based on the heuristic that corner cases and conditions
  // that have been overlooked before might be overlooked again. This guards
  // against regression in correctness proofs.
  val bnd: Z = ubound(symtab.decls, name)
  // Deduce(|- (bnd >= -1))
  val n: Z = bnd + 1
  val ident: Ident = Ident(name, n)
  //Deduce(|- (All(symtab.decls.indices)(i => symtab.decls(i) != ident)))
  val newdecls = symtab.decls :+ ident
  //Deduce(|- (unique(newdecls)))
  symtab.decls = newdecls
  return n
}