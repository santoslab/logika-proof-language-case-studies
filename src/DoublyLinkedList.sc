// #Sireum #Logika
import org.sireum._

// Pool-based Doubly-Linked List

@sig trait DLOrdering[E] {
  @pure def equiv(o: E, other: E): B
  @pure def lt(o: E, other: E): B
}

@datatype trait DL[E] { // [E](ord: ALOrdering[E])
  // Robby: needs [E] for uniformity
  @pure def isLeaf: B // Robby: define isLeaf to workaround type erasure
}

// note: datatype/record without payload is automatically cached as singleton in Slang
@datatype class Leaf[E] extends DL[E] { // [E](ord: DLOrdering[E]) // Robby: object can only "extend" App in Slang
  @pure def isLeaf: B = {
    return T
  }
}

@datatype class Node[E](elem: E,
                        used: B,
                        left: DLLPool.PoolPtr,
                        right: DLLPool.PoolPtr) extends DL[E] {

  @pure def isLeaf: B = {
    return F
  }
}

object DLLPool {
  type PoolPtr = Z
  //  val maxSz: Z = 1024
  val Null: PoolPtr = -1
}

import DLLPool._

@record class DLLPool[@imm E](ord: DLOrdering[E], eDefault: E, poolSz: Z) {

  // Internal representation

  // "pointer" type for DLLPool, i.e., index to memory pool.
  // Out-of-bounds value means NULL

  val defaultNode: Node[E] = Node[E](eDefault, F, Null, Null)

  val maxSz: Z = if (poolSz > 0) poolSz else 0
  val pool: MSZ[Node[E]] = MSZ.create(maxSz, defaultNode)

  @abs def isPointer(p: Z): B = {
    p == Null || (0 <= p & p < maxSz)
  }

  @spec def maxSzPoolSize = Invariant(
    maxSz == pool.size
  )
  @spec def poolChildLeft = Invariant(
    All(pool.indices)(i => 0 <= pool(i).left & pool(i).left < maxSz)
  )
  @spec def poolChildRight = Invariant(
    All(pool.indices)(i => 0 <= pool(i).right & pool(i).right < maxSz)
  )

  var head: Z = Null
  @spec def headRange = Invariant(
    isPointer(head)
  )
  var tail: Z = Null
  @spec def tailRange = Invariant(
    isPointer(tail)
  )
  @spec def headTailSame = Invariant(
    (head == Null) == (tail == Null)
  )

  def initPool(): Unit = {
    Contract(
      Ensures(All(pool.indices)(i => pool(i) == defaultNode))
    )
    var i: Z = 0;
    while (i < pool.size) {
      Invariant(
        Modifies(i),
        0 <= i, i <= pool.size,
        All(0 until i)(i => pool(i) == defaultNode)
      )
      pool(i) = defaultNode
      i = i + 1
    }
  }

  // SHA: With the added invariant this can be done more efficiently.
//  @pure def isLeaf(p: Z): B = {
//    Contract(
//      Ensures(Res == p < 0 || (p >= maxSz))
//    )
//    return (p < 0) || (p >= maxSz)
//  }

  @pure def isLeaf(p: Z): B = {
    Contract(
      Ensures(Res == (p == Null))
    )
    return p == Null
  }

  // SHA: ditto, see above
//  @pure def isEmpty: B = {
//    // cannot be @pure because it depends on mutable objects
//    // SHA: I have just tried. Unless there'd be concurrent modifications
//    // possible, this shouldn't be a problem.
//    return (head < 0) || (head >= maxSz) || (tail < 0) || (tail >= maxSz)
//  }

  @pure def isEmpty: B = {
    Contract(
      Ensures(Res == (head == Null & tail == Null))
    )
    return head == Null
  }

  //  @annotation.tailrec
  def countL(p: Z, acc: Z): Z = {
    Contract(
      Requires(isPointer(p))
    )
    if (isLeaf(p)) {
      return acc
    } else {
      val n: Node[E] = pool(p)
      if (p == n.left) {
        return 0
      } else {
        return countL(n.left, acc + 1)
      }
    }
  }

  def fOezis: Z = {
    Contract(
      Requires(!isEmpty)
    )
    return countL(tail, 0)
  }


  //  @annotation.tailrec
  def countR(p: Z, acc: Z): Z = {
    Contract(
      Requires(isPointer(p))
    )
    if (isLeaf(p)) {
      return acc
    } else {
      val n: Node[E] = pool(p)
      if (p == n.right) {
        return 0
      } else {
        return countR(n.right, acc + 1)
      }
    }
  }

  def sizeOf: Z = {
    Contract(
      Requires(!isEmpty)
    )
    return countR(head, 0)
  }


  def findFreeNode(): Z = {
    Contract(
      Ensures(isPointer(Res))
    )
    var i: Z = 0
    // SHA: Robby,
    // There seems to a problem with the evaluation of the
    // short-circuit boolean expression.
    while ((i < pool.size) && (pool(i) != defaultNode)) {
      Invariant(
        Modifies(i),
        0 <= i, i <= pool.size
      )
      i = i + 1
    }
    if (i == pool.size) {
      i = Null
    }
    return i
  }


  //  @annotation.tailrec
  def findIndexL(elem: E, p: Z): Z = {
    Contract(
      Requires(isPointer(p))
    )
    if (isLeaf(p)) {
      return Null
    } else {
      pool(p) match {
        case Node(_, F, _, _) => return Null
        case Node(e, T, _, _) if ord.equiv(elem, e) => return p
        case Node(_, T, l, _) => return findIndexL(elem, l)
      }
    }
  }

  def findL(e: E): Z = {
    return findIndexR(e, tail)
  }


  //  @annotation.tailrec
  def findIndexR(elem: E, p: Z): Z = {
    Contract(
      Requires(isPointer(p))
    )
    if (isLeaf(p)) {
      return Null
    } else {
      pool(p) match {
        case Node(_, F, _, _) => return Null
        case Node(e, T, _, _) if ord.equiv(elem, e) => return p
        case Node(_, T, _, r) => return findIndexR(elem, r)
      }
    }
  }

  def findR(e: E): Z = {
    return findIndexR(e, head)
  }


  def clear(): Unit = {
    head = Null
    tail = Null
    initPool()
  }


  //  @annotation.tailrec
  // SHA: In case p points to an unused node, Null is returned.
  //      How can it happen that p points to an unused node?
  //      Shouldn't it be reset to Null to avoid this?
  def nthIndexL(n: Z, p: Z): Z = {
    Contract(
      Requires(isPointer(p)),
      Ensures(isPointer(Res))
    )
    if ((n < 0) || isLeaf(p)) {
      return Null
    } else {
      pool(p) match {
        case Node(_, F, _, _) => return Null
        case Node(_, T, _, _) if (n == 0) => return p
        case Node(_, T, l, _) => return nthIndexL(n - 1, l)
      }
    }
    return Null;   // C transpiler complains unless this is present
  }

  def htn(n: Z): Option[E] = {
    val i: Z = nthIndexL(n, tail)
    if (i < 0) {
      return None[E]()
    } else {
      val nd: Node[E] = pool(i)
      return Some(nd.elem)
    }
  }


  //  @annotation.tailrec
  def nthIndexR(n: Z, p: Z): Z = {
    Contract(
      Requires(isPointer(p)),
      Ensures(isPointer(Res))
    )
    if ((n < 0) || isLeaf(p)) {
      return Null
    } else {
      pool(p) match {
        case Node(_, F, _, _) => return Null
        case Node(_, T, _, _) if (n == 0) => return p
        case Node(_, T, _, r) => return nthIndexR(n - 1, r)
      }
    }
    return Null;   // C transpiler complains unless this is present
  }

  def nth(n: Z): Option[E] = {
    val i: Z = nthIndexR(n, head)
    if (i < 0) {
      return None[E]()
    } else {
      val nd: Node[E] = pool(i)
      return Some(nd.elem)
    }
  }


  def insertAfter(elem: E, p: Z): Unit = {
    Contract(
      Requires(isPointer(p))
    )
    if (isLeaf(p)) {
      if (isEmpty) {
        // SHA: Needed to insert this, in case of a list of capacity 0
        if (maxSz > 0) {
          head = 0
          tail = 0
          pool(0) = Node[E](elem, T, Null, Null)
        }
        Deduce(|- (maxSz == pool.size))
      }
      Deduce(|- (maxSz == pool.size))
    } else {
      pool(p) match {
        // Unused node -- should not happen
        case Node(_, F, _, _) =>
          Deduce(|- (maxSz == pool.size))
        case Node(_, T, _, r) =>
          val pnew: Z = findFreeNode()
          if (pnew >= 0) {
            if (r != Null) {
              pool(r) = pool(r)(left = pnew)
            }
            pool(p) = pool(p)(right = pnew)
            pool(pnew) = Node[E](elem, T, p, r)
            Deduce(|- (maxSz == pool.size))
            if (tail == p) {
              tail = pnew
            }
          }
          Deduce(|- (maxSz == pool.size))
      }
      // SHA: Robby,
      // This should prove because the two branches are exhaustive
      // and both establish the property. Same problem in functions
      // below.
      Deduce(|- (maxSz == pool.size))
    }
    Deduce(|- (maxSz == pool.size))
  }

  def snoc(elem: E): Unit = {
    insertAfter(elem, tail)
  }


  def insertBefore(elem: E, p: Z): Unit = {
    Contract(
      Requires(isPointer(p))
    )
    if (isLeaf(p)) {
      if (isEmpty) {
        if (maxSz > 0) {
          head = 0
          tail = 0
          pool(0) = Node[E](elem, T, Null, Null)
        }
      }
    } else {
      pool(p) match {
        // Unused node -- should not happen
        case Node(_, F, _, _) =>
        case Node(_, T, l, _) =>
          val pnew: Z = findFreeNode()
          if (pnew >= 0) {
            if (l != Null) {
              pool(l) = pool(l)(right = pnew)
            }
            pool(p) = pool(p)(left = pnew)
            pool(pnew) = Node[E](elem, T, l, p)
            if (head == p) {
              head = pnew
            }
          }
      }
    }
  }

  def cons(elem: E): Unit = {
    insertBefore(elem, head)
  }


  def updateIndex(elem: E, p: Z): Unit = {
    Contract(
      Requires(isPointer(p))
    )
    if (isLeaf(p)) {
      // return
    } else {
      pool(p) match {
        // Unused node -- should not happen
        case Node(_, F, _, _) =>
        case Node(_, T, _, _) =>
          pool(p) = pool(p)(elem = elem)
      }
    }
  }

  def htn_etadpu(n: Z, elem: E): Unit = {
    if (n < 0) {
      // return
    } else {
      val i: Z = nthIndexL(n, tail)
      if (i >= 0) {
        updateIndex(elem, i)
      }
    }
  }

  def update_nth(n: Z, elem: E): Unit = {
    if (n < 0) {
      // return
    } else {
      val i: Z = nthIndexR(n, head)
      if (i >= 0) {
        updateIndex(elem, i)
      }
    }
  }


  def foreachR(f: ((E)) => Unit @pure, p: Z): Unit = {
    Contract(
      Requires(isPointer(p))
    )
    if (isLeaf(p)) {
      //return
    } else {
      pool(p) match {
        // Unused node -- should not happen
        case Node(_, F, _, _) =>
        case Node(e, T, l, r) =>
          f((e))
          foreachR(f, r)
      }
    }
  }

  def foreach(f: ((E)) => Unit @pure): Unit = {
    foreachR(f, head)
  }


  // Rest, from tail
  def tser(): Unit = {
    if (isEmpty) {
      // return
    } else {
      pool(tail) match {
        // Unused node -- should not happen
        case Node(_, F, _, _) =>
        // Nothing to left
        case Node(_, T, l, _) if isLeaf(l) =>
          if (fOezis == 1) {
            head = Null
            tail = Null
            initPool()
          } else {
            // pathological case -- should not happen
            pool(tail) = defaultNode
            tail = Null  // tail pointer becomes "detached"
          }
        case Node(_, T, l, _) =>
          pool(tail) = defaultNode
          pool(l) = pool(l)(right = Null)
          tail = l
      }
    }
  }


  // Rest, from head
  def rest(): Unit = {
    if (isEmpty) {
      // return
    } else {
      pool(head) match {
        // Unused node -- should not happen
        case Node(_, F, _, _) =>
        // Nothing to right
        case Node(_, T, l, _) if isLeaf(l) =>
          if (sizeOf == 1) {
            head = Null
            tail = Null
            initPool()
          } else {
            // pathological case -- should not happen
            pool(head) = defaultNode
            head = Null  // head pointer becomes "detached"
          }
        case Node(_, T, _, r) =>
          pool(head) = defaultNode
          pool(r) = pool(r)(left = Null)
          head = r
      }
    }
  }


  def deleteIndexL(elem: E, p: Z): Unit = {
    Contract(
      Requires(isPointer(p))
    )
    if (isLeaf(p)) {
      //return
    } else {
      pool(p) match {
        // Unused node -- should not happen
        case Node(_, F, _, _) =>
        // Found it, nothing to left and right
        case Node(e, T, l, r) if ord.equiv(elem, e) && isLeaf(l) && isLeaf(r) =>
          if (fOezis == 1) {
            head = Null
            tail = Null
            initPool()
          } else {
            // pathological case -- should not happen
            pool(p) = defaultNode
          }
        case Node(e, T, l, r) if ord.equiv(elem, e) && isLeaf(l) =>
          pool(p) = defaultNode
          pool(r) = pool(r)(left = Null)
          if (head == p) { head = r }
        case Node(e, T, l, r) if ord.equiv(elem, e) && isLeaf(r) =>
          pool(p) = defaultNode
          pool(l) = pool(l)(right = Null)
          if (tail == p) { tail = l }
        case Node(e, T, l, r) if ord.equiv(elem, e) =>
          pool(p) = defaultNode
          pool(l) = pool(l)(right = r)
          pool(r) = pool(r)(left = l)
        case Node(_, T, l, _) => deleteIndexL(elem, l)
      }
    }
  }

  // Delete, proceeding leftward

  def eteled(e: E): Unit = {
    deleteIndexL(e, tail)
  }


  def deleteIndexR(elem: E, p: Z): Unit = {
    Contract(
      Requires(isPointer(p))
    )
    if (isLeaf(p)) {
      //return
    } else {
      pool(p) match {
        // Unused node -- should not happen
        case Node(_, F, _, _) =>
        // Found it, nothing to left and right
        case Node(e, T, l, r) if ord.equiv(elem, e) && isLeaf(l) && isLeaf(r) =>
          if (sizeOf == 1) {
            head = Null
            tail = Null
            initPool()
          } else {
            // pathological case -- should not happen
            pool(p) = defaultNode
          }
        case Node(e, T, l, r) if ord.equiv(elem, e) && isLeaf(l) =>
          pool(p) = defaultNode
          pool(r) = pool(r)(left = Null)
          if (head == p) { head = r }
        case Node(e, T, l, r) if ord.equiv(elem, e) && isLeaf(r) =>
          pool(p) = defaultNode
          pool(l) = pool(l)(right = Null)
          if (tail == p) { tail = l }
        case Node(e, T, l, r) if ord.equiv(elem, e) =>
          pool(p) = defaultNode
          pool(l) = pool(l)(right = r)
          pool(r) = pool(r)(left = l)
        case Node(_, T, _, r) => deleteIndexR(elem, r)
      }
    }
  }

  // Delete, proceeding rightward

  def delete(e: E): Unit = {
    deleteIndexR(e, head)
  }


  def deletIndex(p: Z): Unit = {
    Contract(
      Requires(isPointer(p))
    )
    if (isLeaf(p)) {
      //return
    } else {
      pool(p) match {
        // Unused node -- should not happen
        case Node(_, F, _, _) =>
        // Found it, nothing to left and right
        case Node(_, T, l, r) if isLeaf(l) && isLeaf(r) =>
          if (sizeOf == 1) {
            head = Null
            tail = Null
            initPool()
          } else {
            // pathological case -- should not happen
            pool(p) = defaultNode
          }
        case Node(_, T, l, r) if isLeaf(l) =>
          pool(p) = defaultNode
          pool(r) = pool(r)(left = Null)
          if (head == p) { head = r }
        case Node(_, T, l, r) if isLeaf(r) =>
          pool(p) = defaultNode
          pool(l) = pool(l)(right = Null)
          if (tail == p) { tail = l }
        case Node(_, T, l, r) =>
          pool(p) = defaultNode
          pool(l) = pool(l)(right = r)
          pool(r) = pool(r)(left = l)
      }
    }
  }


  def stringify(p: Z): String = {
    Contract(
      Requires(isPointer(p))
    )
    if (isLeaf(p)) {
      return s""
    } else {
      pool(p) match {
        // Unused node -- should not happen
        case Node(_, F, _, _) => return s"UNUSED"
        case Node(e, T, l, r) if isLeaf(r) =>
          val res =
            s"($e [$p] :$l :$r)"
          return res
        case Node(e, T, l, r) =>
          val res =
            s"""($e [$p] :$l :$r) ${stringify(r)}"""
          return res
      }
    }
  }


  // Robby: changed to use s"..." and Predef.String
  // (Slang's String is different from Scala's Predef.String)
  override def string: String = {
    return s"(${stringify(head)})"
  }
}
