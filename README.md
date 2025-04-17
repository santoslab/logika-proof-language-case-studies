# logika-proof-language-case-studies

This repository holds examples that support the work in the paper:

> "Proof Engineering in Logika: Synergistically Integrating
  Automated and Semi-Automated Program Verification" 
  by Stefan Hallerstede, Robby, John Hatcliff, Jason Belt and David Hardin

- **Factorial (SMT)** [Factorial-SMT.sc](src/Factorial-SMT.sc)
  - used to illustrate Logika's SMT-based automated verification
    (to provide a contrast to the developer-directed version below
    that uses the Logika proof language.
   
- **Factorial (proof language)**  [Factorial.sc](src/Factorial.sc)
  - used to illustrate basic concepts of the Logika proof language, 
    including simplication (`Simpl`) and rewriting (`Rewrite`), 
    as well direct invocation of the SMT-based deduction 
    via the `Algebra` and `Auto` proof justifications. 
  
- **Doubly-Linked (DLL) List (with refinement from Cons list)** [DLLRefineList.sc](src/DLLRefineList.sc)
  - the primary case study in the paper.  The concrete implementation of the 
    DLL was originally written by author David Hardin (Collins Aerospace).
    Work reported on in this paper added the abstract Cons list 
    (which provides a basis for high-level specification of the concrete 
    implementation, via refinement),  as well as all specifications and 
    proofs.

- **Abstract list (illustrating induction proofs)** [List_Induct.sc](src/List_Induct.sc)
  - Inductive proof of list properties related to reverse, associativity, 
    etc. using rewriting and simplification to guide the proof.
  
- **Sequence sum**
  - In Logika, sequence induction is often done using while loops.
    This example shows how recursive properties are used in such proofs 
    and how abstract properties are propagated to refinements.
  
- **Maximum of sorted sequence**
The maximum of a sequence of increasing values can be computed by returning the last value of the sequence.
  - The proof of this in this development is a program that computes 
    the maximum value, confirming that the last value is the maximum.
    Except for the returned maximum, the entire program is enclosed 
    in a `Spec` block. The program itself becomes a correctness 
    annotation similar to typing information that confirms that values 
    have the correct type.
  
- **Symbol table** [Symbol_Table_Proofs.sc](src/Symbol_Table_Proofs.sc)
  - This example provides a symbol table that one might use, e.g.,
    in a program/model implementation environment.
    The development demonstrates the use of function calls 
    as theorem references and the replacement of
    abstract predicates in pre-conditions by more efficient 
    implementations without affecting the difficulty of the proofs.
    This approach is useful when compile-time and 
    run-time-verification use are combined in practice.