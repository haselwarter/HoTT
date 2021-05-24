(** This file introduces formal equations [Equations], interpretation of equations [InterpEquations], and model of equational theory [IsModelAlgebra]. *)

Require Export
  HoTT.Algebra.Universal.Algebra
  HoTT.Algebra.Universal.TermAlgebra.

Require Import HoTT.Spaces.Finite.Fin.

Unset Elimination Schemes.

Local Open Scope Algebra_scope.
Local Open Scope nat_scope.

(** A formal σ-equation [Equation], for [σ : Signature], consists of a context set [context_equation] and two terms [left_equation] and [right_equations], both of some sort [sort_equation]. This can be written as
<<
  Γ ⊢ ℓ ≈ r
>>
where [Γ] is the context set and [ℓ], [r], the terms. *)

Record Equation {σ : Signature} : Type :=
  Build_Equation
  { context_equation : Carriers σ
  ; hset_context_equation : forall s, IsHSet (context_equation s)
  ; sort_equation : Sort σ
  ; left_equation : CarriersTermAlgebra context_equation sort_equation
  ; right_equation : CarriersTermAlgebra context_equation sort_equation }.

Global Arguments Equation : clear implicits.

Global Arguments Build_Equation
  {σ} context_equation {hset_context_equation}.

Global Existing Instance hset_context_equation.

(** A collection of σ-equations indexed by [I]: *)

Record Equations (σ : Signature) (I : Type) : Type
  := Build_Equations { equations : I -> Equation σ }.

Arguments equations {σ} {I}.

Global Coercion equations : Equations >-> Funclass.

(** Note: the type [{σ : Signature | {I : Type | Equations σ I}}] is commonly referred to as equational theory or algebraic theory.

For example the theory of monoids is an algebraic theory. Here [σ] is a one sorted signature with a nullary operation symbol [u] and a binary operation symbol [m]. The index type [I] is [Fin 3], and the three equations are
<<
  {x} ⊢ m (u, x) ≈ x
  {x} ⊢ m (x, u) ≈ x
  {x,y,z} ⊢ m (m (x, y), z) ≈ m (x, m (y, z))
>>
We are abusing notation in the above equations by writing [m] in the equations rather than [ops_term_algebra {x,y,z} m], and [x] rather than [var_term_algebra {x,y,z} _ x], etc. *)

Section InterpEquations.
  Context {σ} (A : Algebra σ).

(** The interpretation of a σ-equation [Γ ⊢ ℓ ≈ r] in [A] is a type
<<
  forall (f : forall s, Γ s -> A s), t f ℓ = t f r
>>
where
<<
  t : (forall s, Γ s -> A s) -> forall {s}, CarriersTermAlgebra Γ s -> A s
>>
returns the canonical homomorphism out of the term algebra, interpreting the terms [ℓ] and [r]. *)

  Definition InterpEquation (e : Equation σ) : Type
    := forall (f : forall s, context_equation e s -> A s),
       map_term_algebra A f (sort_equation e) (left_equation e)
       = map_term_algebra A f (sort_equation e) (right_equation e).

(** The interpretation of a collection of σ-equations: *)

  Definition InterpEquations {I : Type} (e : Equations σ I)
    := forall (i:I), InterpEquation (e i).

End InterpEquations.

(** An algebra [A] for signature [σ] is a model of the equational theory [e : Equations σ I] if the interpretation of the equations [InterpEquations A e] holds. *)

Class IsModelAlgebra {σ : Signature}
  (A : Algebra σ) {I : Type} (e : Equations σ I)
  := equations_model : InterpEquations A e.

Record ModelAlgebra {σ : Signature} {I : Type} (e : Equations σ I) :=
  Build_ModelAlgebra
  { model_algebra : Algebra σ
  ; is_equational_model_algebra : IsModelAlgebra model_algebra e
  }.

Arguments Build_ModelAlgebra {σ} {I} e
            model_algebra {is_equational_model_algebra}.
Arguments model_algebra {σ} {I} {e}.
Arguments is_equational_model_algebra {σ} {I} {e}.

Global Coercion model_algebra : ModelAlgebra >-> Algebra.

Global Existing Instance is_equational_model_algebra.

Section single_sorted_equation_op.
  Context (Sym : Type) `{!IsHSet Sym} (Aris : Sym -> Type).

  Local Notation sσ := (Build_SingleSortedSignature Sym Aris).

  Definition nullary_equation_op
    (u : Symbol sσ) (isnul : Aris u = Fin 0) (C : Carriers sσ)
    : CarriersTermAlgebra C tt
    := ops_term_algebra C u
        (transport (fun A => A -> CarriersTermAlgebra C tt) isnul^
          (Empty_rec _)).

  Definition unary_equation_op
    (u : Symbol sσ) (isuna : Aris u = Fin 1)
    (C : Carriers sσ) (T : CarriersTermAlgebra C tt)
    : CarriersTermAlgebra C tt
    := ops_term_algebra C u
        (transport (fun A => A -> CarriersTermAlgebra C tt) isuna^
          (fun k => match k with
                    | inr _ => T
                    | inl e => Empty_rec _ e
                    end)).

  Definition binary_equation_op 
    (u : Symbol sσ) (isbin : Aris u = Fin 2)
    (C : Carriers sσ) (L R : CarriersTermAlgebra C tt)
    : CarriersTermAlgebra C tt
    := ops_term_algebra C u
        (transport (fun A => A -> CarriersTermAlgebra C tt) isbin^
          (fun k => match k with
                    | inl (inr _) => L
                    | inr _ => R
                    | inl (inl e) => Empty_rec _ e
                    end)).

End single_sorted_equation_op.

Section single_sorted_equation_law.
  Context (Sym : Type) `{!IsHSet Sym} (Aris : Sym -> Type).

  Local Notation sσ := (Build_SingleSortedSignature Sym Aris).
  Local Notation var C n := (@var_term_algebra sσ C tt (fin_nat n)).
  Local Notation bin C m p := (binary_equation_op Sym Aris m p C).
  Local Notation una C i p := (unary_equation_op Sym Aris i p C).
  Local Notation nul C u p := (nullary_equation_op Sym Aris u p C).

  Definition equation_associativity
    (m : Symbol sσ) (isbin : Aris m = Fin 2)
    : Equation sσ :=
    let C := fun _ : Sort sσ => Fin 3 in
    let opm := bin C m isbin in
    let x n := var C n in
      {| context_equation := C
       ; left_equation := opm (opm (x 0) (x 1)) (x 2)
       ; right_equation := opm (x 0) (opm (x 1) (x 2))
      |}.

  Definition equation_commutativity
    (m : Symbol sσ) (isbin : Aris m = Fin 2)
    : Equation sσ :=
    let C := fun _ : Sort sσ => Fin 2 in
    let opm := bin C m isbin in
    let x n := var C n in
      {| context_equation := C
       ; left_equation := opm (x 0) (x 1)
       ; right_equation := opm (x 1) (x 0)
      |}.

  Definition equation_left_inverse
    (m : Symbol sσ) (isbin : Aris m = Fin 2)
    (i : Symbol sσ) (isuna : Aris i = Fin 1)
    (u : Symbol sσ) (isnul : Aris u = Fin 0)
    : Equation sσ :=
    let C := fun _ : Sort sσ => Fin 1 in
    let opm := bin C m isbin in
    let opi := una C i isuna in
    let opu := nul C u isnul in
    let x n := var C n in
      {| context_equation := C
       ; left_equation := opm (opi (x 0)) (x 0)
       ; right_equation := opu
      |}.

  Definition equation_right_inverse
    (m : Symbol sσ) (isbin : Aris m = Fin 2)
    (i : Symbol sσ) (isuna : Aris i = Fin 1)
    (u : Symbol sσ) (isnul : Aris u = Fin 0)
    : Equation sσ :=
    let C := fun _ : Sort sσ => Fin 1 in
    let opm := bin C m isbin in
    let opi := una C i isuna in
    let opu := nul C u isnul in
    let x n := var C n in
      {| context_equation := C
       ; left_equation := opm (x 0) (opi (x 0))
       ; right_equation := opu
      |}.

  Definition equation_left_unit
    (m : Symbol sσ) (isbin : Aris m = Fin 2)
    (u : Symbol sσ) (isnul : Aris u = Fin 0)
    : Equation sσ :=
    let C := fun _ : Sort sσ => Fin 1 in
    let opm := bin C m isbin in
    let opu := nul C u isnul in
    let x n := var C n in
      {| context_equation := C
       ; left_equation := opm opu (x 0)
       ; right_equation := x 0
      |}.

  Definition equation_right_unit
    (m : Symbol sσ) (isbin : Aris m = Fin 2)
    (u : Symbol sσ) (isnul : Aris u = Fin 0)
    : Equation sσ :=
    let C := fun _ : Sort sσ => Fin 1 in
    let opm := bin C m isbin in
    let opu := nul C u isnul in
    let x n := var C n in
      {| context_equation := C
       ; left_equation := opm (x 0) opu
       ; right_equation := x 0
      |}.

End single_sorted_equation_law.
