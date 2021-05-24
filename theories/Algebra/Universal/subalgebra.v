Require Import
  HoTT.Basics
  HoTT.TruncType
  HoTT.HProp
  HoTT.HSet
  HoTT.Types
  HoTT.Truncations
  HoTT.Algebra.Universal.Equations
  HoTT.Algebra.Universal.Isomorphism.

Local Open Scope Algebra_scope.

Section closed_under_op.
  Context `{Funext} {σ} (A : Algebra σ) (P : forall s, A s -> Type).

  (** Let [α : A s1 -> A s2 -> ... -> A sn -> A t] be an algebra
      operation. Then [P] satisfies [ClosedUnderOp α] iff
      for [x1 : A s1], [x2 : A s2], ..., [xn : A sn],

    <<
      P s1 x1 ∧ P s2 x2 ∧ ... ∧ P sn xn
    >>

    implies

    <<
      P t (α x1 x2 ... xn)
    >>
  *)

  Definition ClosedUnderOp {w : SymbolType σ} (α : Operation A w) : Type :=
    forall (a : DomOperation A w),
    (forall i, P (sorts_dom w i) (a i)) -> P (sort_cod w) (α a).

  Definition IsClosedUnderOps : Type
    := forall (u : Symbol σ), ClosedUnderOp u.#A.

End closed_under_op.

(** [P : forall s, A s -> Type] is a subalgebra predicate if it is closed
    under operations [IsClosedUnderOps A P] and [P s x] is an h-prop. *)

Section subalgebra_predicate.
  Context {σ} (A : Algebra σ) (P : forall s, A s -> Type).

  Class IsSubalgebraPredicate
    := Build_IsSubalgebraPredicate
    { hprop_subalgebra_predicate : forall s x, IsHProp (P s x);
      is_closed_under_ops_subalgebra_predicate : IsClosedUnderOps A P }.

  Global Instance hprop_is_subalgebra_predicate `{Funext}
    : IsHProp IsSubalgebraPredicate.
  Proof.
    apply hprop_allpath.
    intros [x1 x2] [y1 y2].
    by destruct (path_ishprop x1 y1), (path_ishprop x2 y2).
  Defined.
End subalgebra_predicate.

Global Arguments Build_IsSubalgebraPredicate {σ A P hprop_subalgebra_predicate}.

Global Existing Instance hprop_subalgebra_predicate.

(** The next section defines subalgebra. *)

Section subalgebra.
  Context
    {σ : Signature} (A : Algebra σ)
    (P : forall s, A s -> Type) `{!IsSubalgebraPredicate A P}.

(** The subalgebra carriers is the family of subtypes defined by [P]. *)

  Definition carriers_subalgebra : Carriers σ
    := fun (s : Sort σ) => {x | P s x}.

(** Let [α : A s1 -> ... -> A sn -> A t] be an operation and let [C :
    ClosedUnderOp A P α]. The corresponding subalgebra operation
    [op_subalgebra α C : (A&P) s1 -> ... -> (A&P) sn -> (A&P) t] is
    given by

    <<
      op_subalgebra α C (x1; p1) ... (xn; pn) =
        (α x1 ... xn; C x1 p1 x2 p2 ... xn pn).
    >>
*)

  Definition op_subalgebra {w : SymbolType σ} (α : Operation A w)
    (c : ClosedUnderOp A P α) : Operation carriers_subalgebra w :=
    fun a => (α (fun i => (a i).1); c (fun i => (a i).1) (fun i => (a i).2)).

(** The subalgebra operations [ops_subalgebra] are defined in terms of
    [op_subalgebra]. *)

  Definition ops_subalgebra (u : Symbol σ)
    : Operation carriers_subalgebra (σ u)
    := op_subalgebra u.#A (is_closed_under_ops_subalgebra_predicate A P u).

  Definition Subalgebra : Algebra σ
    := Build_Algebra carriers_subalgebra ops_subalgebra.
End subalgebra.

Infix "&&" := Subalgebra : Algebra_scope.

(** The following section defines the inclusion homomorphism
    [Homomorphism (A&P) A], and some related results. *)

Section hom_inc_subalgebra.
  Context
    {σ : Signature} (A : Algebra σ)
    (P : forall s, A s -> Type) `{!IsSubalgebraPredicate A P}.

  Definition def_inc_subalgebra (s : Sort σ) : (A && P) s -> A s
    := pr1.

  Global Instance is_homomorphism_inc_subalgebra
    : IsHomomorphism def_inc_subalgebra.
  Proof.
    intros u a. reflexivity.
  Defined.

  Definition hom_inc_subalgebra : Homomorphism (A && P) A
    := Build_Homomorphism def_inc_subalgebra.

  Global Instance is_embedding_inc_subalgebra
    : forall s, IsEmbedding (hom_inc_subalgebra s).
  Proof.
    intro s.
    apply isembedding_isinj_hset.
    intros a b p.
    by apply path_sigma_hprop.
  Qed.

  Lemma is_isomorphism_inc_improper_subalgebra
    (improper : forall s (x : A s), P s x)
    : IsIsomorphism hom_inc_subalgebra.
  Proof.
    intro s.
    refine (isequiv_adjointify _ (fun x => (x; improper s x)) _ _).
    - intro x. reflexivity.
    - intro x. by apply path_sigma_hprop.
  Qed.
End hom_inc_subalgebra.

Section path_map_term_algebra_subalgebra.
  Context
    `{Funext} {σ : Signature} (A : Algebra σ)
    (P : forall s, A s -> Type) `{!IsSubalgebraPredicate A P}
    (C : Carriers σ) `{forall s, IsHSet (C s)}
    (f : forall s, C s -> (A && P) s).

  Lemma path_map_term_algebra_subalgebra (t : Sort σ) (x : TermAlgebra C t)
    : map_term_algebra A (fun s => hom_inc_subalgebra A P s o f s) t x
      = hom_inc_subalgebra A P t (map_term_algebra (A && P) f t x).
  Proof.
    induction x.
    - reflexivity.
    - cbn. f_ap. funext Y. apply X.
  Defined.
End path_map_term_algebra_subalgebra.

Section model_subalgebra.
  Context
    `{Funext} {σ : Signature} (A : Algebra σ)
    (P : forall s, A s -> Type) `{!IsSubalgebraPredicate A P}
    {I : Type} (e : Equations σ I)
    {E : IsModelAlgebra A e}.

  Global Instance is_model_subalgebra
    : IsModelAlgebra (A && P) e.
  Proof.
    intros i f.
    apply (isinj_embedding (hom_inc_subalgebra A P _)); [exact _|].
    exact ((path_map_term_algebra_subalgebra A P _ _ _ _)^
           @ E i _
           @ path_map_term_algebra_subalgebra A P _ _ _ _).
  Qed.

  Definition model_subalgebra : ModelAlgebra e
    := Build_ModelAlgebra e (A && P).

End model_subalgebra.

(** The next section provides paths between subalgebras. These paths
    are convenient to have because the implicit type-class argument
    [IsClosedUnderOps] of [Subalgebra] is complicating things. *)

Section path_subalgebra.
  Context
    {σ : Signature} (A : Algebra σ)
    (P : forall s, A s -> Type) {CP : IsSubalgebraPredicate A P}
    (Q : forall s, A s -> Type) {CQ : IsSubalgebraPredicate A Q}.

  Lemma path_subalgebra `{Funext} (p : P = Q) : A && P = A && Q.
  Proof.
    by destruct p, (path_ishprop CP CQ).
  Defined.

  Lemma path_subalgebra_iff `{Univalence} (R : forall s x, P s x <-> Q s x)
    : A && P = A && Q.
  Proof.
    apply path_subalgebra.
    funext s x.
    apply (@path_universe _ _ _ (fst (R s x))).
    apply (equiv_equiv_iff_hprop _ _ (R s x)).
  Defined.
End path_subalgebra.
