Require Export HoTT.Algebra.Universal.Congruence.

Require Import
  HoTT.Basics
  HoTT.Types
  HoTT.HProp
  HoTT.HSet
  HoTT.HProp
  HoTT.Truncations
  HoTT.TruncType
  HoTT.Classes.interfaces.canonical_names
  HoTT.Algebra.Universal.Isomorphism
  HoTT.Algebra.Universal.Equations.

Local Open Scope Algebra_scope.

Definition param_map_term_algebra {σ} {C : Carriers σ} (A : Algebra σ)
  (f : forall t, C t -> A t) (P : forall (s : Sort σ), A s -> Type)
  (F : forall t c, P t (f t c))
  (os : forall (u : Symbol σ)
          (a : DomOperation A (σ u)),
        (forall X, P _ (a X)) -> P _ (u.#A a))
  (s : Sort σ) (E : CarriersTermAlgebra C s)
  : P s (map_term_algebra A f s E)
  := CarriersTermAlgebra_ind C
       (fun s T => P s (map_term_algebra A f s T)) F
       (fun u a r => os u (fun i => map_term_algebra A f _ (a i)) r) s E.

Example param_map_term_algebra_is_generalization {σ} {C : Carriers σ}
  (A : Algebra σ) (f : forall t, C t -> A t)
  : param_map_term_algebra A f (fun s _ => A s) f (fun u _ => u.#A)
    = map_term_algebra A f.
Proof.
  reflexivity.
Defined.

Module carriers_quotient_algebra.

  Private Inductive carriers_quotient_algebra {σ : Signature}
    (A : Algebra σ) (Φ : forall s, Relation (A s))
    {I : Type} (e : Equations σ I)
  : Carriers σ :=
  | class_quotient_algebra :
      forall {s : Sort σ}, A s -> carriers_quotient_algebra A Φ e s
  | ops_quotient_algebra : forall (u : Symbol σ),
      DomOperation (carriers_quotient_algebra A Φ e) (σ u) ->
      carriers_quotient_algebra A Φ e (sort_cod (σ u)).

Section context_carriers_quotient_algebra.
  Context
    {σ : Signature} (A : Algebra σ) (Φ : forall s, Relation (A s))
    {I : Type} (e : Equations σ I).

  Axiom hset_quotient_algebra
    : forall (s : Sort σ), IsHSet (carriers_quotient_algebra A Φ e s).

  Global Existing Instance hset_quotient_algebra.

  Definition QuotientAlgebra : Algebra σ
    := Build_Algebra (carriers_quotient_algebra A Φ e)
                     (ops_quotient_algebra A Φ e).

  Local Notation "Ψ '.[' x ]" := (class_quotient_algebra _ Ψ e x) (at level 3, format "Ψ '.[' x ]").

  Axiom path_class_quotient_algebra
  : forall {s} (x y : A s), Φ s x y -> Φ.[x] = Φ.[y].

  Axiom path_ops_quotient_algebra
    : forall (u : Symbol σ) (a : DomOperation A (σ u)),
      ops_quotient_algebra A Φ e u (fun i => Φ.[a i]) = Φ.[u.#A a].

  Axiom equations_quotient_algebra
    : forall (i : I) (f : forall t, context_equation (e i) t ->
                          carriers_quotient_algebra A Φ e t),
      map_term_algebra QuotientAlgebra f _ (left_equation (e i))
      = map_term_algebra QuotientAlgebra f _ (right_equation (e i))
      :> QuotientAlgebra (sort_equation (e i)).

  Fixpoint carriers_quotient_algebra_ind
    (P : forall (s : Sort σ), carriers_quotient_algebra A Φ e s -> Type)
    `{forall (s : Sort σ) (Q : carriers_quotient_algebra A Φ e s), IsHSet (P s Q)}
    (cas : forall (s : Sort σ) (x : A s), P s Φ.[x])
    (pcas : forall (s : Sort σ) (x y : A s) (R : Φ s x y),
            path_class_quotient_algebra x y R # cas s x = cas s y)
    (ops : forall (u : Symbol σ)
             (a : DomOperation (carriers_quotient_algebra A Φ e) (σ u))
             (aP : forall I, P (sorts_dom (σ u) I) (a I)),
           P (sort_cod (σ u)) (ops_quotient_algebra A Φ e u a))
    (pops : forall (u : Symbol σ) (a : DomOperation A (σ u)),
            path_ops_quotient_algebra u a
              # ops u (fun i => Φ.[a i]) (fun i => cas (sorts_dom (σ u) i) (a i))
            = cas (sort_cod (σ u)) (u.#A a))
    (pes : forall (i : I)
             (f : forall t, context_equation (e i) t ->
                       carriers_quotient_algebra A Φ e t)
             (F : forall t c, P t (f t c)),
      equations_quotient_algebra i f #
        param_map_term_algebra QuotientAlgebra f P F ops
          (sort_equation (e i)) (left_equation (e i))
      = param_map_term_algebra QuotientAlgebra f P F ops
          (sort_equation (e i)) (right_equation (e i)))
    (s : Sort σ) (Q : carriers_quotient_algebra A Φ e s)
    : P s Q
    := match Q with
       | class_quotient_algebra s x =>
          cas s x
       | ops_quotient_algebra u a =>
          ops u a (fun i => carriers_quotient_algebra_ind P cas pcas
                             ops pops pes (sorts_dom (σ u) i) (a i))
       end.

End context_carriers_quotient_algebra.
End carriers_quotient_algebra.

Import carriers_quotient_algebra.

Notation "e / Φ" := (QuotientAlgebra _ Φ e) : Algebra_scope.

Lemma compute_op_quotient {σ} (A : Algebra σ) (Φ : forall s, Relation (A s))
  `{!IsCongruence A Φ} (u : Symbol σ) (a : DomOperation A (σ u))
  {I : Type} (e : Equations σ I)
  : (u.#(e/Φ)) (fun i => class_quotient_algebra A Φ e (a i))
    = class_quotient_algebra A Φ e (u.#A a).
Proof.
  apply path_ops_quotient_algebra.
Defined.

Section is_equational_quotient_algebra.
  Context {σ : Signature} (A : Algebra σ) (Φ : forall s, Relation (A s))
          {I : Type} (e : Equations σ I).

  Global Instance is_equational_quotient_algebra
    : IsEquationalModel (e/Φ) e.
  Proof.
    intros i f. apply equations_quotient_algebra.
  Defined.

End is_equational_quotient_algebra.

(** The following section defines the quotient homomorphism
    [hom_quotient : A $-> A/Φ]. *)

Section hom_quotient.
  Context
    `{Funext} {σ} {A : Algebra σ}
    (Φ : forall s, Relation (A s)) `{!IsCongruence A Φ}
    {I : Type} (e : Equations σ I)  {IsA : IsEquationalModel A e}.

  Definition def_hom_quotient : forall (s : Sort σ), A s -> (e/Φ) s :=
    fun s x => class_quotient_algebra A Φ e x.

  Global Instance is_homomorphism_quotient
    : IsHomomorphism def_hom_quotient.
  Proof.
    intros u a. symmetry. apply compute_op_quotient. exact _.
  Defined.

  Definition hom_quotient : A $-> e/Φ
    := Build_Homomorphism def_hom_quotient.

  Lemma isepi_quotient {B : Algebra σ} (f g : e/Φ $-> B)
    (p : f $o hom_quotient = g $o hom_quotient)
    : f = g.
  Proof.
    apply path_homomorphism.
    funext s x.
    generalize dependent s.
    srefine (carriers_quotient_algebra_ind A Φ e
              (fun s Q => f s Q = g s Q) _ _ _ _ _).
    - intros; cbn in *.
      apply (ap (fun h => def_homomorphism h s x) p).
    - intros. cbn. apply hset_path2.
    - intros; cbn in *.
      do 2 rewrite is_homomorphism.
      f_ap.
      funext i.
      apply aP.
    - cbn in *. intros. apply hset_path2.
    - cbn in *. intros. apply hset_path2.
  Qed.
End hom_quotient.

(** This section develops the universal mapping property
    [ump_quotient_algebra] of the quotient algebra. *)

Section ump_quotient_algebra.
  Context
    `{Univalence} {σ} {A B : Algebra σ}
    (Φ : forall s, Relation (A s)) `{!IsCongruence A Φ}
    {I : Type} (e : Equations σ I)
    {IsA : IsEquationalModel A e} {IsB : IsEquationalModel B e}.

(** In the nested section below we show that if [f : A $-> B]
    maps elements related by [Φ] to equal elements, there is a
    [A/Φ $-> B] out of the quotient algebra satisfying
    [compute_quotient_algebra_mapout] below. *)

  Section quotient_algebra_mapout.
    Context
      (f : A $-> B)
      (R : forall s (x y : A s), Φ s x y -> f s x = f s y).

    Definition def_hom_quotient_algebra_mapout
      : forall (s : Sort σ), (e/Φ) s -> B s.
    Proof.
      srefine (carriers_quotient_algebra_ind A Φ e
                (fun s _ => B s) _ _ _ _ _).
      - cbn. intros s x. exact (f s x).
      - cbn. intros s x y r.
        rewrite transport_const.
        by apply R.
      - cbn. intros u a x.
        apply u.#B.
        exact x.
      - cbn. intros u a.
        rewrite transport_const.
        symmetry.
        apply is_homomorphism.
      - cbn. intros i f' F'.
        rewrite transport_const.
        apply IsB.
    Defined.

    Global Instance is_homomorphism_quotient_algebra_mapout
      : IsHomomorphism def_hom_quotient_algebra_mapout.
    Proof.
      easy.
    Qed.

    Definition hom_quotient_algebra_mapout
      : e/Φ $-> B
      := Build_Homomorphism def_hom_quotient_algebra_mapout.

(** The computation rule for [hom_quotient_algebra_mapout] is

    <<
      hom_quotient_algebra_mapout s (class_of (Φ s) x) = f s x.
    >>
*)

    Lemma compute_quotient_algebra_mapout
      : forall (s : Sort σ) (x : A s),
        hom_quotient_algebra_mapout s (class_quotient_algebra A Φ e x) = f s x.
    Proof.
      reflexivity.
    Qed.

  End quotient_algebra_mapout.

  Definition hom_quotient_algebra_mapin (g : e/Φ $-> B)
    : A $-> B
    := g $o hom_quotient Φ e.

  Lemma ump_quotient_algebra_lr :
    {f : A $-> B | forall s (x y : A s), Φ s x y -> f s x = f s y}
    -> e/Φ $-> B.
  Proof.
    intros [f P]. exists (hom_quotient_algebra_mapout f P). exact _.
  Defined.

  Lemma ump_quotient_algebra_rl :
    (e/Φ $-> B) ->
    {f : A $-> B | forall s (x y : A s), Φ s x y -> f s x = f s y}.
  Proof.
    intro g.
    exists (hom_quotient_algebra_mapin g).
    intros s x y E.
    cbn.
    exact (transport (fun z => g s (class_quotient_algebra A Φ e x) = g s z)
            (path_class_quotient_algebra A Φ e _ _ E) idpath).
  Defined.

(** The universal mapping property of the quotient algebra. For each
    homomorphism [f : A $-> B], mapping elements related by
    [Φ] to equal elements, there is a unique homomorphism
    [g : A/Φ $-> B] satisfying

    <<
      f = hom_compose g (hom_quotient Φ).
    >>
*)

  Lemma ump_quotient_algebra
    : {f : A $-> B | forall s (x y : A s), Φ s x y -> f s x = f s y}
     <~>
      (e/Φ $-> B).
  Proof.
    apply (equiv_adjointify
             ump_quotient_algebra_lr ump_quotient_algebra_rl).
    - intro g.
      apply path_homomorphism.
      funext s a.
      generalize dependent s.
      srefine (carriers_quotient_algebra_ind A Φ e
                (fun s a => ump_quotient_algebra_lr (_ g) s a = g s a) _ _ _ _ _).
      + cbn. intros s x. reflexivity.
      + intros. apply hset_path2.
      + cbn. intros u a h.
        rewrite is_homomorphism.
        f_ap.
        funext i.
        apply h.
      + intros. apply hset_path2.
      + intros. apply hset_path2.
    - intro F.
      apply path_sigma_hprop.
      by apply path_homomorphism.
  Defined.
End ump_quotient_algebra.

(** If [Φ s x y] implies [x = y], then homomorphism [hom_quotient Φ]
    is an isomorphism. *)

Global Instance is_isomorphism_quotient `{Univalence}
  {σ : Signature} {A : Algebra σ} (Φ : forall s, Relation (A s))
  {I : Type} (e : Equations σ I) {IsA : IsEquationalModel A e}
  `{!IsCongruence A Φ} (P : forall s x y, Φ s x y -> x = y)
  : IsIsomorphism (hom_quotient Φ e).
Proof.
  intro s.
  srefine (isequiv_adjointify _ _ _ _).
  - generalize dependent s.
    srefine (carriers_quotient_algebra_ind A Φ e (fun s _ => A s) _ _ _ _ _).
    + intros s x. exact x.
    + intros. cbn. rewrite transport_const. apply P. exact R.
    + cbn. intros u x h. apply u.#A. exact h.
    + intros. cbn. rewrite transport_const. reflexivity.
    + cbn. intros. rewrite transport_const. apply IsA.
  - intro x.
    generalize dependent s.
    srefine (carriers_quotient_algebra_ind A Φ e _ _ _ _ _ _).
    + cbn. intros s x. reflexivity.
    + intros. apply hset_path2.
    + cbn. intros u a h.
      rewrite is_homomorphism_quotient; [| exact _].
      f_ap.
      funext i.
      apply h.
    + intros. apply hset_path2.
    + intros. apply hset_path2.
  - reflexivity.
Qed.
