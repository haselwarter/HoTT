(** This file defines the kernel of a homomorphism [cong_ker], the
    image of a homomorphism [in_image_hom], and it proves the first
    isomorphism theorem [isomorphic_first_isomorphism]. The first
    identification theorem [id_first_isomorphism] follows. *)

Require Import
  HoTT.Types
  HoTT.HSet
  HoTT.HIT.quotient
  HoTT.Classes.interfaces.canonical_names
  HoTT.Algebra.Universal.Isomorphism
  HoTT.Algebra.Universal.subalgebra
  HoTT.Algebra.Universal.quotient_algebra
  HoTT.Projective
  HoTT.Algebra.Universal.Equations.

Import carriers_quotient_algebra. (* TODO: Why is this necessary? *)

Local Open Scope Algebra_scope.

(** The following section defines the kernel of a homomorphism
    [cong_ker], and shows that it is a congruence.*)

Section cong_ker.
  Context
    `{Funext} {σ : Signature} {A B : Algebra σ}
    (f : forall s, A s -> B s) {IsH : IsHomomorphism f}.

  Definition cong_ker (s : Sort σ) : Relation (A s)
    := fun (x y : A s) => f s x = f s y.

  Global Instance equiv_rel_ker (s : Sort σ) : EquivRel (cong_ker s).
  Proof.
    repeat constructor.
    - intros x y. exact inverse.
    - intros x y z. exact concat.
  Qed.

  Global Instance ops_compatible_ker : OpsCompatible A cong_ker.
  Proof.
    intros u a b R.
    refine (IsH _ _ @ ap _ _ @ (IsH _ _)^).
    funext i.
    apply R.
  Qed.

  Global Instance is_congruence_ker : IsCongruence A cong_ker
    := Build_IsCongruence A cong_ker.

End cong_ker.

(*

Section in_image_hom.
  Context
    `{Funext} {σ : Signature} {A B : Algebra σ}
    (f : forall s, A s -> B s) {IsH : IsHomomorphism f}.

  Definition in_image_hom (s : Sort σ) (y : B s) : HProp
    := merely (hfiber (f s) y).

  Lemma closed_under_op_in_image_hom
    {w : SymbolType σ} `{ch : HasTrChoice 0 (Arity w)}
    (α : Operation A w) (β : Operation B w) (P : OpPreserving f α β)
    : ClosedUnderOp B in_image_hom β.
  Proof.
    intros b a.
    Print HasOChoice.
    pose proof (is_hsetprojective _ _ a) as a'.
    strip_truncations.
    apply tr.
    exists ((α (λ i, (a' i).1))).
    induction (P (λ i, (a' i).1))^.
    f_ap.
    funext i.
    apply a'.
  Qed.

  Lemma is_closed_under_ops_in_image_hom
    : IsClosedUnderOps B in_image_hom.
  Proof.
    intro u. eapply closed_under_op_in_image_hom, IsH.
  Qed.

  Global Instance is_subalgebra_predicate_in_image_hom
    : IsSubalgebraPredicate B in_image_hom
    := Build_IsSubalgebraPredicate is_closed_under_ops_in_image_hom.

End in_image_hom.

*)

(** The folowing section proves the first isomorphism theorem,
    [isomorphic_first_isomorphism] and the first identification
    theorem [id_first_isomorphism]. *)

Section first_isomorphism.
  Context
    `{Univalence} {σ} {A B : Algebra σ}
    {I : Type} (e : Equations σ I)
    `{EqB : !IsEquationalModel B e}
    (f : forall s, A s -> B s) {IsH : IsHomomorphism f}
    `{surj : !forall s, IsSurjection (f s)}.

(** The homomorphism [def_first_isomorphism] is informally given by

    <<
      def_first_isomorphism s (class_of _ x) := f s x.
    >>
*)

  Definition def_first_isomorphism
    : forall s : Sort σ, (e / cong_ker f) s -> B s.
  Proof.
    srefine (carriers_quotient_algebra_rec A (cong_ker f) e
              (fun s => B s)
              _ _ _ _ _).
    - intros s a. exact (f s a).
    - intros s a b r. apply r.
    - intros u α β. exact (u.#B β).
    - intros u a. symmetry. apply IsH.
    - intros. apply EqB.
  Defined.

(* Leave [is_homomorphism_first_isomorphism] opaque because
   [IsHomomorphism] is an hprop when [B] is a set algebra. *)

  Global Instance is_homomorphism_first_isomorphism
    : IsHomomorphism def_first_isomorphism.
  Proof.
    done.
  Defined.

  Definition hom_first_isomorphism
    : Homomorphism (e / cong_ker f) B
    := Build_Homomorphism def_first_isomorphism.

  Definition def_inv_first_isomorphism'
    : forall s : Sort σ, forall b : B s,
        {q : (e / cong_ker f) s |
          hexists (fun a : A s => {_ : class_quotient_algebra A (cong_ker f) e a = q | f s a = b})}.
  Proof.
    intros s b.
    assert (IsHProp 
      {q : (e / cong_ker f) s &
      hexists
        (fun a : A s =>
         {_ : class_quotient_algebra A (cong_ker f) e a = q & f s a = b})}).
    - apply ishprop_sigma_disjoint.
      intros r1 r2 E1 E2.
      strip_truncations.
      destruct E1 as [a1 [p1 q1]], E2 as [a2 [p2 q2]].
      refine (p1^ @ _ @ p2).
      apply path_class_quotient_algebra.
      exact (q1 @ q2^).
    - specialize (surj s b).
      destruct surj as [surj' _].
      generalize dependent surj'.
      cbn.
      refine (Trunc_rec _).
      intros [a p].
      exists (class_quotient_algebra A (cong_ker f) e a).
      apply tr.
      exists a.
      done.
  Defined.

  Definition def_inv_first_isomorphism
    : forall s : Sort σ, B s -> (e / cong_ker f) s
    := fun s b => (def_inv_first_isomorphism' s b).1.

  Global Instance is_homomorphism_inf_first_isomorphism
    : IsHomomorphism def_inv_first_isomorphism.
  Proof.
    intros u β.
    cbn.
    unfold def_inv_first_isomorphism.
    unfold def_inv_first_isomorphism'.
    cbn in *.
    set (surj0 := surj (sort_cod (σ u))).
    destruct surj0 as [surj' ps].
    generalize dependent surj'.
    refine (Trunc_ind _ _).
    intros [a p].
    intro ptr.
    cbn in *.
  Abort.


  Global Instance isequiv_first_isomorphism (s : Sort σ)
    : IsEquiv (hom_first_isomorphism s).
  Proof.
    refine (isequiv_adjointify
              (def_first_isomorphism s)
              (def_inv_first_isomorphism s)
              _ _).
    - intro b.
      unfold def_inv_first_isomorphism.
      unfold def_inv_first_isomorphism'.
      cbn.
      Locate Trunc_rec.
      cbn.
      set (surj0 := surj s b).
      destruct surj0 as [surj1 sp].
      generalize dependent sp.
      generalize dependent surj1.
      refine (Trunc_ind _ _).
      intros [a p].
      intros ptr.
      exact p.
    - cbn. intro q.
      generalize dependent s.
      refine (carriers_quotient_algebra_ind_hprop A (cong_ker f) e _ _ _).
      + intros s a. cbn.
        unfold def_inv_first_isomorphism.
        destruct (def_inv_first_isomorphism' s (f s a)) as [r p0].
        cbn in *.
        strip_truncations.
        destruct p0 as [a' [p1 p2]].
        refine (p1^ @ _).
        apply path_class_quotient_algebra.
        exact p2.
      + cbn. intros u α h.
        assert (IsHomomorphism def_inv_first_isomorphism) by admit.
        rewrite X.
        set (h' := path_forall _ _ h).
        rewrite h'.
        reflexivity.
  Abort.

  Global Instance isembedding_first_isomorphism (s : Sort σ)
    : IsEmbedding (hom_first_isomorphism s).
  Proof.
    apply isembedding_isinj_hset.
    intros p q.
    generalize dependent s.
    refine (carriers_quotient_algebra_ind_hprop A (cong_ker f) e _ _ _).
    - intros s a q.
      + refine (carriers_quotient_algebra_ind_hprop A (cong_ker f) e
                  (fun s q => forall (a : A s), _) _ _ s q a).
        * clear q a s.
          cbn. intros s a b p.
          apply path_class_quotient_algebra.
          exact p.
        * cbn in *.
          intros u α cs c p.
          assert ({β | forall i, α i = class_quotient_algebra A (cong_ker f) e (β i)}) by admit.
          destruct X as [β pβ].
          rewrite (path_forall _ _ pβ).
          rewrite path_ops_quotient_algebra.
          apply path_class_quotient_algebra.
          unfold cong_ker.
          cbn.
          rewrite p.
          rewrite IsH.
          f_ap.
          funext i.
          rewrite pβ.
          cbn.
          reflexivity.
  Abort.

(*
  Global Instance is_isomorphism_first_isomorphism
    : IsIsomorphism hom_first_isomorphism.
  Proof.
    intro s. apply isequiv_surj_emb; exact _.
  Qed.

  Theorem isomorphic_first_isomorphism
    : A / cong_ker f ≅ B & in_image_hom f.
  Proof.
    exact (Build_Isomorphic def_first_isomorphism).
  Defined.

(* The first identification theorem [id_first_isomorphism] is an
   h-prop, so we can leave it opaque. *)

  Corollary id_first_isomorphism : A / cong_ker f = B & in_image_hom f.
  Proof.
    exact (id_isomorphic isomorphic_first_isomorphism).
  Qed.
*)
End first_isomorphism.

(** The next section gives a specialization of the first isomorphism
    theorem, where the homomorphism is surjective. *)
(*
Section first_isomorphism_surjection.
  Context
    `{Univalence} {σ} {A B : Algebra σ}
    (f : forall s, A s -> B s) `{!IsHomomorphism f} {S : forall s, IsSurjection (f s)}
    `{!forall u, IsHSetProjective (Arity (σ u))}.

  Global Instance is_isomorphism_inc_first_isomorphism_surjection
    : IsIsomorphism (hom_inc_subalgebra B (in_image_hom f)).
  Proof.
    apply is_isomorphism_inc_improper_subalgebra. apply S.
  Qed.

(** The homomorphism [hom_first_isomorphism_surjection] is the
    composition of two isomorphisms, so it is an isomorphism. *)

  Definition hom_first_isomorphism_surjection
    : Homomorphism (A / cong_ker f) B
    := hom_compose
          (hom_inc_subalgebra B (in_image_hom f))
          (hom_first_isomorphism f).

  Theorem isomorphic_first_isomorphism_surjection : A / cong_ker f ≅ B.
  Proof.
    exact (Build_Isomorphic hom_first_isomorphism_surjection).
  Defined.

  Corollary id_first_isomorphism_surjection : (A / cong_ker f) = B.
  Proof.
    exact (id_isomorphic isomorphic_first_isomorphism_surjection).
  Qed.
End first_isomorphism_surjection.

(** The next section specializes the first isomorphism theorem to the
    case where the homomorphism is injective. It proves that an
    injective homomorphism is an isomorphism between its domain
    and its image. *)

Section first_isomorphism_inj.
  Context
    `{Univalence} {σ} {A B : Algebra σ}
    (f : forall s, A s -> B s) `{!IsHomomorphism f} (inj : forall s, isinj (f s))
    `{!forall u, IsHSetProjective (Arity (σ u))}.

  Global Instance is_isomorphism_quotient_first_isomorphism_inj
    : IsIsomorphism (hom_quotient (cong_ker f)).
  Proof.
    apply is_isomorphism_quotient. intros s x y p. apply inj, p.
  Qed.

(** The homomorphism [hom_first_isomorphism_inj] is the
    composition of two isomorphisms, so it is an isomorphism. *)

  Definition hom_first_isomorphism_inj
    : Homomorphism A (B & in_image_hom f)
    := hom_compose
          (hom_first_isomorphism f)
          (hom_quotient (cong_ker f)).

  Definition isomorphic_first_isomorphism_inj : A ≅ B & in_image_hom f
    := Build_Isomorphic hom_first_isomorphism_inj.

  Definition id_first_isomorphism_inj : A = B & in_image_hom f
    := id_isomorphic isomorphic_first_isomorphism_inj.

End first_isomorphism_inj.
*)
