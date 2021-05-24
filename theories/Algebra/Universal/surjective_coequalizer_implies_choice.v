Require Import
  HoTT.HSet
  HoTT.TruncType
  HoTT.Colimits.Quotient
  HoTT.Colimits.Quotient.Choice
  HoTT.HIT.epi
  HoTT.Classes.interfaces.canonical_names
  HoTT.Algebra.Universal.Isomorphism
  HoTT.Algebra.Universal.Congruence
  HoTT.Algebra.Universal.TermAlgebra.

Unset Elimination Schemes.

(* Any equivalence relations [R : forall s, Relation (C s)], [C : Carriers σ],
   can be extended to a congruence on the term algabra
   [forall s, Relation (CarriersTermAlgebra C s)]. *)

Module quotient_to_choice.

(* For the rest of the file we assume the [QuotientAlgebraStatement]. *)

Definition QuotientAlgebraStatement : Type :=
  forall σ (A : Algebra σ) (Φ : forall s, Relation (A s)) (isC : IsCongruence A Φ),
  exists (Q : Algebra σ) (q : A $-> Q) (_ : forall s (y : Q s), merely (hfiber (q s) y)),
  forall (B : Algebra σ),
  exists (e : (Q $-> B) <~> {f : A $-> B | HomCompatible Φ f}),
  forall (h : Q $-> B), (e h).1 = h $o q.

Section assume_quotient.
  Hypothesis (QStmt : QuotientAlgebraStatement).

Section quotient.
    Context
      {σ} {A : Algebra σ} (Φ : forall s, Relation (A s)) `{!IsCongruence A Φ}.
  
  (* The quotient A/Φ *)
  Definition Quot : Algebra σ := (QStmt _ _ Φ _).1.

  (* The quotient map A → A/Φ *)
  Definition quot : A $-> Quot := (QStmt _ _ Φ _).2.1.

  Definition issurjection_quot
    : forall s (y : Quot s), merely (hfiber (quot s) y)
    := (QStmt _ _ Φ _).2.2.1.

  Definition equiv_quot {B : Algebra σ}
    : (Quot $-> B) <~> {f : A $-> B | HomCompatible Φ f}
    := ((QStmt _ _ Φ _).2.2.2 B).1.

  Definition path_equiv_quot {B : Algebra σ} (h : Quot $-> B)
    : (equiv_quot h).1 = h $o quot
    := ((QStmt _ _ Φ _).2.2.2 B).2 h.

  Lemma compatible_quot {s} {x y : A s} (r : Φ s x y)
    : quot s x = quot s y.
  Proof.
    pose (path_equiv_quot (Id Quot)).
    set (p' := ap (fun f => def_homomorphism f s) p).
    set (px := ap (fun f => f x) p').
    refine (px^ @ _).
    set (py := ap (fun f => f y) p').
    refine (_ @ py).
    by apply (equiv_quot (Id Quot)).2.
  Qed.
End quotient.

(* Let [R : forall s, Relation (C s)] be equivalence relations, for [C : Carriers σ].
   The following section shows that there is an isomprphism between
   the quotient algebra of the term algebra and the term algebra of
   the set-quotient,

   <<
    TermAlgebra C / Ext R  ≅  TermAlgebra (λ s, C s / R)
   >>

   where [Ext R] is the extension of R from section [TermCongruenceExtension].
*)

Section isomorphic_quot_term.
  Context
    `{Funext} {σ} {C : Carriers σ} `{!forall s, IsHSet (C s)}
    (R : forall s, Relation (C s))
    `{!forall s, EquivRel (R s)} `{forall s, is_mere_relation (C s) (R s)}.

  Definition Ext : forall s, Relation (TermAlgebra C s)
    := (@ExtendRelTermAlgebra σ C R).

  Definition QuotT := Quot Ext.

  Definition TermQ := TermAlgebra (fun s => Quotient (R s)).

  Lemma map_term_algebra_is_compatible (s1 s2 : Sort σ) (p : s1 = s2)
    (S : CarriersTermAlgebra C s1)
    (T : CarriersTermAlgebra C s2)
    (E : ExtendDRelTermAlgebra R S T)
    : map_term_algebra TermQ
        (fun s (x : C s) => var_term_algebra _ _ (class_of (R s) x)) s2 (p # S) =
      map_term_algebra TermQ
        (fun s (x : C s) => var_term_algebra _ _ (class_of (R s) x)) s2 T.
  Proof.
    generalize dependent s2.
    induction S; intros s2 p T E.
    - destruct T.
      + destruct E as [p' E].
        induction p'.
        cbn.
        induction (hset_path2 idpath p).
        by induction (@qglue (C s) (R s) c c0).
      + elim E.
    - destruct T.
      + elim E.
      + destruct E as [p' E].
        induction p'.
        induction (hset_path2 idpath p).
        cbn.
        f_ap.
        funext i.
        apply (X i (sorts_dom (σ u) i) idpath).
        apply E.
  Qed.

  Definition quot_to_term : QuotT $-> TermQ.
  Proof.
    apply ((equiv_quot Ext)^-1).
    srefine (_; _).
    - exact (hom_term_algebra TermQ (fun s => var_term_algebra _ _ o class_of (R s))).
    - intros s' S T h. by apply (map_term_algebra_is_compatible s' s' idpath).
  Defined.

  Definition term_to_quot : TermQ $-> QuotT.
  Proof.
    apply (hom_term_algebra QuotT).
    intros s.
    srefine (Quotient_rec (R s) _ _ _).
    - intro x. apply quot. apply var_term_algebra. exact x.
    - intros x y h. cbn in *.
      apply compatible_quot.
      exists idpath. apply h.
  Defined.

  Lemma f_id_on_terms (D : Carriers σ) `{forall s, IsHSet (D s)}
    (f : TermAlgebra D $-> TermAlgebra D)
    (idT : forall s (x : D s), f s (var_term_algebra _ _ x) = var_term_algebra _ _ x)
    : forall s (x : TermAlgebra D s), f s x = x.
  Proof.
    assert (
      hom_term_algebra (TermAlgebra D) (fun s => f s o var_term_algebra _ _)
      = hom_term_algebra (TermAlgebra D)
          (fun s => homomorphism_id (TermAlgebra D) s o var_term_algebra _ _)) as p.
    - f_ap. funext s x. apply idT.
    - intros s x.
      set (pf := path_precomp_var_term_algebra_to_hom_term_algebra _ _ f).
      set (pi := path_precomp_var_term_algebra_to_hom_term_algebra _ _ (homomorphism_id (TermAlgebra D))).
      apply (ap (fun f => def_homomorphism f s x) (pf^ @ p @ pi)).
  Qed.

  Lemma equiv_quot_id
    : (equiv_quot Ext (Id QuotT)).1 = quot Ext.
  Proof.
    rewrite path_equiv_quot.
    apply path_homomorphism.
    by funext s x.
  Qed.

  Lemma path_termQ_var (s : Sort σ) (x : C s)
    : quot_to_term s (quot Ext s (var_term_algebra _ _ x))
      = var_term_algebra _ _ (class_of (R s) x).
  Proof.
    set (p := ap (fun g => def_homomorphism g s) (path_equiv_quot Ext quot_to_term)).
    cbn in p.
    set (p' := ap (fun g => g (var_term_algebra _ _ x)) p).
    cbn in p'.
    rewrite <- p'.
    unfold quot_to_term.
    rewrite (eisretr (equiv_quot Ext)).
    reflexivity.
  Qed.

  Lemma path_termQ_compose_var (s : Sort σ) (x : C s)
    : (term_to_quot $o
        (quot_to_term $o quot Ext)) s (var_term_algebra _ _ x)
      = quot Ext s (var_term_algebra _ _ x).
  Proof.
    cbn.
    by rewrite path_termQ_var.
  Qed.

  Lemma equiv_quot_compose
    : term_to_quot $o (quot_to_term $o quot Ext) = quot Ext.
  Proof.
    refine ((path_precomp_var_term_algebra_to_hom_term_algebra _ _ _)^
            @ _ @ path_precomp_var_term_algebra_to_hom_term_algebra _ _ _).
    simple refine (@moveR_equiv_M _ _ _ _ _ _ _).
    - exact (@isequiv_inverse
                (@TermAlgebra H σ C _ $-> QuotT)
                _ (precomp_var_term_algebra _ QuotT) _).
    - rewrite eissect.
      funext s x.
      apply path_termQ_compose_var.
  Qed.

  Lemma sect_term_to_quot
    : Id QuotT = term_to_quot $o quot_to_term.
  Proof.
    apply (equiv_inj (equiv_quot Ext)).
    apply path_sigma_hprop.
    refine (_ @ _ @ (path_equiv_quot Ext _)^).
    - refine (_ @ equiv_quot_compose^).
      apply equiv_quot_id.
    - apply path_homomorphism.
      funext s x.
      reflexivity.
  Qed.

  Global Instance is_isomorphism_quot_to_term
    : IsIsomorphism quot_to_term.
  Proof.
    intro s.
    srapply isequiv_adjointify.
    - apply term_to_quot.
    - intro x.
      apply (f_id_on_terms _ (homomorphism_compose quot_to_term term_to_quot)).
      intros s'.
      refine (Quotient_ind_hprop _ _ _).
      intro x'.
      cbn.
      set (p := ap (fun g => def_homomorphism g s') (path_equiv_quot Ext quot_to_term)).
      set (p' := ap (fun g => g (var_term_algebra _ _ x')) p).
      cbn in p'.
      rewrite <- p'.
      by rewrite (eisretr (equiv_quot Ext)).
    - intro x.
      pose (ap (fun f => def_homomorphism f s x) sect_term_to_quot) as sh.
      symmetry.
      apply sh.
  Qed.

  Lemma isomorphic_quot_term : Isomorphism QuotT TermQ.
  Proof.
    exact (Build_Isomorphism quot_to_term).
  Defined.
End isomorphic_quot_term.

(* Due to the isomorphism in the above section,
   the term algebra of the set-quotient and the same universal
   property as the quotient of the term algebra. This is the contents
   of the following section. *)

Section is_quotient_term.
  Context
    `{Funext} {σ} {C : Carriers σ} `{!forall s, IsHSet (C s)}
    (R : forall s, Relation (C s))
    `{!forall s, EquivRel (R s)} `{forall s, is_mere_relation (C s) (R s)}.

  (* The "quotient map". *)

  Definition termQ : TermAlgebra C $-> TermQ R
    := quot_to_term R $o quot (Ext R).

  Lemma equiv_termQ {B : Algebra σ}
    : (TermQ R $-> B)
      <~> {f : TermAlgebra C $-> B | HomCompatible (Ext R) f}.
  Proof.
    srefine (HoTT.Basics.Equivalences.equiv_compose (equiv_quot (Ext R)) _);
        try exact _.
    - intro h. exact (h $o quot_to_term R).
    - srapply isequiv_adjointify.
      + intro h. exact (h $o homomorphism_inv (quot_to_term R)).
      + cbn. intro h.
        apply path_homomorphism.
        funext s x.
        cbn.
        by rewrite eissect.
      + cbn. intro h.
        apply path_homomorphism.
        funext s x.
        cbn.
        by rewrite eisretr.
  Defined.
  
  Lemma path_equiv_termQ {B : Algebra σ} (h : TermQ R $-> B)
    : (equiv_termQ h).1 = h $o termQ.
  Proof.
    apply path_homomorphism.
    funext s x.
    cbn.
    rewrite path_equiv_quot.
    cbn.
    reflexivity.
  Qed.

  Lemma issurjection_termQ
    : forall s (y : TermQ R s), merely (hfiber (termQ s) y).
  Proof.
    intros s y.
    pose proof (issurjection_quot (Ext R) s ((quot_to_term R s)^-1 y)) as S.
    strip_truncations.
    apply tr.
    destruct S as [t T].
    exists t.
    cbn.
    apply (equiv_inj (quot_to_term R s)^-1).
    by rewrite eissect.
  Qed.
End is_quotient_term.

(* Now we can choose representatives from equivalence classes,
   as shown in the next section. *)

Section choose_representatives.
  Lemma cop_op_to_dom_op' `{Funext} {σ} {C : Carriers σ} `{!forall s, IsHSet (C s)}
    (R : forall s, Relation (C s)) `{!forall s, is_mere_relation (C s) (R s)}
    `{!forall s, EquivRel (R s)} (s : Sort σ) (T : TermAlgebra C s)
    (u : Symbol σ) (a : DomOperation (TermAlgebra (fun s => Quotient (R s))) (σ u))
    (p : ExtendDRelTermAlgebra (fun s => paths) (termQ R s T) (ops_term_algebra _ _ a))
    : exists (f : DomOperation (TermAlgebra C) (σ u)),
        ExtendDRelTermAlgebra (fun s => paths) T (ops_term_algebra _ _ f).
  Proof.
    generalize dependent u.
    induction T.
    - intros. cbn in *.
      rewrite path_termQ_var in p.
      elim p.
    - intros.
      rewrite is_homomorphism in p.
      cbn in p.
      destruct p as [p P].
      induction p.
      exists c.
      apply reflexive_extend_rel_term_algebra.
      intros s x.
      reflexivity.
  Qed.

  Lemma cop_op_to_dom_op `{Funext} {σ} {C : Carriers σ} `{!forall s, IsHSet (C s)}
    (R : forall s, Relation (C s)) `{!forall s, is_mere_relation (C s) (R s)}
    `{!forall s, EquivRel (R s)} (u : Symbol σ) (T : TermAlgebra C (sort_cod (σ u)))
    (a : DomOperation (TermAlgebra (fun s => Quotient (R s))) (σ u))
    (p : termQ R (sort_cod (σ u)) T = ops_term_algebra _ _ a)
    : exists (f : DomOperation (TermAlgebra C) (σ u)),
        T = ops_term_algebra _ _ f.
  Proof.
    apply reflexive_extend_path_term_algebra_path in p.
    srefine (_ ; _).
    - apply (cop_op_to_dom_op' R (sort_cod (σ u)) T u a p).
    - apply path_extend_path_term_algebra.
      apply (cop_op_to_dom_op' R (sort_cod (σ u)) T u a p).
  Qed.

  Lemma cod_var_to_dom_var' `{Funext} {σ} {C : Carriers σ} `{!forall s, IsHSet (C s)}
    (R : forall s, Relation (C s)) `{!forall s, is_mere_relation (C s) (R s)}
    `{!forall s, EquivRel (R s)}
    (s1 s2 : Sort σ) (T : TermAlgebra C s1) (t : Quotient (R s2))
    (p : ExtendDRelTermAlgebra (fun s => paths)  (termQ R s1 T) (var_term_algebra _ _ t))
    : exists y : C s1, T = var_term_algebra _ _ y.
  Proof.
    generalize dependent s2.
    induction T.
    - intros. exists c. reflexivity.
    - intros. rewrite is_homomorphism in p. elim p.
  Defined.

  Lemma fun_cod_var_to_fun_dom_var' `{Funext} {σ} {X}
    {C : Carriers σ} `{!forall s, IsHSet (C s)}
    (R : forall s, Relation (C s)) `{!forall s, is_mere_relation (C s) (R s)}
    `{!forall s, EquivRel (R s)} (k : X -> Sort σ)
    (T : forall x : X, TermAlgebra C (k x))
    (t : forall x : X, Quotient (R (k x)))
    (p : forall x : X,
          ExtendDRelTermAlgebra (fun s => paths)  (termQ R (k x) (T x))
          (var_term_algebra _ _ (t x)))
    : exists f : forall x : X, C (k x),
      forall x : X, T x = var_term_algebra _ _ (f x).
  Proof.
    srefine (_ ; _).
    - intro x. apply (cod_var_to_dom_var' R (k x) (k x) (T x) (t x) (p x)).
    - intro x.
      destruct ((cod_var_to_dom_var' R (k x) (k x) (T x) (t x) (p x))) as [y p'].
      exact p'.
  Defined.

  Lemma fun_cod_var_to_fun_dom_var `{Funext} {σ} {X}
    {C : Carriers σ} `{!forall s, IsHSet (C s)}
    (R : forall s, Relation (C s)) `{!forall s, is_mere_relation (C s) (R s)}
    `{!forall s, EquivRel (R s)} (k : X -> Sort σ)
    (T : forall x : X, TermAlgebra C (k x)) (t : forall x, Quotient (R (k x)))
    (p : forall x : X, termQ R (k x) (T x) = var_term_algebra _ _ (t x))
    : exists f : forall x : X, C (k x),
      forall x : X, T x = var_term_algebra _ _ (f x).
  Proof.
    set (p' := fun x => reflexive_extend_path_term_algebra_path (p x)).
    exact (fun_cod_var_to_fun_dom_var' R k T t p').
  Defined.

  Lemma choose_sum `{Univalence} {X : Type} `{!IsHSet X} {Y : X + Unit -> Type}
    `{!forall x, IsHSet (Y x)} (R : forall x, Relation (Y x))
    `{!forall x, is_mere_relation (Y x) (R x)} `{!forall x, EquivRel (R x)}
    : forall g' : forall x : X, Quotient (R (inl x)),
      hexists (fun g : (forall x : X, Y (inl x)) =>
               forall x, class_of (R (inl x)) (g x) = g' x).
  Proof.
    intro g'.
    set (σ := Build_Signature (X + Unit) Unit
                (fun _ : Unit => Build_SymbolType X inl (inr tt))).
    set (f' := fun x => @var_term_algebra σ (fun x => Quotient (R x)) (inl x) (g' x)).
    set (op' := @ops_term_algebra σ (fun x => Quotient (R x)) tt f').
    pose proof (@issurjection_termQ _ σ Y _ R _ _ (inr tt) op') as S.
    strip_truncations.
    apply tr.
    destruct S as [t T].
    destruct (@cop_op_to_dom_op _ σ Y _ R _ _ tt t f' T) as [g p].
    induction p^.
    rewrite (is_homomorphism (@termQ _ σ Y _ R _ _)) in T.
    pose (@isinj_ops_term_algebra _ σ (fun x => Quotient (R x)) tt) as isi.
    set (T' :=
      isi (fun x => @quot_to_term _ σ Y _ R _ _ (inl x)
                      (quot (@Ext  _ σ Y _ R) (inl x) (g x))) f' T).
    set (T'' := fun x => ap (fun f => f x) T').
    set (S := @fun_cod_var_to_fun_dom_var _ σ X Y _ R _ _ inl g g' T'').
    destruct S as [g0 gp].
    exists g0.
    intro x.
    cbn in T''.
    specialize (T'' x).
    rewrite (gp x) in T''.
    rewrite path_termQ_var in T''.
    by apply isinj_var_term_algebra in T''.
  Qed.

  Definition IncFam {X} (Y : X -> Type) (x' : X + Unit) : Type
    := match x' with
       | inl x => Y x
       | inr tt => Unit
       end.

  Global Instance ishset_inc_fam {X} (Y : X -> Type) `{!forall x, IsHSet (Y x)}
    (x' : X + Unit)
    : IsHSet (IncFam Y x').
  Proof.
    destruct x'.
    - exact _.
    - destruct u. exact _.
  Defined.

  Definition IncRel {X} {Y : X -> Type} (R : forall x, Relation (Y x))
    : forall x' : X + Unit, Relation (IncFam Y x')
    := fun x' =>
         match x' as x' return Relation (IncFam Y x') with
         | inl x => R x
         | inr tt => fun _ _ => Unit
         end.

  Global Instance equivrel_inc_rel {X : Type} {Y : X -> Type}
    (R : forall x, Relation (Y x)) `{!forall x, EquivRel (R x)}
    : forall x', EquivRel (IncRel R x').
  Proof.
    intros []; constructor.
    - apply H.
    - apply H.
    - apply H.
    - destruct u. constructor.
    - destruct u. constructor.
    - destruct u. constructor.
  Defined.

  Global Instance is_mere_relation_inc_rel {X : Type} {Y : X -> Type}
    (R : forall x, Relation (Y x)) `{!forall x, is_mere_relation (Y x) (R x)}
    : forall x', is_mere_relation (IncFam Y x') (IncRel R x').
  Proof.
    intros [].
    - exact _.
    - destruct u. exact _.
  Defined.

  Theorem choose_representatives `{Univalence}
    (X : Type) `{!IsHSet X} (Y : X -> Type)
    `{!forall x, IsHSet (Y x)} (R : forall x, Relation (Y x))
    `{!forall x, is_mere_relation (Y x) (R x)} `{!forall x, EquivRel (R x)}
    : forall g' : forall x : X, Quotient (R x),
      merely (exists g : (forall x : X, Y x), forall x, class_of (R x) (g x) = g' x).
  Proof.
    About choose_sum.
    intro g'.
    exact (@choose_sum _ X _ (IncFam Y) _ (IncRel R) _ _ g').
  Qed.
End choose_representatives.

(* Then we also have the axiom of choice: *)

Section axiom_of_choice.
  Context `{Univalence}
    {A : Type} `{!IsHSet A} {B : A -> Type} `{!forall a, IsHSet (B a)}.

  Corollary axiom_of_choice : (forall a, merely (B a)) -> merely (forall a, B a).
  Proof.
    intro i.
    apply has_tr0_choice_quotientchoice; try exact _.
    - intros Y sY R pR Rf Sm Tn f.
      assert (forall x, EquivRel (R x)) as eR.
      + intro x. constructor; exact _.
      + apply (choose_representatives A Y R).
    - exact i.
  Qed.
End axiom_of_choice.

End assume_quotient.
End quotient_to_choice.
