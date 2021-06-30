Require Export Classes.interfaces.abstract_algebra.

Require Import
  HoTT.HSet
  HoTT.Spaces.Finite
  HoTT.Algebra.Universal.Isomorphism
  HoTT.Algebra.Universal.Equations
  HoTT.Algebra.Universal.prod_algebra
  HoTT.Algebra.Universal.subalgebra
  HoTT.Algebra.Universal.quotient_algebra
  HoTT.Algebra.Universal.free_algebra.

Local Open Scope mc_mult_scope.
Local Open Scope Algebra_scope.

(* This definition of group is taken from HoTT.Algebra.Groups.Group *)

Record Group := {
  group_type : Type;
  group_sgop : SgOp group_type;
  group_unit : MonUnit group_type;
  group_inverse : Negate group_type;
  group_isgroup : IsGroup group_type;
}.

Arguments group_sgop {_}.
Arguments group_unit {_}.
Arguments group_inverse {_}.
Arguments group_isgroup {_}.

Coercion group_type : Group >-> Sortclass.

(* NOTE: with this below we should be able to use notations [mon_unit], [_ * _], [- _], but I have not tested it. *)
Global Existing Instances group_sgop group_unit group_inverse group_isgroup.

Variant GroupSymbol :=
  group_sgop_sym | group_unit_sym | group_inverse_sym.

Lemma equiv_fin3_group_symbol : Fin 3 <~> GroupSymbol.
Proof.
  srapply equiv_adjointify.
  - FinInd.
    + exact group_sgop_sym.
    + exact group_unit_sym.
    + exact group_inverse_sym.
  - intros [].
    + exact (fin_nat 0).
    + exact (fin_nat 1).
    + exact (fin_nat 2).
  - intros []; reflexivity.
  - FinInd; reflexivity.
Defined.

Global Instance dec_paths_group_symbol
  : DecidablePaths GroupSymbol.
Proof.
  apply (decidablepaths_equiv (Fin 3) equiv_fin3_group_symbol).
  exact _.
Qed.

Definition group_symbol_arity := (fun s => match s with
              | group_sgop_sym => Fin 2
              | group_unit_sym => Fin 0
              | group_inverse_sym => Fin 1
              end).

Definition group_signature : Signature :=
  Build_SingleSortedSignature GroupSymbol group_symbol_arity.

Definition AlgebraGroup : Type := Algebra group_signature.

Variant GroupEquation :=
| group_eq_assoc
| group_eq_left_unit
| group_eq_right_unit
| group_eq_left_inverse
| group_eq_right_inverse.


Definition group_equations : Equations group_signature GroupEquation.
Proof.
  constructor. induction 1.
  - exact (equation_associativity _ _ group_sgop_sym idpath).
  - exact (equation_left_unit _ _ group_sgop_sym idpath
            group_unit_sym idpath).
  - exact (equation_right_unit _ _ group_sgop_sym idpath
            group_unit_sym idpath).
  - exact (equation_left_inverse _ _ group_sgop_sym idpath
            group_inverse_sym idpath group_unit_sym idpath).
  - exact (equation_right_inverse _ _ group_sgop_sym idpath
            group_inverse_sym idpath group_unit_sym idpath).
Defined.

Definition ModelAlgebraGroup : Type := ModelAlgebra group_equations.

Definition Fin1_rec {P : Type} (p : P) : Fin 1 -> P :=
  fun x => match x with inr tt => p | inl z => Empty_rec P z end.

Definition Fin1_ind {P : Fin 1 -> Type} (p : P (inr tt)) (x : Fin 1) : P x :=
  match x with inr tt => p | inl z => Empty_rec _ z end.

Definition Fin2_rec {P : Type} (p1 p2 : P) (x : Fin 2) : P :=
  match x with
  | inl x => Fin1_rec p1 x
  | inr tt => p2
  end.

Definition Fin3_rec {P : Type} (p1 p2 p3 : P) (x : Fin 3) : P :=
  match x with
  | inl x => Fin2_rec p1 p2 x
  | inr tt => p3
  end.

Local Definition T (uaG : ModelAlgebraGroup) := model_algebra uaG tt.

(* Local Definition g_op {uaG : ModelAlgebraGroup} : SgOp (T uaG) *)
(*   := *)
(*     (fun x1 x2 => *)
(*        (operations uaG group_sgop_sym) *)
(*          ltac:(intros [[empty|tt]|tt] ; *)
(*               [ elim empty | exact x1 | exact x2 ])). *)

Local Definition g_op {uaG : ModelAlgebraGroup} : SgOp (T uaG)
  := fun x y => operations uaG group_sgop_sym (Fin2_rec x y).

Local Definition g_unit {uaG : ModelAlgebraGroup} : MonUnit (T uaG) :=
  operations uaG group_unit_sym (fun F => ltac:(case F)).

Local Definition g_inverse {uaG : ModelAlgebraGroup} : (Negate (T uaG)) :=
    fun x =>
               operations uaG group_inverse_sym
                          ltac:(intros [F|tt] ; [elim F | exact x ]).

(* destruct completely a term of type Fin k *)
Ltac caseFin' x :=
  let t := type of x in
  lazymatch t with
  | Empty => destruct x
  | ?k + Unit =>
    let x' := fresh "x" in
    let h := fresh "eq_x" in
    destruct x as [x'|[]] ; [caseFin' x'|]
  end.

Definition equational_context_vars_3 (uaG : ModelAlgebraGroup) (x y z : T uaG) : (forall s:Unit, Fin 3 -> uaG s).
  intros s [[[e|tt]|tt]|tt].
  - elim e.
  - destruct s, tt. exact x.
  - destruct s, tt. exact y.
  - destruct s, tt. exact z.
Defined.

Definition equational_context_vars_1 (uaG : ModelAlgebraGroup) (x : T uaG) : (forall s:Unit, Fin 1 -> uaG s).
  intros s [e|tt].
  - elim e.
  - destruct s, tt. exact x.
Defined.

Section RefactorEquationalProofs.

(* Commented out is an attempt at factoring out the construction of Associative in the sense of Classes *)
(* from InterpEquation equation_associativity. It is currently stuck because unlike the concrete *)
(* case of groups (which use idpath), the equation `isbin : Aris m = Fin 2` does not compute, and *)
(* we cannot rewrite along it, possibly because of the following related Coq bugs:
   - https://github.com/coq/coq/issues/6623
     Dan Grayson experiencing a similar issue in UniMath with rewrite.
   - https://github.com/coq/coq/issues/14582
     Inverting the orientation of the `isbin` equation leads to an universe inconsistency.
 *)

  Definition f'
             (Sym : Type)
             `{!IsHSet Sym}
             (Aris : Sym -> Type)
             (A : Algebra (Build_SingleSortedSignature Sym Aris))
             (x y z : carriers A tt) : (forall s:Unit, Fin 3 -> carriers A s).
    intros s [[[e|tt]|tt]|tt].
    - elim e.
    - destruct s, tt. exact x.
    - destruct s, tt. exact y.
    - destruct s, tt. exact z.
  Defined.

  (* Register paths_ind as core.eq.type. *)
  Lemma assoc_if_models_assoc
        `{Funext}
        (Sym : Type)
        `{!IsHSet Sym}
        (Aris : Sym -> Type)
        (A : Algebra (Build_SingleSortedSignature Sym Aris))
        (m : Symbol (Build_SingleSortedSignature Sym Aris))
        (isbin : Aris m = Fin 2)
        (models_assoc : InterpEquation A (equation_associativity Sym Aris m isbin))
        (x y z : carriers A tt)
    : let op := (fun a b =>
                   operations
                     A m
                     (transport (fun T : Type => T -> A tt)
                                isbin^ (Fin2_rec a b))) in
      op x (op y z) = op (op x y) z.

    unfold InterpEquation in models_assoc.
    specialize (models_assoc (f' Sym Aris A x y z)).
    simpl.
    etransitivity.
    2:{ etransitivity.
        - exact models_assoc.
        - unfold sg_op.
          unfold g_op.
          cbn.
          apply ap.
          funext i.
          simpl in i.
          unfold transport.
          unfold f'.
          cbn.
          compute.

          subst.
          revert i.
          Fail rewrite isbin.
  Abort.
    (*       caseFin' i. *)

    (*       + cbn. reflexivity. *)
    (*       + cbn. unfold transport. apply ap. *)
    (*         funext j. simpl in j. caseFin' j. *)
    (*         * cbn. reflexivity. *)
    (*         * cbn. reflexivity. *)
    (* } *)
    (* { unfold sg_op. *)
    (*   unfold g_op. *)
    (*   cbn. *)
    (*   apply ap. *)
    (*   funext i. *)
    (*   simpl in i. *)
    (*   caseFin' i. *)
    (*   - cbn. apply ap. funext i. simpl in i. caseFin' i. *)
    (*     + reflexivity. *)
    (*     + reflexivity. *)
    (*   - cbn. reflexivity. *)
    (* } *)
End RefactorEquationalProofs.

Lemma assoc_if_models_group `{Funext}
      (uaG : ModelAlgebraGroup) (x y z : T uaG)
  : g_op x (g_op y z) = g_op (g_op x y) z.
Proof.
  pose (is_equational_model_algebra uaG group_eq_assoc) as models_assoc.
  unfold InterpEquation in models_assoc.
  specialize (models_assoc (equational_context_vars_3 uaG x y z)).
  symmetry.
  etransitivity.
  2:{ etransitivity.
      - exact models_assoc.
      - unfold sg_op. unfold g_op. cbn.
        apply ap.
        funext i. cbn in i.
        unfold transport. unfold equational_context_vars_3.
        caseFin' i; cbn.
        + reflexivity.
        + unfold transport. apply ap.
          funext j. cbn in j. caseFin' j.
          * cbn. reflexivity.
          * cbn. reflexivity.
  }
  { unfold sg_op, g_op; cbn.
    apply ap. funext i; cbn in i.
    caseFin' i; cbn.
    - apply ap. funext i. cbn in i. caseFin' i.
      + reflexivity.
      + reflexivity.
    - cbn. reflexivity.
  }
Qed.

Lemma left_unit_if_models_group `{Funext}
      (uaG : ModelAlgebraGroup)
  : LeftIdentity (@sg_op _ (@g_op uaG)) (@mon_unit _ g_unit).
Proof.
  unfold LeftIdentity. intros x.
  pose (is_equational_model_algebra uaG group_eq_left_unit) as lunit.
  unfold InterpEquation in lunit.
  specialize (lunit (equational_context_vars_1 _ x)).
  etransitivity.
  { etransitivity. 2:{ exact lunit. }
    unfold sg_op, mon_unit, g_op, map_term_algebra, CarriersTermAlgebra_rec, CarriersTermAlgebra_ind. cbn.
    apply ap. funext i. cbn in i.
    caseFin' i; cbn.
    + unfold g_unit. apply ap. funext j. destruct j.
    + reflexivity. }
  { cbn. reflexivity. }
Qed.

Lemma right_unit_if_models_group `{Funext}
      (uaG : ModelAlgebraGroup)
  : RightIdentity (@sg_op _ (@g_op uaG)) (@mon_unit _ g_unit).
Proof.
  unfold RightIdentity. intros x.
  pose (is_equational_model_algebra uaG group_eq_right_unit) as runit.
  unfold InterpEquation in runit.
  specialize (runit (equational_context_vars_1 _ x)).
  etransitivity.
  { etransitivity. 2:{ exact runit. }
    unfold sg_op, mon_unit, g_op, map_term_algebra, CarriersTermAlgebra_rec,
                   CarriersTermAlgebra_ind. cbn.
    apply ap. funext i. cbn in i.
    caseFin' i; cbn.
    + reflexivity.
    + unfold g_unit.
      apply ap. funext j. destruct j. }
  { cbn. reflexivity. }
Qed.

Lemma LeftInverse_if_models_group `{Funext}
  (uaG : ModelAlgebraGroup)
  : LeftInverse (@sg_op _ (@g_op uaG))
                (@negate (T uaG) (@g_inverse uaG)) (@mon_unit _ g_unit).
Proof.
  unfold LeftInverse. intros x.
  pose (is_equational_model_algebra uaG group_eq_left_inverse) as inv.
  specialize (inv (equational_context_vars_1 _ x)).
  unfold sg_op, mon_unit, g_op. etransitivity.
  * etransitivity. 2:{ exact inv. }
    cbn. apply ap. funext i. cbn in i. caseFin' i.
    -- cbn. unfold transport. unfold negate, g_inverse. cbn.
       apply ap. funext i. cbn in i. caseFin' i.
       reflexivity.
    -- cbn. reflexivity.
  * cbn. unfold g_unit. apply ap. cbn. funext i ; destruct i.
Qed.

Lemma RightInverse_if_models_group `{Funext}
      (uaG : ModelAlgebraGroup)
  : RightInverse (@sg_op _ (@g_op uaG))
                 (@negate (T uaG) (@g_inverse uaG)) (@mon_unit _ g_unit).
Proof.
  unfold RightInverse. intros x.
  pose (is_equational_model_algebra uaG group_eq_right_inverse) as inv.
  specialize (inv (equational_context_vars_1 _ x)).
  unfold sg_op, mon_unit, g_op. etransitivity.
  * etransitivity. 2:{ exact inv. }
    cbn. apply ap. funext i. cbn in i. caseFin' i.
    -- cbn. reflexivity.
    -- cbn. unfold transport. unfold negate, g_inverse. cbn.
       apply ap. funext i. cbn in i. caseFin' i.
       reflexivity.
  * cbn. unfold g_unit. apply ap. cbn. funext i ; destruct i.
Qed.

Definition Group_from_ModelAlgebraGroup `{Funext}
  (uaG : ModelAlgebraGroup) : Group.
    apply (@Build_Group (T uaG) g_op g_unit g_inverse).
    apply Build_IsGroup.
    + apply Build_IsMonoid.
      * apply Build_IsSemiGroup.
        -- apply hset_algebra.
        -- unfold Associative.
           unfold HeteroAssociative.
           apply assoc_if_models_group.
      * apply left_unit_if_models_group.
      * apply right_unit_if_models_group.
    + apply LeftInverse_if_models_group.
    + apply RightInverse_if_models_group.
Defined.

Definition Algebra_from_Group (g : Group) : Algebra group_signature.
  { apply (@Build_Algebra group_signature (fun _ => group_type g)).
      - cbn. intros u. destruct u.
        + unfold Operation. cbn.
          pose (m := @group_sgop g).
          unfold SgOp in m.
          intros args.
          pose (x := args (inr tt)).
          pose (y := args (inl (inr tt))).
          exact (m x y).
        + intros args. cbn in args.
          apply group_unit.
        + intros args. cbn in args.
          exact (group_inverse (args (inr tt))).
      - cbn. intros. destruct (@group_isgroup g).
        destruct group_monoid. destruct monoid_semigroup.
        exact sg_set.
    }
Defined.

(* TODO: factor out components to make it more readable if it appears in a goal. *)
Definition ModelAlgebraGroup_from_Group `{Funext} (g : Group)
  : ModelAlgebraGroup.
  unfold ModelAlgebraGroup.
  apply (@Build_ModelAlgebra _ _ _ {| model_algebra := Algebra_from_Group g |}).
  cbn.
  unfold IsModelAlgebra. unfold InterpEquations.
  intros i. induction i; unfold InterpEquation.
  + intros f.
    cbn in f.
    pose (isg := @group_isgroup g). destruct isg.
    destruct group_monoid. destruct monoid_semigroup.
    unfold Associative, HeteroAssociative in sg_ass.
    unfold sg_op in sg_ass.
    unfold Algebra_from_Group. cbn.
    apply sg_ass.
  + intros f.
    cbn in f.
    unfold Algebra_from_Group. cbn.
    pose (isg := @group_isgroup g). destruct isg.
    destruct group_monoid.
    apply monoid_right_id.
  + intros f.
    cbn in f.
    unfold Algebra_from_Group. cbn.
    pose (isg := @group_isgroup g). destruct isg.
    destruct group_monoid.
    apply monoid_left_id.
  + intros f.
    cbn in f.
    unfold Algebra_from_Group. cbn.
    pose (isg := @group_isgroup g). destruct isg.
    apply negate_r.
  + intros f.
    cbn in f.
    unfold Algebra_from_Group. cbn.
    pose (isg := @group_isgroup g). destruct isg.
    apply negate_l.
Defined.

Theorem ModelAlgebraGroup_Group_equiv `{Funext} : ModelAlgebraGroup <~> Group.
  srapply equiv_adjointify.
  - apply Group_from_ModelAlgebraGroup.
  - apply ModelAlgebraGroup_from_Group. (* Group -> ModelAlgebraGroup *)
  - (* Group_from_ModelAlgebraGroup o ModelAlgebraGroup_from_Group == idmap *)
    (* unfold Group_from_ModelAlgebraGroup. *)
    (* unfold ModelAlgebraGroup_from_Group. *)
    admit.
  - (* ModelAlgebraGroup_from_Group o Group_from_ModelAlgebraGroup == idmap *)
    admit.
Abort.

(* Here I list some of the missing results for this file. Remember that univalence is an axiom, so try to use it only for h-props.
   1. Show that [ModelAlgebraGroup] is equivalent to [Group], [ModelAlgebraGroup <~> Group].
   2. Define group homomorphism and isomorphism, see HoTT.Algebra.Groups.Group. Show group
   homomorphism/isomorphism is equivalent to algebra homomorphism/isomorphism. If a function preserves multiplication and unit, then it also preserves inverse.
   3. Show that group isomorphism is equivalent to equality by applying [equiv_path_isomorphism] from HoTT.Algebra.Universal.Isomorphism.
   4. Define the product group and projection homomorphisms by using [model_prod_algebra].
   5. Prove the universal property for product group using that for [prod_algebra].
   6. Define subgroup as a [model_subalgebra] and the inclusion map using that for [subalgebra].
   7. Define group congruence using algebra congruence.
   8. Define quotient group (by a congruence) as a [model_quotient_algebra].
   9. Obtain the quotient map and universal property from that of [quotient_algebra].
   10. Prove the equivalence normal subgroup <~> group congruence, [fun N => (fun x y => x * -y ∈ N)] and [fun R => {x | R x mon_unit}].
   11. Define quotient group (by normal subgroup).
   12. Prove that the quotient by normal subgroup is equivalent to quotient by congruence, by using the equivalence between normal subgroup and congruence.
   13. Obtain the universal property for quotient by normal subgroup from that of quotient by congruence.
   14. Define the free group and universal property using [FreeAlgebra]. *)
