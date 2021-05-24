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

Definition signature_group : Signature :=
  Build_SingleSortedSignature GroupSymbol
    (fun s => match s with
              | group_sgop_sym => Fin 2
              | group_unit_sym => Fin 0
              | group_inverse_sym => Fin 1
              end).

Definition AlgebraGroup : Type := Algebra signature_group.

Definition equations_group : Equations signature_group (Fin 5).
Proof.
  constructor. FinInd.
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

Definition ModelAlgebraGroup : Type := ModelAlgebra equations_group.

(* Here I list some of the missing results for this file. Remember that univalence is an axiom, so try to use it only for h-props.
   1. Show that [ModelAlgebraGroup] is equivalent to [Group], [ModelAlgebraGroup <~> Group].
   2. Define group homomorphism and isomorphism, see HoTT.Algebra.Groups.Group. Show group homomorphism/isomorphism is equivalent to algebra homomorphism/isomorphism. If a function preserves multiplication, then it also preserves unit and inverse.
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
