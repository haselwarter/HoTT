Require Import
  HoTT.Basics.Equivalences
  HoTT.Types.Bool
  HoTT.Types.Forall
  HoTT.Types.Sigma
  HoTT.Types.Prod
  HoTT.Algebra.Universal.Equations
  HoTT.Algebra.Universal.Homomorphism.

Local Open Scope Algebra_scope.

(** The following section defines product algebra [ProdAlgebra].
    Section [bin_prod_algebra] specialises the definition to
    binary product algebra. *)

Section prod_algebra.
  Context `{Funext} {σ : Signature} (I : Type) (A : I -> Algebra σ).

  Definition carriers_prod_algebra : Carriers σ
    := fun (s : Sort σ) => forall (i:I), A i s.

  Definition op_prod_algebra (w : SymbolType σ)
    (α : forall i, Operation (A i) w)
    : Operation carriers_prod_algebra w :=
      fun (a : DomOperation carriers_prod_algebra w) (i : I) =>
          α i (fun k => a k i).

  Definition ops_prod_algebra (u : Symbol σ)
    : Operation carriers_prod_algebra (σ u)
    := op_prod_algebra (σ u) (fun (i:I) => u.#(A i)).

  Definition ProdAlgebra : Algebra σ
    := Build_Algebra carriers_prod_algebra ops_prod_algebra.

End prod_algebra.

Section path_map_term_algebra_prod_algebra.
  Context
    `{Funext} {σ} (I : Type) (A : I -> Algebra σ)
    (C : Carriers σ) `{forall s, IsHSet (C s)}
    (f : forall s, C s -> ProdAlgebra I A s).

  Lemma path_map_term_algebra_prod_algebra (s : Sort σ)
    (x : TermAlgebra C s) (i : I)
    : map_term_algebra (ProdAlgebra I A) f s x i
      = map_term_algebra (A i) (fun s n => f s n i) s x.
  Proof.
    induction x.
    - reflexivity.
    - cbn. unfold ops_prod_algebra, op_prod_algebra. f_ap. funext Y. apply X.
  Defined.

End path_map_term_algebra_prod_algebra.

Section model_prod_algebra.
  Context `{Funext} {σ : Signature} (I : Type) (A : I -> Algebra σ)
          (J : Type) (e : Equations σ J)
          {E : forall i, IsModelAlgebra (A i) e}.

  Global Instance is_model_prod_algebra
    : IsModelAlgebra (ProdAlgebra I A) e.
  Proof.
    intros j a.
    funext i.
    specialize (E i j).
    destruct (e j) as [C h s L R].
    exact (path_map_term_algebra_prod_algebra I A C _ _ _ i
           @ E _
           @ (path_map_term_algebra_prod_algebra I A C _ _ _ i)^).
  Defined.

  Definition model_prod_algebra : ModelAlgebra e
    := Build_ModelAlgebra e (ProdAlgebra I A).

End model_prod_algebra.

(** The next section defines the product projection homomorphisms. *)

Section hom_proj_prod_algebra.
  Context `{Funext} {σ : Signature} (I : Type) (A : I -> Algebra σ).

  Definition def_proj_prod_algebra (i:I) (s : Sort σ) (c : ProdAlgebra I A s)
    : A i s
    := c i.

  Global Instance is_homomorphism_proj_prod_algebra (i:I)
    : IsHomomorphism (def_proj_prod_algebra i).
  Proof.
    intros u a. reflexivity.
  Defined.

  Definition hom_proj_prod_algebra (i : I)
    : ProdAlgebra I A $-> A i
    := Build_Homomorphism (def_proj_prod_algebra i).

End hom_proj_prod_algebra.

(** The product algebra univarsal mapping property [ump_prod_algebra]. *)

Section ump_prod_algebra.
  Context
    `{Funext}
    {σ : Signature}
    (I : Type)
    (A : I -> Algebra σ)
    (C : Algebra σ).

  Definition hom_prod_algebra_mapout
    (f : C $-> ProdAlgebra I A) (i:I)
    : C $-> A i
    := hom_proj_prod_algebra I A i $o f.

  Definition def_prod_algebra_mapin (f : forall (i:I) s, C s -> A i s)
    : forall (s : Sort σ) , C s -> ProdAlgebra I A s
    := fun (s : Sort σ) (x : C s) (i : I) => f i s x.

  Global Instance is_homomorphism_prod_algebra_mapin
    (f : forall (i:I), C $-> A i)
    : IsHomomorphism (def_prod_algebra_mapin f).
  Proof.
    intros u a. funext i. apply is_homomorphism.
  Defined.

  Definition hom_prod_algebra_mapin (f : forall i, C $-> A i)
    : C $-> ProdAlgebra I A
    := Build_Homomorphism (def_prod_algebra_mapin f).

  (** Given a family of homomorphisms [h : forall (i:I), Homomorphism C (A i)]
      there is a unique homomorphism [f : Homomorphism C (ProdAlgebra I A)]
      such that [h i = hom_compose (pr i) f], where

      <<
        pr i = hom_proj_prod_algebra I A i
      >>

      is the ith projection homomorphism. *)

 Lemma ump_prod_algebra
   : (forall (i:I), C $-> A i) <~> (C $-> ProdAlgebra I A).
  Proof.
    apply (equiv_adjointify hom_prod_algebra_mapin hom_prod_algebra_mapout).
    - intro f. by apply path_homomorphism.
    - intro f. funext i. by apply path_homomorphism.
  Defined.
End ump_prod_algebra.

(** Binary product algebra. *)

Section bin_prod_algebra.
  Context `{Funext} {σ : Signature} (A B : Algebra σ).

  Definition bin_prod_algebras (b:Bool) : Algebra σ
    := if b then B else A.

  Definition BinProdAlgebra : Algebra σ :=
    ProdAlgebra Bool bin_prod_algebras.

  Definition fst_prod_algebra : BinProdAlgebra $-> A
    := hom_proj_prod_algebra Bool bin_prod_algebras false.

  Definition snd_prod_algebra : BinProdAlgebra $-> B
    := hom_proj_prod_algebra Bool bin_prod_algebras true.
End bin_prod_algebra.

Infix "*" := BinProdAlgebra : Algebra_scope.

(** Specialisation of the product algebra univarsal mapping property
    to binary product. *)

Section ump_bin_prod_algebra.
  Context
    `{Funext} {σ : Signature} (A B C : Algebra σ).

 Lemma ump_bin_prod_algebra
   : (C $-> A) * (C $-> B) <~> (C $-> A * B).
  Proof.
    set (k := fun (b:Bool) => C $-> bin_prod_algebras A B b).
    exact (equiv_compose
            (ump_prod_algebra Bool (bin_prod_algebras A B) C)
            (equiv_bool_forall_prod k)^-1).
  Defined.
End ump_bin_prod_algebra.
