Require Import
  HoTT.Basics
  HoTT.Types
  HoTT.Categories.Category.Core
  HoTT.Categories.Category.Univalent
  HoTT.Algebra.Universal.Isomorphism.

Require HoTT.Categories.Category.Morphisms.

Import Morphisms.CategoryMorphismsNotations.

Local Open Scope category.

(** Given any signature [σ], there is a precategory of set algebras
    and homomorphisms for that signature. *)

Lemma precategory_algebra `{Funext} (σ : Signature) : PreCategory.
Proof.
  apply (@Build_PreCategory (Algebra σ) Homomorphism
          (@homomorphism_id σ) (@homomorphism_compose σ));
    [intros; by apply path_homomorphism .. | exact _].
Defined.

(** Category isomorphism implies algebra isomorphism. *)

Lemma catiso_to_uaiso `{Funext} {σ} {A B : object (precategory_algebra σ)}
  : A <~=~> B -> Isomorphism A B.
Proof.
  intros [f [a b c]].
  unshelve eapply (@Build_Isomorphism _ _ _ f).
  intros s.
  refine (isequiv_adjointify (f s) (a s) _ _).
  - exact (apD10_homomorphism c s).
  - exact (apD10_homomorphism b s).
Defined.

(** Algebra isomorphic implies category isomorphic. *)

Lemma uaiso_to_catiso `{Funext} {σ} {A B : object (precategory_algebra σ)}
  : Isomorphism A B -> A <~=~> B.
Proof.
  intros [f F G]. set (h := Build_Homomorphism f).
  apply (@Morphisms.Build_Isomorphic _ A B h).
  apply (@Morphisms.Build_IsIsomorphism _ A B h (homomorphism_inv h)).
  - apply path_homomorphism. funext s x. apply eissect.
  - apply path_homomorphism. funext s x. apply eisretr.
Defined.

(** Category isomorphic and algebra isomorphic is equivalent. *)

Global Instance isequiv_catiso_to_uaiso `{Funext} {σ : Signature}
  (A B : object (precategory_algebra σ))
  : IsEquiv (@catiso_to_uaiso _ σ A B).
Proof.
  refine (isequiv_adjointify catiso_to_uaiso uaiso_to_catiso _ _).
  - intros [f F G]. by apply path_isomorphism.
  - intros [f F]. by apply Morphisms.path_isomorphic.
Defined.

(** [Morphisms.idtoiso] factorizes as the composition of equivalences. *)

Lemma path_idtoiso_isomorphic_id `{Funext} {σ : Signature}
  (A B : object (precategory_algebra σ))
  : @Morphisms.idtoiso (precategory_algebra σ) A B
    = catiso_to_uaiso^-1 o path_to_isomorphism.
Proof.
  funext p. destruct p. by apply Morphisms.path_isomorphic.
Defined.

(** The precategory of set algebras and homomorphisms for a signature
    is a (univalent) category. *)

Lemma iscategory_algebra `{Univalence} (σ : Signature)
  : IsCategory (precategory_algebra σ).
Proof.
  intros A B.
  rewrite path_idtoiso_isomorphic_id.
  apply @isequiv_compose.
  - apply isequiv_compose.
  - apply isequiv_inverse.
Qed.

Definition category_algebra `{Univalence} (σ : Signature) : Category
  := Build_Category (iscategory_algebra σ).
