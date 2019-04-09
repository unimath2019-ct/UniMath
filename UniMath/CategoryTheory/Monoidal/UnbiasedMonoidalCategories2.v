Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.categories.StandardCategories.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.Combinatorics.StandardFiniteSets.

Local Open Scope stn.

Section stn_yoga.

  Definition pair_functions {X : UU} (n m : nat) :
    (⟦n⟧ -> X) -> (⟦m⟧ -> X) -> (⟦n+m⟧ -> X).
  Proof.
    induction n.
    - intros _ l' ; exact l'.
    - intros l l' x.
      induction (natgthorleh (S n) (pr1 x)) as [lt | gte].
      + exact (l (pr1 x ,, lt)).
      + apply l'.
        exists (pr1 x - (S n)).
        exact (nat_split (pr2 x) gte).
  Defined.

  Definition map {X Y : UU} {n : nat} :
    (X -> Y) -> (⟦n⟧ -> X) -> (⟦n⟧ -> Y) := fun f l => f ∘ l.

  Definition pointwise_apply {X Y Z : UU} {n : nat} :
    (X -> Y -> Z) -> (⟦n⟧ -> X) -> (⟦n⟧ -> Y) -> (⟦n⟧ -> Z)
    := fun f l l' x => f (l x) (l' x).

  Definition zip {X Y : UU} {n : nat} :
    (⟦n⟧ -> X) -> (⟦n⟧ -> Y) -> (⟦n⟧ -> X × Y)
    := pointwise_apply dirprodpair .

End stn_yoga.

Local Open Scope cat.

Section param_list_precategory.

  Context {n : nat}.
  Variable (fam : ⟦n⟧ -> precategory).

  Definition param_list_precategory_ob_mor : precategory_ob_mor.
  Proof.
    exists (∏ (x : ⟦n⟧) , ob (fam x)).
    exact (fun l l' => ∏ (x : ⟦n⟧), (fam x)⟦l x, l' x⟧).
  Defined.

  Definition param_list_precategory_id_comp :
    precategory_id_comp param_list_precategory_ob_mor.
  Proof.
    apply dirprodpair.
    - intros c x. apply identity.
    - intros a b c lf lg x.
      exact (lg x ∘ lf x).
  Defined.

  Definition param_list_precategory_data : precategory_data
    := (param_list_precategory_ob_mor ,, param_list_precategory_id_comp).

  Definition param_list_precategory : precategory.
  Proof.
    use mk_precategory.
    - exact param_list_precategory_data.
    - apply dirprodpair ; apply dirprodpair ;
        intros ; apply (pr1weq (weqfunextsec _ _ _)) ;
        intro x ; apply (fam x).
  Defined.

End param_list_precategory.

Section param_list_category.

  Context {n : nat}.
  Variable (fam : ⟦n⟧ -> category).

  Definition has_homsets_param_list_precategory : has_homsets (param_list_precategory fam).
  Proof.
    intros a b.
    apply impred_isaset.
    intro x. apply (fam x).
  Defined.

  Definition param_list_category : category
    := (param_list_precategory fam ,, has_homsets_param_list_precategory).

End param_list_category.

Definition list_category (n : nat) (C : category) : category
  := param_list_category (fun (_ : ⟦n⟧) => C).

Section tensor_constructions.

  Context {C : category} (tensor : ∏ n, list_category n C ⟶ C) .

  Local Notation "⊗ n" := (tensor n) (at level 30).

  (** This constructs the horizontal_domain, the precategory whose objects are
      list of objects in C. Specifically , given [l : ⟦n⟧ -> nat], the objects of
      [h_dom l] are lists

      ((a_(1,1), .., a(1,l(1))), .. ,(a_(n,1), .., a_(n,l(n))))

      where [a_(i,j) : ob C].
   *)

  Definition h_dom {n : nat} (l : ⟦n⟧ -> nat) : category
    := param_list_category (map (fun m => list_category m C) l).

  Definition h_prod_fun {n : nat} (nfun : (∏ n, list_category n C ⟶ C))
             (l : ⟦n⟧ -> nat) : h_dom l ⟶ list_category n C.
  Proof.
    use mk_functor.
    - use mk_functor_data.
      + intro x. cbn in x.
