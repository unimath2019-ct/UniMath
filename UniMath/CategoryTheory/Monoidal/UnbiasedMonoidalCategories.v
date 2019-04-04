Require Import UniMath.Foundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.categories.StandardCategories.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.Combinatorics.Lists.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.

(*** Ye have been warned, everything is made from right-associated products. *)

Section listyoga.

  Definition sumlist : list nat -> nat := foldr add 0.

  Definition flattenlist {A : UU} : list (list A) -> list A := foldr concatenate nil.

End listyoga.


Local Open Scope cat.
Local Open Scope list.

Section unit_category_is_unit.

  Variable (C : precategory).

  Definition lunit_functor : functor (precategory_binproduct unit_category C) C.
  Proof.
    use mk_functor.
    - use functor_data_constr.
      + exact (dirprod_pr2).
      + intros a b f. exact (dirprod_pr2 f).
    - apply dirprodpair.
      + intro a. apply idpath.
      + intros a b c f g. apply idpath.
  Defined.

  Definition lunit_inv_functor : functor C (precategory_binproduct unit_category C).
  Proof.
    use mk_functor.
    - use functor_data_constr.
      + exact (dirprodpair tt).
      + intros a b. apply dirprodpair. apply idpath.
    - apply dirprodpair.
      + intro a. apply dirprod_paths ; apply idpath.
      + intros a b c f g. apply dirprod_paths ; apply idpath.
  Defined.

  Definition runit_functor : functor (precategory_binproduct C unit_category) C.
  Proof.
    use mk_functor.
    - use functor_data_constr.
      + exact (dirprod_pr1).
      + intros a b f. exact (dirprod_pr1 f).
    - apply dirprodpair.
      + intro a. apply idpath.
      + intros a b c f g. apply idpath.
  Defined.

  Definition runit_inv_functor : functor C (precategory_binproduct C unit_category).
  Proof.
    use mk_functor.
    - use functor_data_constr.
      + exact (fun o => dirprodpair o tt).
      + intros a b f. apply dirprodpair. exact f. apply idpath.
    - apply dirprodpair.
      + intro a. apply dirprod_paths ; apply idpath.
      + intros a b c f g. apply dirprod_paths ; apply idpath.
  Defined.

End unit_category_is_unit.

Section ListPrecategory.

  (** Given [C : precategory] and [l : list nat] this constructs

      C^l(0) x (C^l(1) x .. (C^l(last)))

      Note the association, and each power is right-associated too.

   *)

  Variable C : precategory.

  Definition list_precategory (n : nat) : precategory.
  Proof.
    induction n.
    - exact unit_category.
    - exact (precategory_binproduct C IHn).
  Defined.

  Definition horizontal_domain : ∏ (l : list nat), precategory.
  Proof.
    use list_ind.
    - exact unit_category.
    - intros k ks partial_product.
      exact (precategory_binproduct (list_precategory k) partial_product).
  Defined.

  (** Given [l : list nat ], this constructs the cannonical functor from

      C^l(0) x (C^l(1) x .. (C^l(last))) --> C^(sumlist l)

   *)

  Definition flatten_functor : ∏ (l : list nat),
    functor (horizontal_domain l) (list_precategory (sumlist l)).
  Proof.
    use list_ind.
    - exact (functor_identity unit_category).
    - intros k ks suffix_functor.
      induction k.
      + exact (lunit_functor _ ∙ suffix_functor).
      + refine (functor_composite _ _).
        exact (precategory_binproduct_unassoc
                 C (list_precategory k) (horizontal_domain ks)).
        exact (pair_functor (functor_identity C) IHk).
  Defined.

End ListPrecategory.

Section UnivalentListCategory.

  Variable (C : univalent_category).

  Definition is_univalent_list_category (n : nat)
    : is_univalent (list_precategory C n).
  Proof.
    induction n.
    - apply unit_category.
    - apply (is_univalent_binproduct C (_ ,, IHn)).
  Defined.

End UnivalentListCategory.

Section ListReassociation.

Section UnbiasedMoniodalPrecat.

  (** An unbiased (lax) monoidal category is a category C equipped with maps:

      tensor_n : C^n -> C

      for each natural n, as well as natural transformations

      γ : tensor_k ∘ (tensor_n1 , ... , tensor_nk) -> tensor_(∑ n_i)
      ι : id_C -> tensor_1

      for each k ∈ ℕ, and n_1, ..., n_k ∈ ℕ, subject to the following.
   *)

  Context {C : precategory} (tensor : ∏ n, list_precategory C n ⟶ C) .

  (** This constructs, for [ l: list nat ], the functor

      C^l(0) x (C^l(1) ... ( C^l(last) )) --> C^(length l)

      by taking tensors on each listed power.
   *)

  Definition horizontal_tensor : ∏ (l : list nat),
    functor (horizontal_domain C l) (list_precategory C (length l)).
  Proof.
    use list_ind.
    - exact (functor_identity unit_category).
    - intros k ks functor.
      exact (pair_functor (tensor k) functor).
  Defined.

  Definition gammator (l : list nat) : UU
    := nat_trans ((horizontal_tensor _) ∙ (tensor (length l)))
                 ((flatten_functor _ _) ∙ tensor (sumlist l)).

  Definition iotator : UU
    := nat_trans ((runit_inv_functor C) ∙ tensor 1) (functor_identity _).

  Section first_functor.

      (** Here we construct

                       (C^(k_(1,1)) x ... x C^(k_(1,j_1)))    -
                                                               |
                     x ...                                     | n
                                                               |
                     x (C^(k_(n,1)) x ... x C^(k_(n,j_n)))    -

                        |______________________________|
                                       j_n

      from [ ll : list (list nat) ] where        n = length ll,
                                             j_i = length ll[i]
                                         k_(i,m) = ll[i][m]

      as well as the functor (below) with this domain and codomain C.

         x_n (x_m1 (x_k11) ... (x_k1j1) )
             (x_m2 (x_k21 ) ...(x_k2j2) ) ...
             (x_mn (x_kn1) ... (x_knjn) )

   *)

    Definition double_list_to_domain1 : ∏ (ll : list (list nat)), precategory.
    Proof.
      use list_ind.
      - exact unit_category.
      - intros l ls IHls.
        exact (precategory_binproduct (horizontal_domain C l) IHls).
    Defined.

    Definition functor_layer1 :=
      ∑ (l : list nat), horizontal_domain C l ⟶ list_precategory C (length l).

    Definition functor_layer2 :=
      ∑ (ll : list (list nat)),
      double_list_to_domain1 ll ⟶ horizontal_domain C (map length ll).

    Definition functor_layer3 := ∑ (ll : list (list nat)),
      double_list_to_domain1 ll ⟶ list_precategory C (length ll).

    Definition list_of_tensors : list (list nat) → list functor_layer1.
    Proof.
      apply map.
      intro l.
      exact (l ,, horizontal_tensor _).
    Defined.

    Definition innermost_tensor_functor : list functor_layer1 -> functor_layer2.
    Proof.
      apply foldr.
      - intros lF llG.
        exists ((pr1 lF) :: (pr1 llG)).
        exact (pair_functor (pr2 lF) (pr2 llG)).
      - exact (nil ,, functor_identity _).
    Defined.

    Definition innermost_tensor_list_preserves_shape : ∏ (ll : list (list nat)),
      pr1 (innermost_tensor_functor (list_of_tensors ll)) = ll.
    Proof.
      use list_ind.
      - reflexivity.
      - intros l ls IH.
        exact (maponpaths (cons l) IH).
    Defined.

    Definition pre_tensor1 {ll : list (list nat)} :
      double_list_to_domain1 ll ⟶ horizontal_domain C (map length ll).
    Proof.
      apply (transportf (fun ll => functor (double_list_to_domain1 ll)
                                        (horizontal_domain C (map length ll)))
                        (innermost_tensor_list_preserves_shape ll)).
      exact (pr2 (innermost_tensor_functor (list_of_tensors ll))).
    Defined.

    Definition tensor1 {ll : list (list nat)} : double_list_to_domain1 ll ⟶ C
      := pre_tensor1 ∙ horizontal_tensor _ ∙ tensor _.
  End first_functor.

  Section second_functor.

    (** In the notation of the above comments, given [ ll : list (list nat ) ]
        this section constructs:

        C^(k_(1,1)) x (... x ( C^(k_(1,j_1)) x ( C^(2,1) x ( ... C^(k_(n,j_n))...)

        as well as the functor (below) with this as domain and codomain C.

          x_n (x_(sum xk1i) )
             (x_(sum xk2i) ) ...
             (x_(sum xkni) )
     *)

    Definition double_list_to_domain2 (ll : list (list nat)) : precategory
      := horizontal_domain C (flattenlist ll).

    Definition tensor2 {ll : list (list nat)} : double_list_to_domain2 ll ⟶ C
      := horizontal_tensor _ ∙ tensor _.

  End second_functor.

  Section third_functor.

    (** In the established notation, given [ ll: list (list nat) ] this section
        constructs

        C^(sum k_(1,i)) x ( ... x C^(sum k_(n,i)))

        as well as the functor (below) with this as domain and codomain C.

        x_(sum mi) (x_k11) ... (x_k1j1) ... (x_kn1) ... (x_knjn)

     *)

  Definition double_list_to_domain3 (ll : list (list nat)) : precategory
    := horizontal_domain C (map sumlist ll).

  Definition tensor3 {ll : list (list nat)} : double_list_to_domain3 ll ⟶ C
    := horizontal_tensor _ ∙ tensor _ .

  End third_functor.

  Section fourth_functor.

    (** Given [ ll: list (list nat) ] this section constructs the tensor functor


                            x_(sum sum (k_ij))
        C^(sum sum k_(i,j)) -------------------> C
     *)

  Definition double_list_to_domain4 (ll : list (list nat)) : precategory
    := list_precategory C (sumlist (map sumlist ll)).

  Definition tensor4 {ll : list (list nat)} : double_list_to_domain4 ll ⟶ C
    := tensor _.

  End fourth_functor.

  Section first_pasting.

    (** In this section we construct the pasting

                     tensor1
             domain1 ---------> A
                 |             ||
        flatten  |  gammator   ||
                 |             ||
             domain1 -tensor2-> A
                 |             ||
        flatten  |  gammator   ||
                 |             ||
             domain2 ---------> A
                    tensor3
     *)

    Context (ll : list (list nat)).

    (* Definition stuff : ∏ (ll : list (list nat)), *)
    (*                    double_list_to_domain1 ll = *)
    (*                    list_precategory _ _. *)

    Check tensor1.
    Check pre_tensor1 ∙ flatten_functor _ _.

    Definition first_gamma : ∏ (ll : list (list nat)) (g : gammator (map sumlist ll)),
                             tensor1 ⟹ pre_tensor1  ∙ tensor2.

    Check tensor1 ll.
    Check gammator (map sumlist ll).

    Check pre_whisker.



  Definition gamma_comp1 : UU :=
    ∏ (ll : (list (list nat))), .
