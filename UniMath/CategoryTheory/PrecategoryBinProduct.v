(** * Binary product of (pre)categories

  Benedikt Ahrens, Ralph Matthes, Peter LeFanu Lumsdaine

  SubstitutionSystems

  2015

  For the general case, see [product_precategory].

  See [unit_category] for the unit category, which is the unit
  under cartesian product up to isomorphism.

*)


(** ** Contents :

  - Definition of the cartesian product of two precategories

  - From a functor on a product of precategories to a functor on one of
    the categories by fixing the argument in the other component

  - Definition of the associator functors

  - Definition of the pair of two functors: A × C → B × D
    given A → B and C → D

  - Definition of the diagonal functor [bindelta_functor].

*)


Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.opp_precat.

Local Open Scope cat.

Definition precategory_binproduct_mor (C D : precategory_ob_mor) (cd cd' : C × D) := pr1 cd --> pr1 cd' × pr2 cd --> pr2 cd'.

Definition precategory_binproduct_ob_mor (C D : precategory_ob_mor) : precategory_ob_mor
  := tpair _ _ (precategory_binproduct_mor C D).

Definition precategory_binproduct_data (C D : precategory_data) : precategory_data.
Proof.
  exists (precategory_binproduct_ob_mor C D).
  split.
  - intro cd.
    exact (dirprodpair (identity (pr1 cd)) (identity (pr2 cd))).
  - intros cd cd' cd'' fg fg'.
    exact (dirprodpair (pr1 fg · pr1 fg') (pr2 fg · pr2 fg')).
Defined.

Section precategory_binproduct.

Variables C D : precategory.

Lemma is_precategory_precategory_binproduct_data : is_precategory (precategory_binproduct_data C D).
Proof.
  repeat split; simpl; intros.
  - apply dirprodeq; apply id_left.
  - apply dirprodeq; apply id_right.
  - apply dirprodeq; apply assoc.
  - apply dirprodeq; apply assoc'.
Defined.

Definition precategory_binproduct : precategory
  := tpair _ _ is_precategory_precategory_binproduct_data.

Definition has_homsets_precategory_binproduct (hsC : has_homsets C) (hsD : has_homsets D) :
  has_homsets precategory_binproduct.
Proof.
  intros a b.
  apply isasetdirprod.
  - apply hsC.
  - apply hsD.
Qed.

Definition ob1 (x : precategory_binproduct) : C := pr1 x.
Definition ob2 (x : precategory_binproduct) : D := pr2 x.
Definition mor1 (x x' : precategory_binproduct) (f : _ ⟦x, x'⟧) : _ ⟦ob1 x, ob1 x'⟧ := pr1 f.
Definition mor2 (x x' : precategory_binproduct) (f : _ ⟦x, x'⟧) : _ ⟦ob2 x, ob2 x'⟧ := pr2 f.

End precategory_binproduct.

Arguments ob1 { _ _ } _ .
Arguments ob2 { _ _ } _ .
Arguments mor1 { _ _ _ _ } _ .
Arguments mor2 { _ _ _ _ } _ .
Local Notation "C × D" := (precategory_binproduct C D) (at level 75, right associativity).

Goal ∏ (C D:precategory), (C × D)^op = (C^op × D^op).
  reflexivity.
Qed.

(** Objects and morphisms in the product precategory of two precategories *)
Definition precatbinprodpair {C D : precategory} (X : C) (Y : D) : precategory_binproduct C D
  := dirprodpair X Y.

Local Notation "A ⊗ B" := (precatbinprodpair A B).
Local Notation "( A , B )" := (precatbinprodpair A B).

Definition precatbinprodmor {C D : precategory} {X X' : C} {Z Z' : D} (α : X --> X') (β : Z --> Z')
  : X ⊗ Z --> X' ⊗ Z'
  := dirprodpair α β.

Local Notation "( f #, g )" := (precatbinprodmor f g).

(* Some useful facts about product precategories *)
Definition binprod_id {C D : precategory} (c : C) (d : D) : (identity c #, identity d) = identity (c, d).
Proof.
  apply idpath.
Defined.

Definition binprod_comp {C D : precategory} (c c' c'' : C) (d d' d'' : D) (f : c --> c') (f' : c' --> c'') (g : d --> d') (g' : d' --> d'') : (f · f' #, g · g') = (f #, g) · (f' #, g').
Proof.
  apply idpath.
Defined.

Definition is_iso_binprod_iso {C D : precategory} {c c' : C} {d d' : D} {f : c --> c'} {g : d --> d'} (f_is_iso : is_iso f)
  (g_is_iso : is_iso g) : is_iso (f #, g).
Proof.
  apply (is_iso_qinv (f #, g) (inv_from_iso (isopair f f_is_iso) #, inv_from_iso (isopair g g_is_iso))).
  apply dirprodpair.
  - transitivity ((isopair f f_is_iso) · (inv_from_iso (isopair f f_is_iso)) #, (isopair g g_is_iso) · (inv_from_iso (isopair g g_is_iso))).
    + symmetry.
      apply binprod_comp.
    + rewrite 2 iso_inv_after_iso.
      apply binprod_id.
  - transitivity ((inv_from_iso (isopair f f_is_iso)) · (isopair f f_is_iso) #, (inv_from_iso (isopair g g_is_iso)) · (isopair g g_is_iso)).
    + symmetry.
      apply binprod_comp.
    + rewrite 2 iso_after_iso_inv.
      apply binprod_id.
Defined.

(** Isos in product precategories *)
Definition precatbinprodiso {C D : precategory} {X X' : C} {Z Z' : D} (α : iso X X') (β : iso Z Z')
  : iso (X ⊗ Z) (X' ⊗ Z').
Proof.
  set (f := precatbinprodmor α β).
  set (g := precatbinprodmor (iso_inv_from_iso α) (iso_inv_from_iso β)).
  exists f.
  apply (is_iso_qinv f g).
  use tpair.
  - apply pathsdirprod.
    apply iso_inv_after_iso.
    apply iso_inv_after_iso.
  - apply pathsdirprod.
    apply iso_after_iso_inv.
    apply iso_after_iso_inv.
Defined.

Definition precatbinprodiso_inv {C D : precategory} {X X' : C} {Z Z' : D}
  (α : iso X X') (β : iso Z Z')
  : precatbinprodiso (iso_inv_from_iso α) (iso_inv_from_iso β)
  = iso_inv_from_iso (precatbinprodiso α β).
Proof.
  apply inv_iso_unique.
  apply pathsdirprod.
  - apply iso_inv_after_iso.
  - apply iso_inv_after_iso.
Defined.

(** Univalence of binary products of categories *)

Section univalence.

  Variable (C D : univalent_category).

  (** We factor     idtoiso       as in this diagram
     (a,b) = (x,y) -------------> iso (a,b) (x,y)
           |                       ^
           |                       |
           v                       |
     a = b × x = y --> (iso a b) × (iso x y)
   where the other composite is show to be an equivalence.*)

  Definition id_to_prodid_weq (v w : precategory_binproduct C D) :
    v = w ≃ (dirprod (pr1 v = pr1 w) (pr2 v = pr2 w)).
  Proof.
    exact pathsdirprodweq.
  Defined.

  Definition prodid_to_prodiso_weq (v w : precategory_binproduct C D) :
    (dirprod (pr1 v = pr1 w) (pr2 v = pr2 w)) ≃ (dirprod (iso (pr1 v) (pr1 w))
                                                         (iso (pr2 v) (pr2 w))).
  Proof.
    apply weqdirprodf ; apply (weqpair idtoiso).
    - apply (pr2 C).
    - apply (pr2 D).
  Defined.

  Definition prodiso_to_iso (v w : precategory_binproduct C D) :
    (dirprod (iso (pr1 v) (pr1 w)) (iso (pr2 v) (pr2 w))) -> iso v w.
  Proof.
    intro.
    exists (pr1 (pr1 X) ,, pr1 (pr2 X)).
    use is_iso_qinv.
    { exact (inv_from_iso (pr1 X) ,, inv_from_iso (pr2 X)). }
    apply dirprodpair ; cbn ; apply pathsdirprod ;
      try (apply iso_inv_after_iso) ; try (apply iso_after_iso_inv).
  Defined.

  Definition iso_to_prodiso (v w : precategory_binproduct C D) :
    iso v w -> (dirprod (iso (pr1 v) (pr1 w)) (iso (pr2 v) (pr2 w))).
  Proof.
    intro.
    apply dirprodpair.
    - exists (pr1 (pr1 X)).
      use is_iso_qinv.
      { exact (pr1 (inv_from_iso X)). }
      apply dirprodpair.
      + exact (maponpaths dirprod_pr1 (iso_inv_after_iso X)).
      + exact (maponpaths dirprod_pr1 (iso_after_iso_inv X)).
    - exists (pr2 (pr1 X)).
      use is_iso_qinv.
      { exact (pr2 (inv_from_iso X)). }
      apply dirprodpair.
      + exact (maponpaths dirprod_pr2 (iso_inv_after_iso X)).
      + exact (maponpaths dirprod_pr2 (iso_after_iso_inv X)).
  Defined.

  Definition prod_iso_to_iso_homot1 (v w : precategory_binproduct C D)
             (x : dirprod (iso (pr1 v) (pr1 w)) (iso (pr2 v) (pr2 w))) :
    (iso_to_prodiso v w (prodiso_to_iso v w x )) = x.
  Proof.
    apply dirprod_paths ;
      apply (subtypeEquality (fun f => isaprop_is_iso _ _ f)) ;
      apply idpath.
  Defined.

  Definition prod_iso_to_iso_homot2 (v w : precategory_binproduct C D)
             (x : iso v w) : (prodiso_to_iso v w (iso_to_prodiso v w x )) = x.
  Proof.
    apply (subtypeEquality (fun f => isaprop_is_iso _ _ f)).
    apply dirprod_paths ; reflexivity.
  Defined.

  Definition prodiso_to_iso_weq (v w : precategory_binproduct C D) :
    (dirprod (iso (pr1 v) (pr1 w)) (iso (pr2 v) (pr2 w))) ≃ iso v w.
  Proof.
    apply (weq_iso (prodiso_to_iso v w) (iso_to_prodiso v w)).
    - apply prod_iso_to_iso_homot1.
    - apply prod_iso_to_iso_homot2.
  Defined.

  Definition factored_idtoiso (v w : precategory_binproduct C D) :
    v = w ≃ iso v w.
  Proof.
    refine (_ ∘ _)%weq.
    refine (_ ∘ _)%weq.
    apply id_to_prodid_weq.
    apply prodid_to_prodiso_weq.
    apply prodiso_to_iso_weq.
  Defined.

  Definition idtoiso_is_weq (v w : precategory_binproduct C D) :
    isweq (@idtoiso _ v w).
  Proof.
    Search isweq.
    apply (isweqhomot (factored_idtoiso v w)).
    - intro p.
      induction p.
      apply (subtypeEquality (fun f => isaprop_is_iso _ _ f)).
      apply idpath.
    - apply (factored_idtoiso v w).
  Defined.

  Definition is_univalent_binproduct :
    is_univalent (precategory_binproduct C D).
  Proof.
    apply dirprodpair.
    - apply idtoiso_is_weq.
    - apply has_homsets_precategory_binproduct.
      + apply C.
      + apply D.
  Defined.

  Definition univalent_binproduct : univalent_category
    := tpair _ _ is_univalent_binproduct.

End univalence.

(** Associativity functors *)
Section assoc.

Definition precategory_binproduct_assoc_data (C0 C1 C2 : precategory_data)
  : functor_data (precategory_binproduct_data C0 (precategory_binproduct_data C1 C2))
                 (precategory_binproduct_data (precategory_binproduct_data C0 C1) C2).
Proof.
  use tpair.
  (* functor_on_objects *) intros c. exact (tpair _ (tpair _ (pr1 c) (pr1 (pr2 c))) (pr2 (pr2 c))).
  (* functor_on_morphisms *) intros a b c. exact (tpair _ (tpair _ (pr1 c) (pr1 (pr2 c))) (pr2 (pr2 c))).
Defined.

Definition precategory_binproduct_assoc (C0 C1 C2 : precategory)
  : functor (C0 × (C1 × C2)) ((C0 × C1) × C2).
Proof.
  exists (precategory_binproduct_assoc_data _ _ _). split.
  (* functor_id *) intros c. simpl; apply paths_refl.
  (* functor_comp *) intros c0 c1 c2 f g. simpl; apply paths_refl.
Defined.

Definition precategory_binproduct_unassoc_data (C0 C1 C2 : precategory_data)
  : functor_data (precategory_binproduct_data (precategory_binproduct_data C0 C1) C2)
                 (precategory_binproduct_data C0 (precategory_binproduct_data C1 C2)).
Proof.
  use tpair.
  (* functor_on_objects *) intros c. exact (tpair _ (pr1 (pr1 c)) (tpair _ (pr2 (pr1 c)) (pr2 c))).
  (* functor_on_morphisms *) intros a b c. exact (tpair _ (pr1 (pr1 c)) (tpair _ (pr2 (pr1 c)) (pr2 c))).
Defined.

Definition precategory_binproduct_unassoc (C0 C1 C2 : precategory)
  : functor ((C0 × C1) × C2) (C0 × (C1 × C2)).
Proof.
  exists (precategory_binproduct_unassoc_data _ _ _). split.
  (* functor_id *) intros c. simpl; apply paths_refl.
  (* functor_comp *) intros c0 c1 c2 f g. simpl; apply paths_refl.
Defined.

End assoc.

(** Fixing one argument of C × D -> E results in a functor *)
Section functor_fix_fst_arg.

Variable C D E : precategory.
Variable F : functor (precategory_binproduct C D) E.
Variable c : C.

Definition functor_fix_fst_arg_ob (d:D) : E := F (tpair _ c d).
Definition functor_fix_fst_arg_mor (d d' : D) (f : d --> d') : functor_fix_fst_arg_ob d --> functor_fix_fst_arg_ob d'.
Proof.
  apply (#F).
  exact (dirprodpair (identity c) f).
Defined.

Definition functor_fix_fst_arg_data : functor_data D E
  := tpair _ functor_fix_fst_arg_ob functor_fix_fst_arg_mor.

Lemma is_functor_functor_fix_fst_arg_data: is_functor functor_fix_fst_arg_data.
Proof.
  red.
  split; red.
  + intros d.
    unfold functor_fix_fst_arg_data; simpl.
    unfold functor_fix_fst_arg_mor; simpl.
    unfold functor_fix_fst_arg_ob; simpl.
    assert (functor_id_inst := functor_id F).
    rewrite <- functor_id_inst.
    apply maponpaths.
    apply idpath.
  + intros d d' d'' f g.
    unfold functor_fix_fst_arg_data; simpl.
    unfold functor_fix_fst_arg_mor; simpl.
    assert (functor_comp_inst := @functor_comp _ _ F (dirprodpair c d) (dirprodpair c d') (dirprodpair c d'')).
    rewrite <- functor_comp_inst.
    apply maponpaths.
    unfold compose at 2.
    unfold precategory_binproduct; simpl.
    rewrite id_left.
    apply idpath.
Qed.

Definition functor_fix_fst_arg : functor D E
  := tpair _ functor_fix_fst_arg_data is_functor_functor_fix_fst_arg_data.

End functor_fix_fst_arg.

Section nat_trans_fix_fst_arg.

Variable C D E : precategory.
Variable F F' : functor (precategory_binproduct C D) E.
Variable α : F ⟹ F'.
Variable c : C.

Definition nat_trans_fix_fst_arg_data (d:D): functor_fix_fst_arg C D E F c d --> functor_fix_fst_arg C D E F' c d := α (tpair _ c d).

Lemma nat_trans_fix_fst_arg_ax: is_nat_trans _ _ nat_trans_fix_fst_arg_data.
Proof.
  red.
  intros d d' f.
  unfold nat_trans_fix_fst_arg_data, functor_fix_fst_arg; simpl.
  unfold functor_fix_fst_arg_mor; simpl.
  assert (nat_trans_ax_inst := nat_trans_ax α).
  apply nat_trans_ax_inst.
Qed.

Definition nat_trans_fix_fst_arg: functor_fix_fst_arg C D E F c ⟹ functor_fix_fst_arg C D E F' c
  := tpair _ nat_trans_fix_fst_arg_data nat_trans_fix_fst_arg_ax.

End nat_trans_fix_fst_arg.

Section functor_fix_snd_arg.

Variable C D E : precategory.
Variable F: functor (precategory_binproduct C D) E.
Variable d: D.

Definition functor_fix_snd_arg_ob (c:C): E := F(tpair _ c d).
Definition functor_fix_snd_arg_mor (c c':C)(f: c --> c'): functor_fix_snd_arg_ob c --> functor_fix_snd_arg_ob c'.
Proof.
  apply (#F).
  exact (dirprodpair f (identity d)).
Defined.

Definition functor_fix_snd_arg_data : functor_data C E
  := tpair _ functor_fix_snd_arg_ob functor_fix_snd_arg_mor.

Lemma is_functor_functor_fix_snd_arg_data: is_functor functor_fix_snd_arg_data.
Proof.
  split.
  + intros c.
    unfold functor_fix_snd_arg_data; simpl.
    unfold functor_fix_snd_arg_mor; simpl.
    unfold functor_fix_snd_arg_ob; simpl.
    assert (functor_id_inst := functor_id F).
    rewrite <- functor_id_inst.
    apply maponpaths.
    apply idpath.
  + intros c c' c'' f g.
    unfold functor_fix_snd_arg_data; simpl.
    unfold functor_fix_snd_arg_mor; simpl.
    assert (functor_comp_inst := @functor_comp _ _ F (dirprodpair c d) (dirprodpair c' d) (dirprodpair c'' d)).
    rewrite <- functor_comp_inst.
    apply maponpaths.
    unfold compose at 2.
    unfold precategory_binproduct; simpl.
    rewrite id_left.
    apply idpath.
Qed.

Definition functor_fix_snd_arg: functor C E.
Proof.
  exists functor_fix_snd_arg_data.
  exact is_functor_functor_fix_snd_arg_data.
Defined.

End functor_fix_snd_arg.

Section nat_trans_fix_snd_arg.

Variable C D E : precategory.
Variable F F': functor (precategory_binproduct C D) E.
Variable α: F ⟹ F'.
Variable d: D.

Definition nat_trans_fix_snd_arg_data (c:C): functor_fix_snd_arg C D E F d c --> functor_fix_snd_arg C D E F' d c := α (tpair _ c d).

Lemma nat_trans_fix_snd_arg_ax: is_nat_trans _ _ nat_trans_fix_snd_arg_data.
Proof.
  red.
  intros c c' f.
  unfold nat_trans_fix_snd_arg_data, functor_fix_snd_arg; simpl.
  unfold functor_fix_snd_arg_mor; simpl.
  assert (nat_trans_ax_inst := nat_trans_ax α).
  apply nat_trans_ax_inst.
Qed.

Definition nat_trans_fix_snd_arg: functor_fix_snd_arg C D E F d ⟹ functor_fix_snd_arg C D E F' d
  := tpair _ nat_trans_fix_snd_arg_data nat_trans_fix_snd_arg_ax.

End nat_trans_fix_snd_arg.

(* Define pairs of functors and functors from pr1 and pr2 *)
Section functors.

Definition pair_functor_data {A B C D : precategory}
  (F : functor A C) (G : functor B D) :
  functor_data (precategory_binproduct A B) (precategory_binproduct C D).
Proof.
use tpair.
- intro x; apply (precatbinprodpair (F (pr1 x)) (G (pr2 x))).
- intros x y f; simpl; apply (precatbinprodmor (# F (pr1 f)) (# G (pr2 f))).
Defined.

Definition pair_functor {A B C D : precategory}
  (F : functor A C) (G : functor B D) :
  functor (precategory_binproduct A B) (precategory_binproduct C D).
Proof.
apply (tpair _ (pair_functor_data F G)).
abstract (split;
  [ intro x; simpl; rewrite !functor_id; apply idpath
  | intros x y z f g; simpl; rewrite !functor_comp; apply idpath]).
Defined.

Definition pr1_functor_data (A B : precategory) :
  functor_data (precategory_binproduct A B) A.
Proof.
use tpair.
- intro x; apply (pr1 x).
- intros x y f; simpl; apply (pr1 f).
Defined.

Definition pr1_functor (A B : precategory) :
  functor (precategory_binproduct A B) A.
Proof.
apply (tpair _ (pr1_functor_data A B)).
abstract (split; [ intro x; apply idpath | intros x y z f g; apply idpath ]).
Defined.

Definition pr2_functor_data (A B : precategory) :
  functor_data (precategory_binproduct A B) B.
Proof.
use tpair.
- intro x; apply (pr2 x).
- intros x y f; simpl; apply (pr2 f).
Defined.

Definition pr2_functor (A B : precategory) :
  functor (precategory_binproduct A B) B.
Proof.
apply (tpair _ (pr2_functor_data A B)).
abstract (split; [ intro x; apply idpath | intros x y z f g; apply idpath ]).
Defined.

Definition bindelta_functor_data (C : precategory) :
  functor_data C (precategory_binproduct C C).
Proof.
use tpair.
- intro x; apply (precatbinprodpair x x).
- intros x y f; simpl; apply (precatbinprodmor f f).
Defined.

(* The diagonal functor Δ *)
Definition bindelta_functor (C : precategory) :
  functor C (precategory_binproduct C C).
Proof.
apply (tpair _ (bindelta_functor_data C)).
abstract (split; [ intro x; apply idpath | intros x y z f g; apply idpath ]).
Defined.

Definition bindelta_pair_functor_data (C D E : precategory)
  (F : functor C D)
  (G : functor C E) :
  functor_data C (precategory_binproduct D E).
Proof.
  use tpair.
  - intro c. apply (precatbinprodpair (F c) (G c)).
  - intros x y f. simpl. apply (precatbinprodmor (# F f) (# G f)).
Defined.

Definition bindelta_pair_functor {C D E : precategory}
  (F : functor C D)
  (G : functor C E) :
  functor C (precategory_binproduct D E).
Proof.
  apply (tpair _ (bindelta_pair_functor_data C D E F G)).
  split.
  - intro c.
    simpl.
    rewrite functor_id.
    rewrite functor_id.
    apply idpath.
  - intros c c' c'' f g.
    simpl.
    rewrite functor_comp.
    rewrite functor_comp.
    apply idpath.
Defined.


(* The swap functor C × D → D × C. *)
Definition swap_functor {C D : precategory} :
  functor (precategory_binproduct C D) (precategory_binproduct D C) :=
  pair_functor (pr2_functor C D) (pr1_functor C D) □ bindelta_functor (precategory_binproduct C D).


End functors.
