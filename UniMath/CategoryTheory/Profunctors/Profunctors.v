(** * Profunctors *)

(** E-valued profunctors for an arbitrary category E. *)

(** References:
    - https://link.springer.com/content/pdf/10.1007/BFb0060443.pdf
    - https://bartoszmilewski.com/2017/03/29/ends-and-coends/
    - https://arxiv.org/abs/1501.02503
 *)

(** ** Contents

  - Definition
  - Dinatural transformations
    - Dinatural transformation from a natural transformation
  - (Co)ends
    - Wedges
    - Ends
      - Accessors/coercions
    - Cowedges
    - Coends
      - Accessors/coercions
    - Coends and ends

 *)

Require Import UniMath.Foundations.Preamble.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.categories.HSET.Univalence.

Local Open Scope cat.

(** *** E-valued profunctors. *)
Section Profunctors.
  Context (E : precategory).

  (** * Definition *)
  (** A E-valued profunctor [C ↛ D] is a functor [D^op × C → E]. *)
  Definition profunctor (C D : precategory) : UU :=
    functor (precategory_binproduct (opp_precat D) C) E.

  Identity Coercion profunctor_coercion : profunctor >-> functor.

  Infix "↛" := profunctor (at level 99, only parsing) : cat.

  Local Notation "A ⊗ B" := (precatbinprodpair A B).

  Local Open Scope cat.

  (** Maps over the first argument contravariantly. The name is inspired by Data.Profunctor in
  Haskell. *)
  Definition lmap {C D : precategory} (F : C ↛ D) {a : ob C} {b b' : ob D} (g : b' --> b) :
    F (opp_ob b ⊗ a)  --> F (opp_ob b' ⊗ a).
  Proof.
    use (functor_on_morphisms F).
    - use precatbinprodmor.
      + exact (opp_mor g).
      + exact (identity a).
  Defined.

  (** Maps over the second argument covariantly. The name is inspired by Data.Profunctor in
  Haskell. *)
  Definition rmap {C D : precategory} (F : C ↛ D) {a a' : ob C} {b : ob D} (f : a --> a') :
    F (opp_ob b ⊗ a)  --> F (opp_ob b ⊗ a').
  Proof.
    use (functor_on_morphisms F).
    - use precatbinprodmor.
      + exact (identity b).
      + exact f.
  Defined.


  (** ** Dinatural transformations *)
  Section Dinatural.

    Context {C : precategory}.

    (** A dinatural transformation is given by a family of morphisms f(a,a) → g(a,a) in the
    category E. *)
    Definition dinatural_transformation_data (f : C ↛ C) (g : C ↛ C) : UU :=
      ∏ x : C , f (x ⊗ x) --> g (x ⊗ x).

    Definition is_dinatural {F : C ↛ C} {G : C ↛ C}
               (d : dinatural_transformation_data F G) :=
      ∏ (a b : C) (f : a --> b) , lmap F f · d a · rmap G f = rmap F f · d b · lmap G f.

    (** When the precategory has homsets, this is a proposition. *)
    Lemma isaprop_is_dinatural (hs : has_homsets E)
          {F : C ↛ C} {G : C ↛ C} (d : dinatural_transformation_data F G) : isaprop (is_dinatural d).
    Proof.
      abstract (do 3 (apply impred; intro) ; apply hs).
    Qed.

    Definition dinatural_transformation (f : C ↛ C) (g : C ↛ C) : UU :=
      ∑ d : dinatural_transformation_data f g , is_dinatural d.

    Definition make_dinatural_transformation {F : C ↛ C} {G : C ↛ C}
               (data : dinatural_transformation_data F G)
               (is_dinat : is_dinatural data) : dinatural_transformation F G.
    Proof.
      use tpair.
      - assumption.
      - assumption.
    Defined.

    Section Accessors.
      Context {f : C ↛ C} {g : C ↛ C} (d : dinatural_transformation f g).

      Definition dinatural_transformation_get_data :
        ∏ a : C, f (a ⊗ a) --> g (a ⊗ a) := pr1 d.

      Definition dinatural_transformation_is_dinatural :
        is_dinatural dinatural_transformation_get_data := pr2 d.
    End Accessors.

    Coercion dinatural_transformation_get_data : dinatural_transformation >-> Funclass.

    (** See below for the non-local notation *)
    Local Notation "F ⇏ G" := (dinatural_transformation F G) (at level 39) : cat.

    (** *** Dinatural transformation from a natural transformation *)

    Lemma nat_trans_to_dinatural_transformation {f : C ↛ C} {g : C ↛ C}
          (alpha : nat_trans f g) : f ⇏ g.
    Proof.
      use make_dinatural_transformation.
      - intro; apply alpha.
      - intros a b h. simpl.
        (**
         Have:
         <<
                    F (i, j)
           F(a, b) --------> F(c, d)
              |                 |
              | alpha a b       | alpha c d
              V                 V
           G(a, b) --------> G(c, d)
                    G (i, j)
         >>
         Want:
         <<
                    F(a, a) -- alpha --> G(a, a)
              lmap /                        \ rmap
            F(b, a)                    G(a, b)
              rmap \                        / lmap
                    F(b, b) -- alpha --> G(b, b)
         >>
         *)
        unfold lmap, rmap.

        do 2 (
          symmetry;
          refine (maponpaths (fun z => z · _) (pr2 alpha _ _ _) @ _);
          refine (!assoc _ _ _ @ _);
          refine (!maponpaths (fun z => _ · z) (functor_comp g _ _) @ _);
          unfold compose at 2;
          simpl; cbn;
          do 2 (try rewrite id_left; try rewrite id_right)
        ).

        apply idpath.
    Qed.

  End Dinatural.

  Notation "F ⇏ G" := (dinatural_transformation F G) (at level 39) : cat.

  (** ** (Co)ends *)

  Section Ends.

    Context {C : precategory}.
    Context (F : C ↛ C).

    (** *** Wedges *)

    (** Wedge diagram:
          <<
              w -----> F(a, a)
              |           |
              | F(f, id)  | F(id, f)
              V           V
            F(b, b) --> F(a, b)
          >>
     *)

    Definition is_wedge (w : ob E) (pi : ∏ a : ob C, w --> F (a ⊗ a)) : UU :=
      ∏ (a b : C) (f : a --> b) , pi a · rmap F f = pi b · lmap F f.

    Lemma isaprop_is_wedge (hs : has_homsets E) (w : ob E) (pi : ∏ a : ob C, w --> F (a ⊗ a))
      : isaprop (is_wedge w pi).
    Proof.
      do 3 (apply impred; intro).
      apply hs.
    Qed.

    (** Following the convention for limits, the tip is explicit in the type. *)
    Definition wedge (w : ob E) : UU :=
      ∑ pi : (∏ a : ob C, w --> F (a ⊗ a)), is_wedge w pi.

    Definition make_wedge (w : ob E) (pi : (∏ a : ob C, (w : ob E) --> F (a ⊗ a))) :
      (∏ (a b : ob C) (f : a --> b), pi a · rmap F f = pi b · lmap F f) -> wedge w.
    Proof.
      intro.
      use tpair.
      - assumption.
      - assumption.
    Qed.

    Definition wedge_pr (w : ob E) (W : wedge w) :
      ∏ a : ob C, w --> F (a ⊗ a) := (pr1 W).

    Coercion wedge_pr : wedge >-> Funclass.

    Definition is_end (w : ob E) (W : wedge w) : UU :=
      ∏ v (V : wedge v), iscontr (∑ f : v --> w, ∏ a , f · W a = V a).

    Lemma isaprop_is_end (w : ob E) (W : wedge w) : isaprop (is_end w W).
    Proof.
      do 2 (apply impred; intro).
      apply isapropiscontr.
    Qed.

    (** This must be capitalized because 'end' is a Coq keyword.
          It also matches the convention for limits. *)
    Definition End : UU := ∑ w W , is_end w W.

    (** **** Accessors/coercions *)

    Definition end_ob (e : End) : ob E  := pr1 e.
    Coercion end_ob : End >-> ob.

    Definition end_wedge (e : End) : wedge e := pr1 (pr2 e).
    Coercion end_wedge : End >-> wedge.

    (** *** Cowedges *)
    Definition is_cowedge (w : ob E) (pi : ∏ a : ob C, F (a ⊗ a) --> w) : UU :=
      ∏ (a b : C) (f : a --> b) , lmap F f · pi a = rmap F f · pi b.

    Lemma isaprop_is_cowedge (hs : has_homsets E) (w : ob E) (pi : ∏ a : ob C, F (a ⊗ a) --> w)
      : isaprop (is_cowedge w pi).
    Proof.
      do 3 (apply impred; intro).
      apply hs.
    Qed.

    Definition cowedge (w : ob E) : UU :=
      ∑ pi : (∏ a : ob C, F (a ⊗ a) --> w), is_cowedge w pi.

    Definition make_cowedge (w : ob E) (pi : (∏ a : ob C, F (a ⊗ a) --> (w : ob E))) :
      (∏ (a b : ob C) (f : a --> b), lmap F f · pi a = rmap F f · pi b) -> cowedge w.
    Proof.
      intro.
      use tpair.
      - assumption.
      - assumption.
    Qed.

    Definition cowedge_pr (w : ob E) (W : cowedge w) :
      ∏ a : ob C, F (a ⊗ a) --> w := (pr1 W).

    Coercion cowedge_pr : cowedge >-> Funclass.

    (** *** Coends *)
    Definition is_coend (w : ob E) (W : cowedge w) : UU :=
      ∏ v (V : cowedge v), iscontr (∑ f : w --> v, ∏ a , W a · f = V a).

    Lemma isaprop_is_coend (w : ob E) (W : cowedge w) : isaprop (is_coend w W).
    Proof.
      do 2 (apply impred; intro).
      apply isapropiscontr.
    Qed.

    Definition Coend : UU := ∑ w W , is_coend w W.

    (** **** Accessors/coercions *)

    Definition coend_ob (e : Coend) : ob E  := pr1 e.
    Coercion coend_ob : Coend >-> ob.

    Definition coend_cowedge (e : Coend) : cowedge e := pr1 (pr2 e).
    Coercion coend_cowedge : Coend >-> cowedge.

  End Ends.

  Notation "∫↓ F" := (End F) (at level 40) : cat.
  Notation "∫↑ F" := (Coend F) (at level 40) : cat.

End Profunctors.

(** *** Coends and ends *)
Section CoendsAndEnds.
  Context {E : precategory}.
  Context {C : precategory}.

  (* This could be defined at the end of PrecatgeoryBinProduct.v *)
  Definition swap_functor {C D : precategory} :
    functor (precategory_binproduct C D) (precategory_binproduct D C) :=
    pair_functor (pr2_functor C D) (pr1_functor C D) □ bindelta_functor (precategory_binproduct C D).

  Definition profunctor_opp (F : profunctor E C C) : profunctor (E^op) C C.
  Proof.
    unfold profunctor in *.
    exact (functor_opp (F □ swap_functor)).
  Defined.

  (* By definition, an end for F : C^op × C → V is a coend for
     F^op : C^op × C ≅ C × C^op → V^op and viceversa. *)
  Proposition coend_is_opposite_end {F : profunctor E C C} (e : Coend E F) : End E^op (profunctor_opp F).
  Proof. exact e. Qed.

  Proposition end_is_opposite_coend {F : profunctor E C C} (e : End E F) : Coend E^op (profunctor_opp F).
  Proof. exact e. Qed.

End CoendsAndEnds.
