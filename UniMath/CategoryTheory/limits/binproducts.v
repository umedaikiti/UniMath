(** * Direct implementation of binary products

Written by: Benedikt Ahrens, Ralph Matthes
Extended by: Anders Mörtberg and Tomi Pannila
Extended by: Langston Barrett (@siddharthist), 2018

*)

(** ** Contents

- Definition of binary products
- Definition of binary product functor ([binproduct_functor])
- Definition of a binary product structure on a functor category by taking
  pointwise binary products in the target category ([BinProducts_functor_precat])
- Binary products from limits ([BinProducts_from_Lims])
- Equivalent universal property: [(C --> A) × (C --> B) ≃ (C --> A × B)]
- Terminal object as the unit (up to isomorphism) of binary products

 *)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.MoreFoundations.PartA.
Require Import UniMath.MoreFoundations.Tactics.
Require Import UniMath.MoreFoundations.WeakEquivalences.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.limits.terminal.
Require Import UniMath.CategoryTheory.limits.zero.
Require Import UniMath.CategoryTheory.limits.graphs.colimits.
Require Import UniMath.CategoryTheory.limits.graphs.limits.
Require Import UniMath.CategoryTheory.FunctorCategory.

Local Open Scope cat.

(** ** Definition of binary products *)
Section binproduct_def.

Variable C : category.

Definition isBinProduct (c d p : C) (p1 : p --> c) (p2 : p --> d) : UU :=
  ∏ (a : C) (f : a --> c) (g : a --> d),
  ∃! fg, (fg · p1 = f) × (fg · p2 = g).

Lemma isaprop_isBinProduct (c d p : C) (p1 : p --> c) (p2 : p --> d) :
  isaprop (isBinProduct c d p p1 p2).
Proof.
  do 3 (apply impred_isaprop; intro).
  apply isapropiscontr.
Qed.

Definition BinProduct (c d : C) : UU :=
  ∑ pp1p2 : (∑ p : C, (p --> c) × (p --> d)),
    isBinProduct c d (pr1 pp1p2) (pr1 (pr2 pp1p2)) (pr2 (pr2 pp1p2)).

Definition BinProducts : UU := ∏ (c d : C), BinProduct c d.
Definition hasBinProducts : UU := ∏ (c d : C), ∥ BinProduct c d ∥.

Definition BinProductObject {c d : C} (P : BinProduct c d) : C := pr1 (pr1 P).
Definition BinProductPr1 {c d : C} (P : BinProduct c d): BinProductObject P --> c :=
  pr1 (pr2 (pr1 P)).
Definition BinProductPr2 {c d : C} (P : BinProduct c d) : BinProductObject P --> d :=
   pr2 (pr2 (pr1 P)).

Definition isBinProduct_BinProduct {c d : C} (P : BinProduct c d) :
   isBinProduct c d (BinProductObject P) (BinProductPr1 P) (BinProductPr2 P).
Proof.
  exact (pr2 P).
Defined.

Definition BinProductArrow {c d : C} (P : BinProduct c d) {a : C} (f : a --> c) (g : a --> d) :
       a --> BinProductObject P.
Proof.
  exact (pr1 (pr1 (isBinProduct_BinProduct P _ f g))).
Defined.

Lemma BinProductPr1Commutes (c d : C) (P : BinProduct c d):
     ∏ (a : C) (f : a --> c) g, BinProductArrow P f g · BinProductPr1 P = f.
Proof.
  intros a f g.
  exact (pr1 (pr2 (pr1 (isBinProduct_BinProduct P _ f g)))).
Qed.

Lemma BinProductPr2Commutes (c d : C) (P : BinProduct c d):
     ∏ (a : C) (f : a --> c) g, BinProductArrow P f g · BinProductPr2 P = g.
Proof.
  intros a f g.
  exact (pr2 (pr2 (pr1 (isBinProduct_BinProduct P _ f g)))).
Qed.

Lemma BinProductArrowUnique (c d : C) (P : BinProduct c d) (x : C)
    (f : x --> c) (g : x --> d) (k : x --> BinProductObject P) :
    k · BinProductPr1 P = f -> k · BinProductPr2 P = g ->
      k = BinProductArrow P f g.
Proof.
  intros H1 H2.
  set (H := tpair (λ h, dirprod _ _ ) k (make_dirprod H1 H2)).
  set (H' := (pr2 (isBinProduct_BinProduct P _ f g)) H).
  apply (base_paths _ _ H').
Qed.

Lemma BinProductArrowsEq (c d : C) (P : BinProduct c d) (x : C)
      (k1 k2 : x --> BinProductObject P) :
  k1 · BinProductPr1 P = k2 · BinProductPr1 P ->
  k1 · BinProductPr2 P = k2 · BinProductPr2 P ->
  k1 = k2.
Proof.
  intros H1 H2.
  set (p1 := k1 · BinProductPr1 P).
  set (p2 := k1 · BinProductPr2 P).
  rewrite (BinProductArrowUnique _ _ P _ p1 p2 k1).
  apply pathsinv0.
  apply BinProductArrowUnique.
  unfold p1. apply pathsinv0. apply H1.
  unfold p2. apply pathsinv0. apply H2.
  apply idpath. apply idpath.
Qed.

Definition make_BinProduct (a b : C) :
  ∏ (c : C) (f : C⟦c,a⟧) (g : C⟦c,b⟧),
   isBinProduct _ _ _ f g -> BinProduct a b.
Proof.
  intros.
  use tpair.
  - exists c.
    exists f.
    exact g.
  - exact X.
Defined.

Definition make_isBinProduct (a b p : C)
  (pa : C⟦p,a⟧) (pb : C⟦p,b⟧) :
  (∏ (c : C) (f : C⟦c,a⟧) (g : C⟦c,b⟧),
    ∃! k : C⟦c,p⟧, k · pa = f × k · pb = g) ->
  isBinProduct a b p pa pb.
Proof.
  intros H c cc g.
  apply H.
Defined.

Lemma BinProductArrowEta (c d : C) (P : BinProduct c d) (x : C)
    (f : x --> BinProductObject P) :
    f = BinProductArrow P (f · BinProductPr1 P) (f · BinProductPr2 P).
Proof.
  apply BinProductArrowUnique;
  apply idpath.
Qed.


Definition BinProductOfArrows {c d : C} (Pcd : BinProduct c d) {a b : C}
    (Pab : BinProduct a b) (f : a --> c) (g : b --> d) :
          BinProductObject Pab --> BinProductObject Pcd :=
    BinProductArrow Pcd (BinProductPr1 Pab · f) (BinProductPr2 Pab · g).

Lemma BinProductOfArrowsPr1 {c d : C} (Pcd : BinProduct c d) {a b : C}
    (Pab : BinProduct a b) (f : a --> c) (g : b --> d) :
    BinProductOfArrows Pcd Pab f g · BinProductPr1 Pcd = BinProductPr1 Pab · f.
Proof.
  unfold BinProductOfArrows.
  rewrite BinProductPr1Commutes.
  apply idpath.
Qed.

Lemma BinProductOfArrowsPr2 {c d : C} (Pcd : BinProduct c d) {a b : C}
    (Pab : BinProduct a b) (f : a --> c) (g : b --> d) :
    BinProductOfArrows Pcd Pab f g · BinProductPr2 Pcd = BinProductPr2 Pab · g.
Proof.
  unfold BinProductOfArrows.
  rewrite BinProductPr2Commutes.
  apply idpath.
Qed.


Lemma postcompWithBinProductArrow {c d : C} (Pcd : BinProduct c d) {a b : C}
    (Pab : BinProduct a b) (f : a --> c) (g : b --> d)
    {x : C} (k : x --> a) (h : x --> b) :
        BinProductArrow Pab k h · BinProductOfArrows Pcd Pab f g =
         BinProductArrow Pcd (k · f) (h · g).
Proof.
  apply BinProductArrowUnique.
  - rewrite <- assoc, BinProductOfArrowsPr1.
    rewrite assoc, BinProductPr1Commutes.
    apply idpath.
  - rewrite <- assoc, BinProductOfArrowsPr2.
    rewrite assoc, BinProductPr2Commutes.
    apply idpath.
Qed.


Lemma precompWithBinProductArrow {c d : C} (Pcd : BinProduct c d) {a : C}
    (f : a --> c) (g : a --> d) {x : C} (k : x --> a)  :
       k · BinProductArrow Pcd f g  = BinProductArrow Pcd (k · f) (k · g).
Proof.
  apply BinProductArrowUnique.
  -  rewrite <- assoc, BinProductPr1Commutes;
     apply idpath.
  -  rewrite <- assoc, BinProductPr2Commutes;
     apply idpath.
Qed.

End binproduct_def.


Section BinProducts.

Variable C : category.
Variable CC : BinProducts C.
Variables a b c d x y : C.

Definition BinProductOfArrows_comp (f : a --> c) (f' : b --> d) (g : c --> x) (g' : d --> y)
  : BinProductOfArrows _ (CC c d) (CC a b) f f' ·
    BinProductOfArrows _ (CC _ _) (CC _ _) g g'
    =
    BinProductOfArrows _ (CC _ _) (CC _ _)(f · g) (f' · g').
Proof.
  apply BinProductArrowUnique.
  - rewrite <- assoc.
    rewrite BinProductOfArrowsPr1.
    rewrite assoc.
    rewrite BinProductOfArrowsPr1.
    apply pathsinv0.
    apply assoc.
  - rewrite <- assoc.
    rewrite BinProductOfArrowsPr2.
    rewrite assoc.
    rewrite BinProductOfArrowsPr2.
    apply pathsinv0.
    apply assoc.
Qed.

End BinProducts.

Section BinProduct_unique.

Variable C : category.
Variable CC : BinProducts C.
Variables a b : C.

Lemma BinProduct_endo_is_identity (P : BinProduct _ a b)
  (k : BinProductObject _ P --> BinProductObject _ P)
  (H1 : k · BinProductPr1 _ P = BinProductPr1 _ P)
  (H2 : k · BinProductPr2 _ P = BinProductPr2 _ P)
  : identity _ = k.
Proof.
  apply pathsinv0.
  eapply pathscomp0.
  apply BinProductArrowEta.
  apply pathsinv0.
  apply BinProductArrowUnique; apply pathsinv0.
  + rewrite id_left. exact H1.
  + rewrite id_left. exact H2.
Qed.

End BinProduct_unique.

(** ** Binary products from limits ([BinProducts_from_Lims]) *)

Section BinProducts_from_Lims.

Variables (C : category).

Definition two_graph : graph := (bool,,λ _ _,empty).

Definition binproduct_diagram (a b : C) : diagram two_graph C.
Proof.
exists (λ x : bool, if x then a else b).
abstract (intros u v F; induction F).
Defined.

Definition Binproduct {a b c : C} (f : c --> a) (g : c --> b) :
  cone (binproduct_diagram a b) c.
Proof.
use make_cone; simpl.
+ intros x; induction x; assumption.
+ abstract (intros x y e; destruct e).
Defined.

Lemma BinProducts_from_Lims : Lims_of_shape two_graph C -> BinProducts C.
Proof.
intros H a b.
set (LC := H (binproduct_diagram a b)); simpl.
use make_BinProduct.
+ apply (lim LC).
+ apply (limOut LC true).
+ apply (limOut LC false).
+ apply (make_isBinProduct C); simpl; intros c f g.
  use unique_exists; simpl.
  - apply limArrow, (Binproduct f g).
  - abstract (split;
      [ apply (limArrowCommutes LC c (Binproduct f g) true)
      | apply (limArrowCommutes LC c (Binproduct f g) false) ]).
  - abstract (intros h; apply isapropdirprod; apply C).
  - abstract (now intros h [H1 H2]; apply limArrowUnique; intro x; induction x).
Defined.

End BinProducts_from_Lims.

Section test.

Variable C : category.
Variable H : BinProducts C.
Arguments BinProductObject [C] c d {_}.
Local Notation "c 'x' d" := (BinProductObject  c d )(at level 5).
(*
Check (λ c d : C, c x d).
*)
End test.

(** ** Definition of binary product functor ([binproduct_functor]) *)

Section binproduct_functor.

Context {C : category} (PC : BinProducts C).

Definition binproduct_functor_data :
  functor_data (category_binproduct C C) C.
Proof.
use tpair.
- intros p.
  apply (BinProductObject _ (PC (pr1 p) (pr2 p))).
- simpl; intros p q f.
  apply (BinProductOfArrows _ (PC (pr1 q) (pr2 q))
                           (PC (pr1 p) (pr2 p)) (pr1 f) (pr2 f)).
Defined.

Definition binproduct_functor : functor (category_binproduct C C) C.
Proof.
apply (tpair _ binproduct_functor_data).
abstract (split;
  [ intro x; simpl; apply pathsinv0, BinProduct_endo_is_identity;
    [ now rewrite BinProductOfArrowsPr1, id_right
    | now rewrite BinProductOfArrowsPr2, id_right ]
  | now intros x y z f g; simpl; rewrite BinProductOfArrows_comp]).
Defined.

End binproduct_functor.

(* Defines the product of two functors by:
    x -> (x,x) -> (F x,G x) -> F x * G x

  For a direct definition see FunctorsPointwiseBinProduct.v

*)
Definition BinProduct_of_functors_alt {C D : category} (HD : BinProducts D)
  (F G : functor C D) : functor C D :=
  functor_composite (bindelta_functor C)
     (functor_composite (pair_functor F G) (binproduct_functor HD)).


(** In the following section we show that if the morphism to components are
    zero, then the unique morphism factoring through the binproduct is the
    zero morphism. *)
Section BinProduct_zeroarrow.

  Variable C : category.
  Variable Z : Zero C.

  Lemma BinProductArrowZero {x y z: C} {BP : BinProduct C x y} (f : z --> x) (g : z --> y) :
    f = ZeroArrow Z _ _ -> g = ZeroArrow Z _ _ -> BinProductArrow C BP f g = ZeroArrow Z _ _ .
  Proof.
    intros X X0. apply pathsinv0.
    use BinProductArrowUnique.
    rewrite X. apply ZeroArrow_comp_left.
    rewrite X0. apply ZeroArrow_comp_left.
  Qed.

End BinProduct_zeroarrow.

(** ** Definition of a binary product structure on a functor category *)

(** Goal: lift binary products from the target (pre)category to the functor (pre)category *)
Section def_functor_pointwise_binprod.

Variable C D : category.
Variable HD : BinProducts D.

Section BinProduct_of_functors.

Variables F G : functor C D.


Local Notation "c ⊗ d" := (BinProductObject _ (HD c d)).

Definition BinProduct_of_functors_ob (c : C) : D := F c ⊗ G c.

Definition BinProduct_of_functors_mor (c c' : C) (f : c --> c')
  : BinProduct_of_functors_ob c --> BinProduct_of_functors_ob c'
  := BinProductOfArrows _ _ _ (#F f) (#G f).

Definition BinProduct_of_functors_data : functor_data C D.
Proof.
  exists BinProduct_of_functors_ob.
  exact BinProduct_of_functors_mor.
Defined.

Lemma is_functor_BinProduct_of_functors_data : is_functor BinProduct_of_functors_data.
Proof.
  split; simpl; intros.
  - red; intros; simpl in *.
    apply pathsinv0.
    unfold BinProduct_of_functors_mor.
    apply BinProduct_endo_is_identity.
    + rewrite BinProductOfArrowsPr1.
      rewrite functor_id.
      apply id_right.
    + rewrite BinProductOfArrowsPr2.
      rewrite functor_id.
      apply id_right.
  - red; intros; simpl in *.
    unfold BinProduct_of_functors_mor.
    do 2 rewrite functor_comp.
    apply pathsinv0.
    apply BinProductOfArrows_comp.
Qed.

Definition BinProduct_of_functors : functor C D :=
  tpair _ _ is_functor_BinProduct_of_functors_data.

Lemma BinProduct_of_functors_alt_eq_BinProduct_of_functors :
  BinProduct_of_functors_alt HD F G = BinProduct_of_functors.
Proof.
now apply (functor_eq _ _ D).
Defined.

Definition binproduct_nat_trans_pr1_data : ∏ c, BinProduct_of_functors c --> F c
  := λ c : C, BinProductPr1 _ (HD (F c) (G c)).

Lemma is_nat_trans_binproduct_nat_trans_pr1_data
  : is_nat_trans _ _ binproduct_nat_trans_pr1_data.
Proof.
  red.
  intros c c' f.
  unfold binproduct_nat_trans_pr1_data.
  unfold BinProduct_of_functors. simpl.
  unfold BinProduct_of_functors_mor.
  apply BinProductOfArrowsPr1.
Qed.

Definition binproduct_nat_trans_pr1 : nat_trans _ _
  := tpair _ _ is_nat_trans_binproduct_nat_trans_pr1_data.


Definition binproduct_nat_trans_pr2_data : ∏ c, BinProduct_of_functors c --> G c
  := λ c : C, BinProductPr2 _ (HD (F c) (G c)).

Lemma is_nat_trans_binproduct_nat_trans_pr2_data
  : is_nat_trans _ _ binproduct_nat_trans_pr2_data.
Proof.
  red.
  intros c c' f.
  unfold binproduct_nat_trans_pr2_data.
  unfold BinProduct_of_functors. simpl.
  unfold BinProduct_of_functors_mor.
  apply BinProductOfArrowsPr2.
Qed.

Definition binproduct_nat_trans_pr2 : nat_trans _ _
  := tpair _ _ is_nat_trans_binproduct_nat_trans_pr2_data.


Section vertex.

(** The product morphism of a diagram with vertex [A] *)

Variable A : functor C D.
Variable f : A ⟹ F.
Variable g : A ⟹ G.

Definition binproduct_nat_trans_data : ∏ c,  A c --> BinProduct_of_functors c.
Proof.
  intro c.
  apply BinProductArrow.
  - exact (f c).
  - exact (g c).
Defined.

Lemma is_nat_trans_binproduct_nat_trans_data : is_nat_trans _ _ binproduct_nat_trans_data.
Proof.
  intros a b k.
  simpl.
  unfold BinProduct_of_functors_mor.
  unfold binproduct_nat_trans_data.
  set (XX:=postcompWithBinProductArrow).
  set (X1 := XX D _ _ (HD (F b) (G b))).
  set (X2 := X1 _ _ (HD (F a) (G a))).
  rewrite X2.
  clear X2 X1 XX.
  set (XX:=precompWithBinProductArrow).
  set (X1 := XX D _ _ (HD (F b) (G b))).
  rewrite X1.
  rewrite (nat_trans_ax f).
  rewrite (nat_trans_ax g).
  apply idpath.
Qed.

Definition binproduct_nat_trans : nat_trans _ _
  := tpair _ _ is_nat_trans_binproduct_nat_trans_data.

Lemma binproduct_nat_trans_Pr1Commutes :
  nat_trans_comp _ _ _ binproduct_nat_trans binproduct_nat_trans_pr1  = f.
Proof.
  apply nat_trans_eq.
  - apply D.
  - intro c; simpl.
    apply BinProductPr1Commutes.
Qed.

Lemma binproduct_nat_trans_Pr2Commutes :
  nat_trans_comp _ _ _ binproduct_nat_trans binproduct_nat_trans_pr2  = g.
Proof.
  apply nat_trans_eq.
  - apply D.
  - intro c; simpl.
    apply BinProductPr2Commutes.
Qed.

End vertex.

Lemma binproduct_nat_trans_univ_prop (A : [C, D])
  (f : (A --> (F:[C,D]))) (g : A --> (G:[C,D])) :
   ∏
   t : ∑ fg : A --> (BinProduct_of_functors:[C,D]),
       fg · (binproduct_nat_trans_pr1 : (BinProduct_of_functors:[C,D]) --> F) = f
      ×
       fg · (binproduct_nat_trans_pr2 : (BinProduct_of_functors:[C,D]) --> G) = g,
   t =
   tpair
     (λ fg : A --> (BinProduct_of_functors:[C,D]),
      fg · (binproduct_nat_trans_pr1 : (BinProduct_of_functors:[C,D]) --> F) = f
   ×
      fg · (binproduct_nat_trans_pr2 : (BinProduct_of_functors:[C,D]) --> G) = g)
     (binproduct_nat_trans A f g)
     (make_dirprod (binproduct_nat_trans_Pr1Commutes A f g)
        (binproduct_nat_trans_Pr2Commutes A f g)).
Proof.
  intro t.
  simpl in *.
  destruct t as [t1 [ta tb]].
  simpl in *.
  apply subtypePath.
  - intro.
    simpl.
    apply isapropdirprod;
    apply isaset_nat_trans;
    apply D.
  - simpl.
    apply nat_trans_eq.
    + apply D.
    + intro c.
      unfold binproduct_nat_trans.
      simpl.
      unfold binproduct_nat_trans_data.
      apply BinProductArrowUnique.
      * apply (nat_trans_eq_pointwise ta).
      * apply (nat_trans_eq_pointwise tb).
Qed.

Definition functor_precat_binproduct_cone
  : BinProduct [C, D] F G.
Proof.
use make_BinProduct.
- apply BinProduct_of_functors.
- apply binproduct_nat_trans_pr1.
- apply binproduct_nat_trans_pr2.
- use make_isBinProduct.
  + intros A f g.
    exists (tpair _ (binproduct_nat_trans A f g)
             (make_dirprod (binproduct_nat_trans_Pr1Commutes _ _ _ )
                          (binproduct_nat_trans_Pr2Commutes _ _ _ ))).
    simpl.
    apply binproduct_nat_trans_univ_prop.
Defined.

End BinProduct_of_functors.

Definition BinProducts_functor_precat : BinProducts [C, D].
Proof.
  intros F G.
  apply functor_precat_binproduct_cone.
Defined.


End def_functor_pointwise_binprod.


(** ** Construction of BinProduct from an isomorphism to BinProduct. *)
Section BinProduct_from_iso.

  Variable C : category.

  Local Lemma iso_to_isBinProduct_comm {x y z : C} (BP : BinProduct C x y)
        (i : iso z (BinProductObject C BP)) (w : C) (f : w --> x) (g : w --> y) :
    (BinProductArrow C BP f g · inv_from_iso i · (i · BinProductPr1 C BP) = f)
      × (BinProductArrow C BP f g · inv_from_iso i · (i · BinProductPr2 C BP) = g).
  Proof.
    split.
    - rewrite <- assoc. rewrite (assoc _ i).
      rewrite (iso_after_iso_inv i). rewrite id_left.
      apply BinProductPr1Commutes.
    - rewrite <- assoc. rewrite (assoc _ i).
      rewrite (iso_after_iso_inv i). rewrite id_left.
      apply BinProductPr2Commutes.
  Qed.

  Local Lemma iso_to_isBinProduct_unique {x y z : C} (BP : BinProduct C x y)
        (i : iso z (BinProductObject C BP)) (w : C) (f : C ⟦w, x⟧) (g : C ⟦w, y⟧) (y0 : C ⟦w, z⟧)
        (T : y0 · (i · BinProductPr1 C BP) = f × y0 · (i · BinProductPr2 C BP) = g) :
    y0 = BinProductArrow C BP f g · iso_inv_from_iso i.
  Proof.
    apply (post_comp_with_iso_is_inj _ _ i (pr2 i)).
    rewrite <- assoc. cbn. rewrite (iso_after_iso_inv i). rewrite id_right.
    apply BinProductArrowUnique.
    - rewrite <- assoc. apply (dirprod_pr1 T).
    - rewrite <- assoc. apply (dirprod_pr2 T).
  Qed.

  Lemma iso_to_isBinProduct {x y z : C} (BP : BinProduct C x y)
        (i : iso z (BinProductObject C BP)) :
    isBinProduct C _ _ z (i · (BinProductPr1 C BP))  (i · (BinProductPr2 C BP)).
  Proof.
    intros w f g.
    use unique_exists.
    (* Arrow *)
    - exact ((BinProductArrow C BP f g) · (iso_inv_from_iso i)).
    (* Commutativity *)
    - exact (iso_to_isBinProduct_comm BP i w f g).
    (* Equality of equalities of morphisms. *)
    - intros y0. apply isapropdirprod. apply C. apply C.
    (* Uniqueness *)
    - intros y0 T. exact (iso_to_isBinProduct_unique BP i w f g y0 T).
  Defined.
  Opaque iso_to_isBinProduct.

  Definition iso_to_BinProduct {x y z : C} (BP : BinProduct C x y)
             (i : iso z (BinProductObject C BP)) :
    BinProduct C x y := make_BinProduct C _ _ z
                                              (i · (BinProductPr1 C BP))
                                              (i · (BinProductPr2 C BP))
                                              (iso_to_isBinProduct BP i).

End BinProduct_from_iso.

(** ** Equivalent universal property: [(C --> A) × (C --> B) ≃ (C --> A × B)]

 Compare to [weqfuntoprodtoprod].
 *)

Section EquivalentDefinition.
  Context {C : category} {c d p : ob C} (p1 : p --> c) (p2 : p --> d).

  Definition postcomp_with_projections (a : ob C) (f : a --> p) :
    (a --> c) × (a --> d) := make_dirprod (f · p1)  (f · p2).

  Definition isBinProduct' : UU := ∏ a : ob C, isweq (postcomp_with_projections a).

  Definition isBinProduct'_weq (is : isBinProduct') :
    ∏ a, (a --> p) ≃ (a --> c) × (a --> d) :=
    λ a, make_weq (postcomp_with_projections a) (is a).

  Lemma isBinProduct'_to_isBinProduct :
    isBinProduct' -> isBinProduct _ _ _ p p1 p2.
  Proof.
    intros isBP' ? f g.
    apply (@iscontrweqf (hfiber (isBinProduct'_weq isBP' _)
                                (make_dirprod f g))).
    - use weqfibtototal; intro; cbn.
      unfold postcomp_with_projections.
      apply pathsdirprodweq.
    - apply weqproperty.
  Defined.

  Lemma isBinProduct_to_isBinProduct' :
    isBinProduct _ _ _ p p1 p2 -> isBinProduct'.
  Proof.
    intros isBP ? fg.
    unfold hfiber, postcomp_with_projections.
    apply (@iscontrweqf (∑ u : C ⟦ a, p ⟧, u · p1 = pr1 fg × u · p2 = pr2 fg)).
    - use weqfibtototal; intro; cbn.
      apply invweq, pathsdirprodweq.
    - exact (isBP a (pr1 fg) (pr2 fg)). (* apply universal property *)
  Defined.

  (* TODO: prove that [isBinProduct'_to_isBinProduct] is an equivalence *)

End EquivalentDefinition.

(** Match non-implicit arguments of [isBinProduct] *)
Arguments isBinProduct' _ _ _ _ _ : clear implicits.

(** ** Terminal object as the unit (up to isomorphism) of binary products *)

(** [T × x ≅ x]*)
Lemma terminal_binprod_unit_l {C : category}
      (T : Terminal C) (BC : BinProducts C) :
  ∏ x : C, is_iso (BinProductPr2 C (BC T x)).
Proof.
  intros x.
  use is_iso_qinv.
  apply BinProductArrow.
  - (** The unique [x -> T] *)
    apply TerminalArrow.
  - apply identity.
  - (** These are inverses *)
    unfold is_inverse_in_precat.
    split; [|apply BinProductPr2Commutes].
    refine (precompWithBinProductArrow _ _ _ _ _ @ _).
    refine (_ @ !BinProductArrowEta _ _ _ _ _ (identity _)).
    apply maponpaths_12.
    + apply TerminalArrowEq.
    + exact (id_right _ @ !id_left _).
Defined.

(** [x × T ≅ x]*)

Lemma terminal_binprod_unit_r {C : category}
      (T : Terminal C) (BC : BinProducts C) :
  ∏ x : C, is_iso (BinProductPr1 C (BC x T)).
Proof.
  intros x.
  use is_iso_qinv.
  apply BinProductArrow.
  - apply identity.
  - (** The unique [x -> T] *)
    apply TerminalArrow.
  - (** These are inverses *)
    unfold is_inverse_in_precat.
    split; [|apply BinProductPr1Commutes].
    refine (precompWithBinProductArrow _ _ _ _ _ @ _).
    refine (_ @ !BinProductArrowEta _ _ _ _ _ (identity _)).
    apply maponpaths_12.
    + exact (id_right _ @ !id_left _).
    + apply TerminalArrowEq.
Defined.
