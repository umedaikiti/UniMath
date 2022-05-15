Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.limits.binproducts.

Local Open Scope cat.

Section SimpleFibration.

Context (C : category) (B : BinProducts C).

Local Notation "〈 f ',' g 〉" := (BinProductArrow _ f g).

Definition simple_disp_cat_ob_mor : disp_cat_ob_mor C.
Proof.
  use make_disp_cat_ob_mor.
  - intros.
    exact (ob C).
  - intros i j x y u.
    exact (C ⟦ BinProductObject _ (B i x), y ⟧).
Defined.

Definition simple_disp_cat_data : disp_cat_data C.
Proof.
  exists simple_disp_cat_ob_mor.
  split;simpl.
  - intros x y.
    apply BinProductPr2.
  - intros x y z f g xx yy zz ff gg.
    use (_ · gg).
    use BinProductArrow.
    + exact (BinProductPr1 _ _ · f).
    + exact ff.
Defined.

Definition simple_disp_cat : disp_cat C.
Proof.
  exists simple_disp_cat_data.
  repeat split;simpl.
  - intros x y f xx yy ff.
    cbn.
    induction (id_left f).
    rewrite id_right.
    rewrite <- (id_left (BinProductPr1 _ _)).
    rewrite <- (id_left (BinProductPr2 _ _)). 
    rewrite <- BinProductArrowEta.
    rewrite id_left.
    reflexivity.
  - intros x y f xx yy ff.
    cbn.
    induction (id_right f).
    rewrite BinProductPr2Commutes.
    reflexivity.
  - intros x y z w f g h xx yy zz ww ff gg hh.
    cbn.
    induction (assoc f g h).
    cbn.
    rewrite assoc.
    apply cancel_postcomposition.
    use BinProductArrowUnique.
    + rewrite assoc'.
      rewrite BinProductPr1Commutes.
      rewrite assoc.
      rewrite BinProductPr1Commutes.
      apply assoc'.
    + rewrite assoc'.
      rewrite BinProductPr2Commutes.
      reflexivity.
  - intros.
    apply homset_property.
Defined.

Definition simple_fibration : fibration C.
Proof.
  exists simple_disp_cat.
  intros y x f yy.
  exists yy.
  exists (BinProductPr2 _ _).
  intros z g zz hh.
  use unique_exists.
  - exact hh.
  - apply BinProductPr2Commutes.
  - intros.
    apply homset_property.
  - intro gg.
    cbn.
    now rewrite BinProductPr2Commutes.
Defined.

End SimpleFibration.
