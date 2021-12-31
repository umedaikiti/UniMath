Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Sets.
Require Import UniMath.CategoryTheory.Core.Prelude.

Local Open Scope cat.

Section Quotient.

Definition iscongr {C : category} (R : ∏ x y, eqrel (C ⟦ x, y ⟧)) := ∏ (x y z : C) (f f' : x --> y) (g g' : y --> z), (R _ _ f f') -> (R _ _ g g') -> (R _ _ (f · g) (f' · g')).

Definition congrrel (C : category) := ∑ (R : ∏ x y, eqrel (C ⟦ x, y ⟧)), iscongr R.

Definition eqrel_from_congrrel {C : category} (R : congrrel C) : ∏ x y, eqrel (C ⟦ x, y ⟧) := pr1 R.
Coercion eqrel_from_congrrel : congrrel >-> Funclass.

Definition congruence_congrrel {C : category} (R : congrrel C) : iscongr R := pr2 R.

(* copied from UniMath/Topology/Prelim.v *)
Lemma hinhuniv' {P X : UU} :
  isaprop P → (X → P) → (∥ X ∥ → P).
Proof.
  intros HP Hx.
  apply (hinhuniv (P := make_hProp _ HP)).
  exact Hx.
Defined.

Definition quotient_precategory_data {C : category} (R : congrrel C) : precategory_data.
Proof.
  use make_precategory_data.
  - use make_precategory_ob_mor.
    + exact C.
    + intros x y.
      exact (setquot (R x y)).
  - intro x.
    apply setquotpr.
    exact (identity _).
  - simpl.
    intros a b c f.
    assert (X : isaset (setquot (R b c) → setquot (R a c))).
    {
      apply impred_isaset.
      intro.
      apply isasetsetquot.
    }
    use (setquotuniv (R a b) (_,,X) _ _ f).
    + simpl.
      intros f' g.
      use (setquotuniv (R b c) (_,, isasetsetquot (R a c)) (λ g, setquotpr (R a c) (f' · g)) _ g).
      intros x y H.
      apply iscompsetquotpr.
      apply congruence_congrrel.
      * apply eqrelrefl.
      * assumption.
    + intros f' f'' H.
      apply funextsec.
      intro g.
      use (hinhuniv' _ _ (issurjsetquotpr (R b c) g)).
      * apply isasetsetquot.
      * intro g'.
        induction g' as [g' H0].
        rewrite <- H0.
        rewrite !setquotunivcomm.
        apply iscompsetquotpr.
        apply congruence_congrrel.
        assumption.
        apply eqrelrefl.
Defined.

Definition quotient_precategory {C : category} (R : congrrel C) : precategory.
Proof.
  use make_precategory.
  - exact (quotient_precategory_data R).
  - repeat split; simpl.
    + intros a b f.
      use (hinhuniv' (isasetsetquot _ _ _) _ (issurjsetquotpr _ f)).
      intro X; induction X as [f' X]; rewrite <- !X; clear X.
      unfold compose, identity.
      simpl.
      rewrite !setquotunivcomm.
      rewrite id_left.
      reflexivity.
    + intros a b f.
      use (hinhuniv' (isasetsetquot _ _ _) _ (issurjsetquotpr _ f)).
      intro X; induction X as [f' X]; rewrite <- !X; clear X.
      unfold compose, identity.
      simpl.
      rewrite !setquotunivcomm.
      rewrite id_right.
      reflexivity.
    + intros a b c d f g h.
      use (hinhuniv' (isasetsetquot _ _ _) _ (issurjsetquotpr _ f)).
      intro X; induction X as [f' X]; rewrite <- !X; clear X.
      use (hinhuniv' (isasetsetquot _ _ _) _ (issurjsetquotpr _ g)).
      intro X; induction X as [g' X]; rewrite <- !X; clear X.
      use (hinhuniv' (isasetsetquot _ _ _) _ (issurjsetquotpr _ h)).
      intro X; induction X as [h' X]; rewrite <- !X; clear X.
      unfold compose, identity.
      simpl.
      rewrite !setquotunivcomm.
      rewrite assoc.
      reflexivity.
    + intros a b c d f g h.
      use (hinhuniv' (isasetsetquot _ _ _) _ (issurjsetquotpr _ f)).
      intro X; induction X as [f' X]; rewrite <- !X; clear X.
      use (hinhuniv' (isasetsetquot _ _ _) _ (issurjsetquotpr _ g)).
      intro X; induction X as [g' X]; rewrite <- !X; clear X.
      use (hinhuniv' (isasetsetquot _ _ _) _ (issurjsetquotpr _ h)).
      intro X; induction X as [h' X]; rewrite <- !X; clear X.
      unfold compose, identity.
      simpl.
      rewrite !setquotunivcomm.
      rewrite assoc.
      reflexivity.
Defined.

Definition quotient_category {C : category} (R : congrrel C) : category.
Proof.
  use make_category.
  - exact (quotient_precategory R).
  - intros x y.
    simpl.
    apply isasetsetquot.
Defined.

End Quotient.