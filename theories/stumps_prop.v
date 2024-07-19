(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

From Coq Require Import Arith Lia List Utf8.

From KruskalAfProp
  Require Import base notations pfx_rev almost_full.

From KruskalHigmanProp
  Require Import tactics.

Require Import wft.

Set Implicit Arguments.

Import lift_notations ListNotations.

Section af_secure.

  Variables (X : Type).

  Implicit Types (R : rel₂ X)
                 (P Q : rel₁ (list X)) 
                 (φ : nat → X)
                 (ω : WFT X).

  (* Using a WFT as a mesure of the almost fullness of binary relation *)
  Fixpoint af_secures R ω :=
    match ω with
    | leaf   => ∀ x y, R x y
    | node ρ => ∀a, af_secures R↑a (ρ a)
    end.

  Fact af_secures_af R ω : af_secures R ω → af R.
  Proof. 
    induction ω in R |- *; simpl.
    + now constructor 1.
    + constructor 2; eauto.
  Qed.

  (* Using a WFT as a mesure for bar inductive predicates on lists *)
  Definition bar_secures P :=
    fix loop l ω :=
      match ω with
      | leaf   => P l
      | node ρ => ∀a, loop (a::l) (ρ a)
      end.

  Lemma bar_secures_bar P l ω : bar_secures P l ω → bar P l.
  Proof.
    induction ω in l |- *; simpl.
    + now constructor 1.
    + constructor 2; eauto.
  Qed.

  Fact bar_secures_mono P Q : P ⊆₁ Q → bar_secures P ⊆₂ bar_secures Q.
  Proof. intros ? l w; induction w in l |- *; simpl; auto. Qed.

  Local Remark good_vs_good_pairs R φ n : good R (pfx_rev φ n) ↔ ∃ i j, i < j < n ∧ R (φ i) (φ j).
  Proof. apply good_pfx_rev. Qed.

  Fact bar_secures_lift_snoc R x l ω : bar_secures (good R↑x) l ω → bar_secures (good R) (l++[x]) ω.
  Proof.
    induction ω as [ | ρ IH ] in R, x, l |- *; simpl.
    + apply good_rel_lift.
    + intros H ?; apply IH with (1 := H _).
  Qed.

  Fact bar_secures_app P l r ω : bar_secures P (l++r) ω → bar_secures (λ m, P (m++r)) l ω.
  Proof. induction ω in l |- *; simpl; eauto. Qed.

  Fact bar_secures_snoc_lift R x l ω : bar_secures (good R) (l++[x]) ω → bar_secures (good R↑x) l ω⁺¹.
  Proof.
    intros H%bar_secures_app; revert H.
    induction ω in l |- *; simpl; auto.
    apply good_rel_lift_rev.
  Qed.

  Fact bar_secures_bound P l ω φ : bar_secures P l ω → P (pfx_rev φ φ↗ω ++ l).
  Proof.
    induction ω as [ | ρ IH ] in l, φ |- *; intros HP; auto.
    simpl WFT_ht; rewrite pfx_rev_S, app_ass.
    apply IH, HP.
  Qed.

  Fact bar_secures_nil_bound P ω φ : bar_secures P [] ω → P (pfx_rev φ φ↗ω).
  Proof. intros; rewrite app_nil_end; now apply bar_secures_bound. Qed.

  Lemma af_secures_bar_secures R ω : af_secures R ω → bar_secures (good R) [] (ω⁺¹⁺¹).
  Proof.
    induction ω as [ | ρ IH ] in R |- *; simpl.
    + intros ? x ?; constructor 1 with x; simpl; auto.
    + intros H ?; apply bar_secures_lift_snoc with (l := []), IH, H.
  Qed.

  Lemma bar_secures_af_secures R l ω : bar_secures (good R) l ω → af_secures (R⇈l) ω.
  Proof.
    induction ω as [ | ρ IH ] in l |- *; simpl.
    + intros; apply rel_lift_rel_iff_good; auto.
    + intros; now apply IH with (l := _::_).
  Qed.

  Lemma af_secures_good_bound R ω φ : af_secures R ω → good R (pfx_rev φ φ↗ω⁺¹⁺¹).
  Proof. now intros; apply bar_secures_nil_bound, af_secures_bar_secures. Qed.

  Definition afₛ R := ∀φ, ∃ i j, i < j ∧ R (φ i) (φ j).
  Definition afₛ_secures R ω := ∀φ, ∃ i j, i < j < φ↗ω ∧ R (φ i) (φ j).

  Fact afₛ_secures_afₛ R ω : afₛ_secures R ω → afₛ R.
  Proof.
    intros H phi.
    destruct (H phi) as (i & j & [] & ?).
    exists i, j; auto.
  Qed.

  Theorem af_secures_afₛ_secures R ω : af_secures R ω →  afₛ_secures R ω⁺¹⁺¹.
  Proof. intros ? ?; now apply good_pfx_rev, af_secures_good_bound. Qed. 

  (** Remark: we need to lift by 1 to be able to find an inhabitant in X *)
  Theorem WFT_bar_secures P l ω : (∀φ, P (pfx_rev φ φ↗ω⁺¹ ++ l)) → bar_secures P l ω⁺¹.
  Proof.
    induction ω as [ | f IHf ] in l |- *; intros Hf.
    + simpl in Hf |- *.
      intros a; apply (Hf (fun _ => a)).
    + intros a.
      apply IHf.
      intros phi.
      specialize (Hf (a⋅phi)).
      rewrite WFT_lift_ht, pfx_rev_S, app_ass in Hf.
      rewrite WFT_lift_ht; apply Hf.
  Qed.

  Lemma good_af_secures R ω : (∀φ, good R (pfx_rev φ φ↗ω)) → af_secures R ω⁺¹.
  Proof.
    intros H.
    apply bar_secures_af_secures with (l := []), WFT_bar_secures.
    intro phi; rewrite <- app_nil_end, WFT_lift_ht; constructor 2; auto.
  Qed.

  Theorem afₛ_secures_af_secures R ω : afₛ_secures R ω → af_secures R ω⁺¹.
  Proof.
    intros H; apply good_af_secures.
    intro; apply good_pfx_rev, H.
  Qed.

  Corollary afₛ_secures_iff_af_secures R : (∃ω, afₛ_secures R ω) ↔ (∃ω, af_secures R ω).
  Proof.
    split.
    + intros (ω & ?); exists ω⁺¹; now apply afₛ_secures_af_secures.
    + intros (ω & ?); exists ω⁺¹⁺¹; now apply af_secures_afₛ_secures.
  Qed.

  Section using_Brouwer_thesis.

    Hypothesis BT : ∀P,    (∀φ, ∃n, P (pfx_rev φ n))
                      → ∃ω, ∀φ, ∃n, (P ∩₁ (stump ω)) (pfx_rev φ n).

    Theorem Brouwer_thesis_monotonic P :
               (∀ l r, P r → P (l++r))
             → (∀φ, ∃n, P (pfx_rev φ n))
             → ∃ω, ∀φ, P (pfx_rev φ φ↗ω).
    Proof.
      intros Pmono HP.
      destruct (BT P) as (t & Ht); auto.
      exists t; intros phi.
      destruct (Ht phi) as (h & H1 & H2).
      apply stump_ht in H2.
      replace (WFT_ht phi t) with ((WFT_ht phi t-h)+h) by lia.
      rewrite pfx_rev_plus.
      now apply Pmono.
    Qed.

    Theorem Brouwer_af R : afₛ R → ∃ω, af_secures R ω.
    Proof.
      intros HR.
      destruct Brouwer_thesis_monotonic with (P := good R) as (t & Ht).
      + intros; now apply good_app_left.
      + intros phi.
        destruct (HR phi) as (i & j & []).
        exists (S j); apply good_pfx_rev.
        exists i, j; split; auto; lia.
      + exists (WFT_lift t); now apply good_af_secures.
    Qed.

    Theorem Brouwer_afₛ R : afₛ R → ∃ω, afₛ_secures R ω.
    Proof.
      intros (t & Ht)%Brouwer_af.
      exists t⁺¹⁺¹.
      intro; now apply af_secures_afₛ_secures.
    Qed.

  End using_Brouwer_thesis.

  Section using_Fun_Choice.

    Hypothesis FunChoice : ∀(F : X → WFT X → Prop), (∀x, ∃y, F x y) → ∃f, ∀x, F x (f x).

    Fact af_af_secured R : af R → ∃ω, af_secures R ω.
    Proof.
      induction 1 as [ R HR | R _ (f & Hf)%FunChoice ].
      + now exists leaf.
      + exists (node f); assumption.
    Qed.

    Fact bar_bar_secures P l : bar P l → ∃ω, bar_secures P l ω.
    Proof.
      induction 1 as [ | l _ (f & Hf)%FunChoice ].
      + now exists leaf.
      + exists (node f); assumption.
    Qed.

    Theorem bar_brouwer P l : bar P l → ∃ω, ∀φ, P (pfx_rev φ φ↗ω ++ l).
    Proof.
      intros (t & Ht)%bar_bar_secures.
      exists t.
      induction t as [ | f IHf ] in l, Ht |- *; intros phi; simpl in Ht; auto.
      simpl WFT_ht; rewrite pfx_rev_S, app_ass.
      apply IHf with (l := _::l); auto.
    Qed.

    Theorem af_brouwer R : af R → ∃ω, ∀φ, good R (pfx_rev φ φ↗ω).
    Proof.
      intros (t & Ht)%af_iff_bar_good_nil%bar_brouwer.
      exists t; intros phi.
      specialize (Ht phi).
      now rewrite <- app_nil_end in Ht.
    Qed.

  End using_Fun_Choice.

End af_secure.

