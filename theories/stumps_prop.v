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

Set Implicit Arguments.

Import lift_notations ListNotations.

Notation "↓ φ" := (λ n, φ (S n)) (at level 0, right associativity, format "↓ φ").
Notation "a ⋅ φ" := (λ n, match n with 0 => a | S n => φ n end) (at level 0, right associativity, format "a ⋅ φ").

Reserved Notation "t ⁺¹" (at level 1, left associativity, format "t ⁺¹").
Reserved Notation "φ ↗ t " (at level 2, no associativity, format "φ ↗ t").

(* X-indexed well founded trees, possibly infinitely branching *)
Inductive WFT X := 
  | leaf : WFT X
  | node : (X → WFT X) → WFT X.

Arguments leaf {X}.
Arguments node {X} _.

Section WFT.

  (* Infinitely branching well founded trees *)

  Variables (X : Type).

  Implicit Types (R : rel₂ X)
                 (P : rel₁ (list X)) 
                 (φ : nat → X)
                 (ω : WFT X).

  Fixpoint WFT_ht φ ω :=
    match ω with
    | leaf   => 0
    | node ρ => 1 + ↓φ↗(ρ (φ 0))
    end
  where "φ ↗ t" := (WFT_ht φ t).

  Definition ω₁ : WFT X := node (λ _, leaf).

  Fact WFT_ht_ω₁ φ : φ↗ω₁ = 1.
  Proof. reflexivity. Qed.

  Fixpoint WFT_lift ω :=
    match ω with
    | leaf   => ω₁
    | node ρ => node (λ a, (ρ a)⁺¹)
    end
  where "t ⁺¹" := (WFT_lift t).

  Fact WFT_lift_ht φ ω : φ↗ω⁺¹ = 1 + φ↗ω.
  Proof. induction ω in φ |- *; simpl; auto. Qed.

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

  Fact bar_secures_lift R x l ω : bar_secures (good R↑x) l ω → bar_secures (good R) (l++[x]) ω.
  Proof.
    induction ω as [ | ρ IH ] in R, x, l |- *; simpl.
    + apply good_rel_lift.
    + intros H ?; apply IH with (1 := H _).
  Qed.

  Fact af_secures_bar_secures R ω : af_secures R ω → bar_secures (good R) [] (ω⁺¹⁺¹).
  Proof.
    induction ω as [ | ρ IH ] in R |- *; simpl.
    + intros ? x ?; constructor 1 with x; simpl; auto.
    + intros H ?; apply bar_secures_lift with (l := []), IH, H.
  Qed.

  Fact bar_secures_bound P l ω φ : bar_secures P l ω → P (pfx_rev φ φ↗ω ++ l).
  Proof.
    induction ω as [ | ρ IH ] in l, φ |- *; intros HP; auto.
    simpl WFT_ht; rewrite pfx_rev_S, app_ass.
    apply IH, HP.
  Qed.

  Fact bar_secures_nil_bound P ω φ : bar_secures P [] ω → P (pfx_rev φ φ ↗ ω).
  Proof. intros; rewrite app_nil_end; now apply bar_secures_bound. Qed.

  Fact bar_secures_af_secures R l ω : bar_secures (good R) l ω → af_secures (R⇈l) ω.
  Proof.
    induction ω as [ | ρ IH ] in l |- *; simpl.
    + intros; apply rel_lift_rel_iff_good; auto.
    + intros; now apply IH with (l := _::_).
  Qed.

  Lemma af_secures_good_bound R ω φ : af_secures R ω → good R (pfx_rev φ φ↗ω⁺¹⁺¹).
  Proof. now intros; apply bar_secures_nil_bound, af_secures_bar_secures. Qed.

  Local Remark good_vs_good_pairs R φ n : good R (pfx_rev φ n) ↔ ∃ i j, i < j < n ∧ R (φ i) (φ j).
  Proof. apply good_pfx_rev. Qed.

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
  Theorem WFT_P_barP P l ω : (∀φ, P (pfx_rev φ φ↗ω⁺¹ ++ l)) → bar_secures P l ω⁺¹.
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

  Lemma WFT_good_af R ω : (∀φ, good R (pfx_rev φ φ↗ω)) → af_secures R ω⁺¹.
  Proof.
    intros H.
    apply bar_secures_af_secures with (l := []), WFT_P_barP.
    intro phi; rewrite <- app_nil_end, WFT_lift_ht; constructor 2; auto.
  Qed.

  Theorem afₛ_secures_af_secures R ω : afₛ_secures R ω → af_secures R ω⁺¹.
  Proof.
    intros H; apply WFT_good_af.
    intro; apply good_pfx_rev, H.
  Qed.

  Corollary afₛ_secures_iff_af_secures R : (∃ω, afₛ_secures R ω) ↔ (∃ω, af_secures R ω).
  Proof.
    split.
    + intros (ω & ?); exists ω⁺¹; now apply afₛ_secures_af_secures.
    + intros (ω & ?); exists ω⁺¹⁺¹; now apply af_secures_afₛ_secures.
  Qed.

 (** We give the semantics of a WFT in terms of Wim Veldman stumps, that it
      sets of finite sequences of X representing the finite branches of a WFT *)
  Fixpoint stump ω : list X → Prop :=
    match ω with 
    | leaf   => λ _, False
    | node ρ => λ l, l = [] ∨ ∃ x l', l = l'++[x] ∧ stump (ρ x) l'
    end.

  (** The height of an infinite branch is larger that the length of 
      its prefixes that also belong to the stump *)
  Fact stump_ht ω φ n : stump ω (pfx_rev φ n) → n < φ↗ω.
  Proof.
    induction ω as [ | ρ IH ] in φ, n |- *; simpl.
    + easy.
    + intros [ E | (x & l' & E & H) ].
      * destruct n; lia || easy.
      * destruct n as [ | n ].
        1: now destruct l'.
        rewrite pfx_rev_S in E.
        apply app_inj_tail in E as []; subst.
        apply IH in H; lia.
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
      + exists (WFT_lift t); now apply WFT_good_af.
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

End WFT.

