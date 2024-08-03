(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

From Coq Require Import Arith Lia List Utf8.

From KruskalTrees
  Require Import list_utils.


Set Implicit Arguments.

Import ListNotations.

#[global] Notation "↓ φ" := (λ n, φ (S n)) (at level 0, right associativity, format "↓ φ").
#[global] Notation "a ⋅ φ" := (λ n, match n with 0 => a | S n => φ n end) (at level 0, right associativity, format "a ⋅ φ").

#[global] Reserved Notation "ω ⁺¹" (at level 1, left associativity, format "ω ⁺¹").
#[global] Reserved Notation "φ ↗ t " (at level 2, no associativity, format "φ ↗ t").

#[global] Reserved Notation "⟨ φ | n ⟩" (at level 0, no associativity, format "⟨ φ | n ⟩").

Section pfx_rev.

  Variables (X : Type).

  Implicit Type (φ : nat → X).

  (* ⟨φ|n⟩ = [φₙ₋₁;...;φ₀] *)

  Fixpoint pfx_rev φ n :=
    match n with
    | 0   => []
    | S n => φ n :: ⟨φ|n⟩
    end
  where "⟨ φ | n ⟩" := (pfx_rev φ n).

  Fact pfx_rev_plus φ n m : ⟨φ|n+m⟩ = ⟨λ i, φ (m+i)|n⟩ ++ ⟨φ|m⟩.
  Proof. induction n; simpl; do 2 f_equal; auto; lia. Qed.

  Fact pfx_rev_S φ n : ⟨φ|S n⟩ = ⟨↓φ|n⟩ ++ [φ 0].
  Proof.
    replace (S n) with (n+1) by lia.
    now rewrite pfx_rev_plus.
  Qed.

End pfx_rev.

Arguments pfx_rev {X}.

#[global] Notation "⟨ φ | n ⟩" := (pfx_rev φ n).

Section WFT_tools.

  (** Infinitely branching well founded trees *)

  Variables (X : Type).

  (* X-indexed well founded trees, possibly infinitely branching *)
  Inductive WFT := 
    | leaf : WFT
    | node : (X → WFT) → WFT.

  Implicit Types (φ : nat → X)
                 (ω : WFT).

  Fixpoint WFT_ht φ ω :=
    match ω with
    | leaf   => 0
    | node ρ => 1 + ↓φ↗(ρ (φ 0))
    end
  where "φ ↗ ω" := (WFT_ht φ ω).

  Definition ω₁ : WFT := node (λ _, leaf).

  Fact WFT_ht_ω₁ φ : φ↗ω₁ = 1.
  Proof. reflexivity. Qed.

  Fixpoint WFT_lift ω :=
    match ω with
    | leaf   => ω₁
    | node ρ => node (λ a, (ρ a)⁺¹)
    end
  where "ω ⁺¹" := (WFT_lift ω).

  Fact WFT_lift_ht φ ω : φ↗ω⁺¹ = 1 + φ↗ω.
  Proof. induction ω in φ |- *; simpl; auto. Qed.

  (** We give the semantics of a WFT in terms of Wim Veldman stumps, that it
      sets of finite sequences of X representing the finite branches of a WFT *)
  Fixpoint stump ω : list X → Prop :=
    match ω with 
    | leaf   => λ _, False
    | node ρ => λ l, l = [] ∨ ∃ x l', l = l'++[x] ∧ stump (ρ x) l'
    end.

  (** The height of an infinite branch is larger that the length of 
      its prefixes that also belong to the stump *)
  Fact stump_ht ω φ n : stump ω ⟨φ|n⟩ → n < φ↗ω.
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

  Fact stump_pfx_rev ω φ : stump ω⁺¹ ⟨φ|φ↗ω⟩.
  Proof.
    induction ω as [ | ρ IH ] in φ |- *.
    + now left.
    + right.
      exists (φ 0), ⟨↓φ|↓φ↗(ρ (φ 0))⟩.
      simpl WFT_ht.
      rewrite pfx_rev_S; auto.
  Qed.

  Fact stump_empty_dec ω : stump ω [] ∨ stump ω = λ _, False.
  Proof. destruct ω; simpl; auto. Qed.

  Fact stump_cons_inv ω x r : stump ω (x::r) → stump ω r.
  Proof.
    induction ω as [ | ρ IH ] in x, r |- *; simpl; auto.
    intros [ | (z & [ | u m ] & E & H) ]; try easy.
    * inversion E; auto.
    * inversion E; subst u r.
      right; eauto.
  Qed.

  Fact stump_app_inv ω l r : stump ω (l++r) → stump ω r.
  Proof.
    induction l; simpl; auto.
    intros ?%stump_cons_inv; eauto.
  Qed.

  Fact stump_inv_nil ω l : stump ω l → stump ω [].
  Proof. rewrite <- (app_nil_r l); apply stump_app_inv. Qed.

  Fact stump_dec ω : ∀l, stump ω l ∨ ¬ stump ω l.
  Proof.
    induction ω as [ | ρ IHρ ]; simpl.
    + now right.
    + intros l.
      destruct (list_snoc_inv l) as [ -> | (m & x & ->) ]; auto.
      destruct (IHρ x m).
      * left; right; eauto.
      * right; intros [ | (z & m' & E & ?) ].
        - now destruct m.
        - now apply app_inj_tail_iff in E as (<- & <-).
  Qed.

  Inductive lt_WFT : WFT → WFT → Prop :=
    | lt_WFT_intro ρ a : lt_WFT (ρ a) (node ρ).

  Fact lt_WFT_well_founded : well_founded lt_WFT.
  Proof. intros t; induction t; constructor; inversion 1; trivial. Qed.

End WFT_tools.

Arguments leaf {X}.
Arguments node {X} _.

#[global] Notation "φ ↗ ω" := (WFT_ht φ ω).
#[global] Notation "ω ⁺¹" := (WFT_lift ω).

