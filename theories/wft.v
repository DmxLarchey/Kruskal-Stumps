(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

From Coq Require Import Arith Lia List Utf8.

Set Implicit Arguments.

Import ListNotations.

#[global] Notation "↓ φ" := (λ n, φ (S n)) (at level 0, right associativity, format "↓ φ").
#[global] Notation "a ⋅ φ" := (λ n, match n with 0 => a | S n => φ n end) (at level 0, right associativity, format "a ⋅ φ").

#[global] Reserved Notation "t ⁺¹" (at level 1, left associativity, format "t ⁺¹").
#[global] Reserved Notation "φ ↗ t " (at level 2, no associativity, format "φ ↗ t").

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
  where "φ ↗ t" := (WFT_ht φ t).

  Definition ω₁ : WFT := node (λ _, leaf).

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

  (** We give the semantics of a WFT in terms of Wim Veldman stumps, that it
      sets of finite sequences of X representing the finite branches of a WFT *)
  Fixpoint stump ω : list X → Prop :=
    match ω with 
    | leaf   => λ _, False
    | node ρ => λ l, l = [] ∨ ∃ x l', l = l'++[x] ∧ stump (ρ x) l'
    end.

  Fixpoint pfx_rev φ n :=
    match n with
    | 0   => []
    | S n => φ n :: pfx_rev φ n
    end.

  Fact pfx_rev_plus φ n m : pfx_rev φ (n+m) = pfx_rev (λ i, φ (m+i)) n ++ pfx_rev φ m.
  Proof. induction n; simpl; do 2 f_equal; auto; lia. Qed.

  Fact pfx_rev_S φ n : pfx_rev φ (S n) = pfx_rev ↓φ n ++ [φ 0].
  Proof.
    replace (S n) with (n+1) by lia.
    now rewrite pfx_rev_plus.
  Qed.

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

End WFT_tools.

Arguments leaf {X}.
Arguments node {X} _.


