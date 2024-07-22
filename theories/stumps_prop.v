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

  Local Remark good_vs_good_pairs R φ n : good R ⟨φ|n⟩ ↔ ∃ i j, i < j < n ∧ R (φ i) (φ j).
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

  Fact bar_secures_bound P l ω φ : bar_secures P l ω → P (⟨φ|φ↗ω⟩ ++ l).
  Proof.
    induction ω as [ | ρ IH ] in l, φ |- *; intros HP; auto.
    simpl WFT_ht; rewrite pfx_rev_S, app_ass.
    apply IH, HP.
  Qed.

  Fact bar_secures_nil_bound P ω φ : bar_secures P [] ω → P ⟨φ|φ↗ω⟩.
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

  Lemma af_secures_good_bound R ω φ : af_secures R ω → good R ⟨φ|φ↗ω⁺¹⁺¹⟩.
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
  Theorem WFT_bar_secures P l ω : (∀φ, P (⟨φ|φ↗ω⁺¹⟩ ++ l)) → bar_secures P l ω⁺¹.
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

  Lemma good_af_secures R ω : (∀φ, good R ⟨φ|φ↗ω⟩) → af_secures R ω⁺¹.
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

    (** In Wim Veldman's p222 §3.7, the statement of Brouwer's thesis

        "Let P be a subset of the set of finite sequences of natural numbers.
         If for every infinite sequence φ of natural numbers, there exists n 
         such that <φ₀;...;φₙ₋₁> belongs to P, then there exists a stump σ 
         such that for every infinite sequence φ of natural numbers there 
         exists n such that <φ₀;...;φₙ₋₁> belongs to σ and P." *)

    (* Here we rewrite the statement viewing lists as finite sequences
       in reverse, hence the prefix sequence is the list [φₙ₋₁;...;φ₀]
       also denoted ⟨φ|n⟩. Moreover, a stump σ is computed from a ω : WFT X
       as σ := stump ω. *)

    Hypothesis BT : ∀P,    (∀φ, ∃n, P ⟨φ|n⟩)
                      → ∃ω, ∀φ, ∃n, ((stump ω) ∩₁ P) ⟨φ|n⟩.

    (** Assuming Brouwer's thesis and a monotonic predicate,
        one can compute a WFT for which ⟨φ|φ↗ω⟩ gives a prefix
        of φ satisfying P for any φ : nat → X *)

    Lemma Brouwer_thesis_monotonic P :
               (∀ x l, P l → P (x::l))
             → (∀φ, ∃n, P ⟨φ|n⟩)
             → ∃ω, ∀φ, P ⟨φ|φ↗ω⟩.
    Proof.
      intros Pmono HP.
      assert (Pmono' : ∀ l r, P r → P (l++r)) 
        by (induction l; simpl; eauto).
      destruct (BT P) as (ω & Hω); auto.
      exists ω; intros phi.
      destruct (Hω phi) as (h & H1%stump_ht & H2).
      replace (WFT_ht phi ω) with ((WFT_ht phi ω-h)+h) by lia.
      rewrite pfx_rev_plus.
      now apply Pmono'.
    Qed.

    (** Since P := good R is a monotonic predicate, we
        instanciate Brouwer_thesis_monotonic *)

    Theorem Brouwer_afₛ R : afₛ R → ∃ω, af_secures R ω.
    Proof.
      intros HR.
      destruct Brouwer_thesis_monotonic with (P := good R) as (ω & Hω).
      + now constructor 2.
      + intros phi.
        destruct (HR phi) as (i & j & []).
        exists (S j); apply good_pfx_rev.
        exists i, j; split; auto; lia.
      + exists (WFT_lift ω); now apply good_af_secures.
    Qed.

    Theorem Brouwers_Thesis_equivalences R : 
          (afₛ R → ∃ω, af_secures R ω)
        ∧ ((∃ω, af_secures R ω) → ∃ω, afₛ_secures R ω)
        ∧ ((∃ω, afₛ_secures R ω) → afₛ R).
    Proof.
      repeat split.
      + apply Brouwer_afₛ.
      + apply afₛ_secures_iff_af_secures.
      + intros (ω & Hω) phi.
        destruct (Hω phi) as (i & j & [] & ?); eauto.
    Qed.

  End using_Brouwer_thesis.

  Section using_Fun_Choice.

    Hypothesis FunChoice : ∀(F : X → WFT X → Prop), (∀x, ∃y, F x y) → ∃f, ∀x, F x (f x).

    Lemma af_af_secures R : af R → ∃ω, af_secures R ω.
    Proof.
      induction 1 as [ R HR | R _ (f & Hf)%FunChoice ].
      + now exists leaf.
      + exists (node f); assumption.
    Qed.

    Theorem FunChoice_equivalences R :
             (af R → ∃ω, af_secures R ω)
           ∧ ((∃ω, af_secures R ω) → ∃ω, afₛ_secures R ω)
           ∧ ((∃ω, afₛ_secures R ω) → af R).
    Proof.
      rewrite afₛ_secures_iff_af_secures.
      repeat split; auto.
      + apply af_af_secures.
      + now intros (? & ?%af_secures_af).
    Qed.

    Lemma bar_bar_secures P l : bar P l → ∃ω, bar_secures P l ω.
    Proof.
      induction 1 as [ | l _ (f & Hf)%FunChoice ].
      + now exists leaf.
      + exists (node f); assumption.
    Qed.

    Theorem bar_brouwer P l : bar P l → ∃ω, ∀φ, P (⟨φ|φ↗ω⟩ ++ l).
    Proof.
      intros (ω & Hω)%bar_bar_secures.
      exists ω; intro; now apply bar_secures_bound.
    Qed.

  End using_Fun_Choice.

End af_secure.

