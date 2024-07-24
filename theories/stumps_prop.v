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

  Implicit Types (R : rel₂ X) (φ : nat → X) (ω : WFT X) (l : list X).

 (** The existence of a good pair below n can be characterized
      by the inductive predicate "good R" applied to the prefix
      ⟨φ|n⟩ := [φₙ₋₁;...;φ₀] of the infinite sequence φ.

        good R [φₙ₋₁;...;φ₀] ↔ ∃ i < j < n, R φᵢ φⱼ *)

  Local Remark good_vs_good_pairs R φ n : good R ⟨φ|n⟩ ↔ ∃ i j, i < j < n ∧ R (φ i) (φ j).
  Proof. apply good_pfx_rev. Qed.

  Print af.

  Definition afₛ R := ∀φ, ∃ i j, i < j ∧ R (φ i) (φ j).

  (* af is constructivelly stronger that afₛ. One can find an intuitive 
     explanation of this fact by Thierry Coquand in 

       https://www.cairn-int.info/journal-revue-internationale-de-philosophie-2004-4-page-483.htm

     The issue with the unability to prove afₛ R → af R comes from the universal 
     quantification over infinite sequences in the type φ : nat → X, which constructivelly
     does not to cover sequences of which the enumeration is not given by a law (think 
     of lambda terms), whereas the inductive characterization covers any sequence. *)
  Theorem af_afₛ R : af R → afₛ R.
  Proof.
    induction 1 as [ R HR | R _ IHR ]; intros phi.
    + exists 0, 1; auto.
    + destruct (IHR (phi 0) ↓phi) as (i & j & ? & []).
      * exists (S i), (S j); split; auto; lia.
      * exists 0, (S i); split; auto; lia.
  Qed.

  (** Using a WFT as a mesure of the almost fullness of binary relation *)

  (* Following the inductive structure of the af predicate *)
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

  (* Using infinite sequences *)
  Definition afₛ_secures R ω := ∀φ, ∃ i j, i < j < φ↗ω ∧ R (φ i) (φ j).

  Fact afs_secures_iff_good R ω : afₛ_secures R ω ↔ ∀φ, good R ⟨φ|φ↗ω⟩.
  Proof. split; intros ? ?; now apply good_pfx_rev. Qed.

  Fact afₛ_secures_afₛ R ω : afₛ_secures R ω → afₛ R.
  Proof.
    intros H phi.
    destruct (H phi) as (i & j & [] & ?).
    exists i, j; auto.
  Qed.

  (* We need to generalize the following way to get af_secures → afₛ_secures below *)
  Lemma af_secures_good R ω l φ : af_secures R⇈l ω → good R (⟨φ|φ↗ω⁺¹⁺¹⟩ ++ l).
  Proof.
    induction ω as [ | ρ IH ] in l, φ |- *; intros H.
    + simpl.
      specialize (H (φ 0) (φ 1)).
      apply rel_lift_rel_iff_good in H
        as [ | [ (z & []) | ] ].
      * repeat constructor; auto.
      * now constructor 2; constructor 1 with z.
      * constructor 1 with (φ 0); simpl; auto.
    + simpl WFT_ht; rewrite pfx_rev_S, app_ass.
      apply IH with (l := _::_), H.
  Qed.

  (* Notice that ω : WFT X is modified in the transfert *)
  Corollary af_secures_afₛ_secures R ω : af_secures R ω → afₛ_secures R ω⁺¹⁺¹.
  Proof. 
    intros ? ?.
    apply good_pfx_rev.
    rewrite app_nil_end.
    now apply af_secures_good.
  Qed.

  (* We need to generalize the following way to get afₛ_secures → af_secures below *)
  Lemma good_af_secures R ω l : (∀φ, good R (⟨φ|φ↗ω⟩ ++ l)) → af_secures R⇈l ω⁺¹.
  Proof.
    induction ω as [ | ρ IH ] in l |- *; intros H.
    + simpl in H |- *. 
      left; apply rel_lift_rel_iff_good; left; auto.
    + intros a.
      apply IH with (l := _::_).
      intros phi.
      specialize (H (a⋅phi)).
      simpl WFT_ht in H.
      now rewrite pfx_rev_S, app_ass in H.
  Qed.

  (* Notice that ω : WFT X is modified in the transfert *)
  Corollary afₛ_secures_af_secures R ω : afₛ_secures R ω → af_secures R ω⁺¹.
  Proof.
    intros H; apply good_af_secures with (l := []).
    intro; rewrite <- app_nil_end; apply good_pfx_rev, H.
  Qed.

  Theorem afₛ_secures_iff_af_secures R : (∃ω, afₛ_secures R ω) ↔ (∃ω, af_secures R ω).
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
         exists n such that <φ₀;...;φₙ₋₁> belongs to σ and P." 

        This definition is incomplete w/o giving the definition of stumps:
        these are sets of finite sequences of natural numbers generated by
        the two inductive rules:
                                         ρ : nat → stump nat
            ----------------   ------------------------------------------
             {} : stump nat     { <> } ∪ { <x>*σ | σ ∈ ρ x } : stump nat

     *)

    (* Here we rewrite the statement viewing lists as reversed finite sequences
       hence the prefix sequence is the list [φₙ₋₁;...;φ₀] also denoted ⟨φ|n⟩.
       Moreover, a stump σ is computed from ω : WFT X as σ := stump ω. *)

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

    (* Since P := good R is a monotonic predicate, we
       instanciate Brouwer_thesis_monotonic *)
    Theorem Brouwer_afₛ R : afₛ R → ∃ω, afₛ_secures R ω.
    Proof.
      intros HR.
      destruct Brouwer_thesis_monotonic with (P := good R) as (ω & Hω).
      + now constructor 2.
      + intros phi.
        destruct (HR phi) as (i & j & []).
        exists (S j); apply good_pfx_rev.
        exists i, j; split; auto; lia.
      + exists ω; intro; apply good_pfx_rev, Hω.
    Qed.

    (** Under Brouwer's thesis, the following statements are equivalent:

          1. ∃ω, afₛ_secures R ω
          2. ∃ω, af_secures R ω
          3. af R
          4. afₛ R

        Notice that only the implication 1 -> 2 -> 3 -> 4
        can be established w/o using any axiom. Only the
        last implication, 4 -> 1 ie 

                afₛ R → ∃ω, afₛ_secures R ω

        requires the use of Brouwer's thesis. *)

    Theorem Brouwers_Thesis_equivalences R :
          ((∃ω, afₛ_secures R ω) → ∃ω, af_secures R ω)
        ∧ ((∃ω, af_secures R ω) → af R)
        ∧ (af R → afₛ R)
        ∧ (afₛ R → ∃ω, afₛ_secures R ω).
    Proof.
      repeat split.
      + apply afₛ_secures_iff_af_secures.
      + now intros (? & ?%af_secures_af).
      + apply af_afₛ.
      + apply Brouwer_afₛ.
    Qed.

  End using_Brouwer_thesis.

  Section Stump.

    Inductive Stump : (list X → Prop) → Prop :=
      | Stump_empty : Stump (λ _, False)
      | Stump_node ρ : (∀x, Stump (ρ x)) → Stump (λ l, l = [] ∨ ∃ x l', l = l'++[x] ∧ ρ x l').

    Definition finitary Γ := ∃l, ∀x m, Γ (x::m) → x ∈ l → False.

    Definition afS_secures R Γ := ∀φ, ∃n, (Γ ∩₁ (good R)) ⟨φ|n⟩.

    Hypothesis BT' : ∀P,    (∀φ, ∃n, P ⟨φ|n⟩)
                      → ∃Γ, Stump Γ ∧ ∀φ, ∃n, (Γ ∩₁ P) ⟨φ|n⟩.

    Theorem Brouwer_afS R : afₛ R → ∃Γ, Stump Γ ∧ afS_secures R Γ.
    Proof.
      intros HR.
      destruct BT' with (P := good R) as (Γ & H1 & H2).
      + intros phi; destruct (HR phi) as (i & j & []).
        exists (S j); apply good_pfx_rev.
        exists i, j; split; auto; lia.
      + exists Γ; split; auto.
    Qed.

    Lemma good_af R ω l : (∀φ, good R (⟨φ|φ↗ω⟩ ++ l)) → af R⇈l.
    Proof.
      induction ω as [ | ρ IH ] in l |- *; intros H.
      + simpl in H |- *.
        constructor 1.
        intros x y.
        apply rel_lift_rel_iff_good; left; auto.
      + constructor 2; intros a.
        apply IH with (l := _::_) (x := a).
        intros phi.
        specialize (H (a⋅phi)).
        simpl WFT_ht in H.
        now rewrite pfx_rev_S, app_ass in H.
    Qed.

    Hypothesis forall_disj : ∀ P (Q : (nat → X) → Prop), (∀φ, P ∨ Q φ) →  P ∨ ∀φ, Q φ.

    (* One should be able to exclude the case good R l a priori below if
       one is to avoid using forall_disj ... *)

    Lemma good_stump_af R ω l : (∀φ, ∃n, stump ω ⟨φ|n⟩ ∧ good R (⟨φ|n⟩ ++ l)) → af R⇈l.
    Proof.
      induction ω as [ | ρ IH ] in l |- *; intros H.
      + constructor 1.
        intros x y.
        now destruct (H (fun _ => x)). 
      + assert (∀φ, good R l ∨ ∃ n, stump (node ρ) ⟨φ|S n⟩ ∧ good R (⟨φ|S n⟩ ++ l)) as [H' | H']%forall_disj.
        1: { intros phi.
             destruct (H phi) as (n & H1 & H2).
             destruct n as [ | n ]; auto.
             right.
             destruct H1 as [ | H1 ]; [ easy | ].
             exists n; split; auto.
             right; auto. }
        * constructor 1; intros; apply rel_lift_rel_iff_good; auto.
        * clear H.
          constructor 2; intros a.
          apply IH with (l := _::_) (x := a).
          intros phi.
          specialize (H' (a⋅phi)).
          destruct H' as (n' & H1 & H2).
          rewrite pfx_rev_S in H1, H2.
          rewrite app_ass in H2.
          exists n'; split; auto.
          destruct H1 as [ | (x & m & H1 & H3) ].
          1: now destruct n'.
          apply app_inj_tail_iff in H1 as (<- & <-); eauto.
    Qed.

    Lemma afS_af R Γ l : Stump Γ → (∀φ, ∃n, Γ ⟨φ|n⟩ ∧ good R (⟨φ|n⟩++l)) → af (R⇈l).
    Proof.
      induction 1 as [ | rho Hrho IHrho ] in R, l |- *; intros H.
      + constructor 1. 
        intros x y.
        now destruct (H (fun _ => x)).
      + assert (∀φ, good R l ∨ ∃ n, rho (φ 0) ⟨↓φ|n⟩ ∧ good R (⟨φ|S n⟩ ++ l)) as [H' | H']%forall_disj.
        1: { intros phi.
             destruct (H phi) as (n & H1 & H2).
             destruct n as [ | n ]; auto.
             right.
             destruct H1 as [ | H1 ]; [ easy | ].
             exists n; split; auto.
             destruct H1 as (x & m & H1 & H3).
             rewrite pfx_rev_S in H1.
             now apply app_inj_tail_iff in H1 as (<- & <-). }
        all: clear H.
        * constructor 1; intros; apply rel_lift_rel_iff_good; auto.
        * constructor 2; intros a.
          apply IHrho with (l := _::_) (x := a).
          intros phi.
          specialize (H' (a⋅phi)).
          destruct H' as (n & H1 & H2).
          rewrite pfx_rev_S, app_ass in H2.
          exists n; split; auto.
    Qed.

    Theorem afS_forall_disj R Γ : Stump Γ → afS_secures R Γ → af R.
    Proof.
      intros H1 H2; apply afS_af with (1 := H1) (l := []).
      intros phi.
      destruct (H2 phi) as (n & []).
      exists n; split; auto.
    Qed.

    Theorem af_iff_afS R : af R ↔ ∃Γ, Stump Γ ∧ afS_secures R Γ.
    Proof.
      split.
      + now intros ?%af_afₛ%Brouwer_afS.
      + intros (G & H1 & H2); revert H1 H2; apply afS_forall_disj.
    Qed.

  End Stump.

  Check af_iff_afS.

  Section using_Fun_Choice.

    Hypothesis FunChoice : ∀(F : X → WFT X → Prop), (∀x, ∃y, F x y) → ∃f, ∀x, F x (f x).

    Lemma af_af_secures R : af R → ∃ω, af_secures R ω.
    Proof.
      induction 1 as [ R HR | R _ (f & Hf)%FunChoice ].
      + now exists leaf.
      + exists (node f); assumption.
    Qed.

    (** Under Functional Choice, the following statements are equivalent:
        1. af R
        2. ∃ω, af_secures R ω
        4. ∃ω, afₛ_secures R ω  

        Notice that only the implication

               af R → ∃ω, af_secures R ω

        requires the use of Functional Choice.

        Also notice that using FunChoice instead of Brouwer's thesis, 
        afₛ R becomes a weaker statement, not included in the list. *)

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

  End using_Fun_Choice.

End af_secure.

