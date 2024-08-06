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

From KruskalAfProp
  Require Import base notations pfx_rev almost_full af_bar.

From KruskalHigmanProp
  Require Import tactics list_embed.

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

  Lemma good_stump_bar R ω l : (∀φ, ∃n, stump ω ⟨φ|n⟩ ∧ good R (⟨φ|n⟩++l)) → bar (good R) l.
  Proof.
    induction ω as [ | ρ IH ] in l |- *; intros H.
    + constructor 2; constructor 1.
      now destruct (H (λ _, x)).
    + constructor 2; intros a.
      (* We use the emptyness of stump (ρ a) to discriminate between n = 0 or not
         in the ∃n of hypothesis H for any φ starting such that φ 0 = a *)
      destruct (stump_empty_dec (ρ a)) as [ Ha | Ha ].
      * (* stump (ρ a) [] holds hence we can do something with the case n = 0 *) 
        apply IH with a.
        intros phi.
        destruct (H (a⋅phi)) as ([ | n] & H1 & H2).
        - exists 0; auto.
        - destruct H1 as [ | (z & m & H1 & H3) ]; [ easy | ].
          rewrite pfx_rev_S in H1, H2.
          rewrite app_ass in H2.
          apply app_inj_tail_iff in H1 as (<- & <-).
          eauto.
      * (* Since stump (ρ a) = ⊥₁ then we use H on the constant function λ _, a *)
        destruct (H (λ _, a)) as ([ | n ] & H1 & H2).
        - constructor 1; auto.
        - rewrite pfx_rev_S in H1.
          destruct H1 as [ H1 | (z & u & H1 & H3) ].
          1: now destruct n.
          apply app_inj_tail_iff in H1 as (<- & <-).
          now rewrite Ha in H3.
  Qed.

  (* And we get the theorem that we want !!! *)
  Theorem good_stump_af R ω : (∀φ, ∃n, stump ω ⟨φ|n⟩ ∧ good R ⟨φ|n⟩) → af R.
  Proof.
    intros H.
    apply af_iff_bar_good_nil, good_stump_bar with ω.
    intros phi.
    destruct (H phi) as (n & ?).
    exists n.
    now rewrite app_nil_r.
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

  Definition extends l m :=
    match l with
    | []   => False
    | _::l => l = m
    end.

  Section bar_dec.

    Variables (P : list X → Prop) (Pdec : ∀l, P l ∨ ¬ P l). 

    Fact bar_Acc l : bar P l → Acc (λ l m, extends l m ∧ ¬ P m) l.
    Proof.
      induction 1 as [ l Hl | l Hl IHl ].
      + constructor 1; intros ? []; tauto.
      + constructor 1; intros [ | x m ] [ H1 H2 ]; [ easy | ].
        simpl in H1; subst m.
        apply IHl.
    Qed.

    Fact Acc_bar l : Acc (λ l m, extends l m ∧ ¬ P m) l → bar P l.
    Proof.
      induction 1 as [ l Hl IHl ].
      destruct (Pdec l) as [ H | H ].
      + now constructor 1.
      + constructor 2; intros x.
        apply IHl; simpl; auto.
    Qed.

  End bar_dec.

  Section using_Brouwer_thesis'.

    Implicit Type Γ : list X → Prop.

    Notation "Γ \ x" := (λ l, Γ (l++[x])) (at level 1, left associativity, format "Γ \ x").

    Remark Stump_equivalence Γ : Γ [] → ∀l, Γ l ↔ l = [] ∨ ∃ x m, l = m++[x] ∧ Γ\x m.
    Proof.
      intros H l.
      destruct (list_snoc_inv l) as [ -> | (m & x & ->) ].
      + tauto.
      + split; eauto.
        intros [ | (? & ? & (<- & <-)%app_inj_tail_iff & ?) ]; auto.
        now destruct m.
    Qed.

    (** Stump is the inductive predicate over Γ : list X → Prop defined
        by the two rules:

            Γ ⊆₁ ⊥₁         Γ []   ∀x, Stump Γ\x
           ---------       ----------------------
            Stump Γ             Stump Γ

        meaning 

        1. any empty predicate is a Stump
        2. if Γ [] holds and Γ\x is a Stump for any x then Γ is a Stump *)

    Inductive Stump Γ : Prop :=
      | Stump_empty : Γ ⊆₁ ⊥₁ → Stump Γ
      | Stump_node  : Γ [] → (∀x, Stump Γ\x) → Stump Γ.

    Hint Constructors Stump : core.

    Fact Stump_dec Γ : Stump Γ → ∀ l, Γ l ∨ ¬ Γ l.
    Proof.
      induction 1 as [ Γ H1 | Γ H1 H2 IH2 ].
      + right; exact (H1 _).
      + intros l.
        destruct (list_snoc_inv l) as [ -> | (m & x & ->) ]; auto.
    Qed.

    Fact Stump_empty_dec Γ : Stump Γ → Γ [] ∨ Γ ⊆₁ ⊥₁.
    Proof. induction 1; eauto. Qed.

    Fact Stump_inv Γ : Stump Γ → ∀x, Stump Γ\x.
    Proof.
      induction 1 as [ Γ H1 | ]; auto; intros x.
      constructor 1; intro; apply H1.
    Qed.

    Lemma Stump_iff Γ : Stump Γ ↔ Γ ⊆₁ ⊥₁ ∨ Γ [] ∧ ∀x, Stump Γ\x.
    Proof.
      split.
      + induction 1; eauto.
      + intros [ | [] ]; [ constructor 1 | constructor 2 ]; auto.
    Qed.

    Fact Stump_ext Γ Γ' : (∀l, Γ l ↔ Γ' l) → Stump Γ → Stump Γ'.
    Proof.
      intros H; induction 1 as [ Γ H1 | Γ H1 H2 IH2 ] in Γ', H |- *.
      + constructor 1; intros l; rewrite <- H; eauto.
      + constructor 2.
        * now apply H.
        * intros x; apply IH2 with x.
          intro; apply H.
    Qed.

    Definition Stump_lift Γ l := l = [] ∨ ∃ x l', l = l'++[x] ∧ Γ l'.

    Fact Stump_lift_correct Γ : Stump Γ → Stump (Stump_lift Γ).
    Proof.
      intros H.
      constructor 2.
      + now left.
      + intros x.
        revert H; apply Stump_ext.
        intros l; split.
        * right; now exists x, l.
        * intros [ H | (y & m & (<- & <-)%app_inj_tail_iff & H2) ]; auto.
          now destruct l.
    Qed.

    Fact stump_is_Stump ω : Stump (stump ω).
    Proof. 
      induction ω; simpl; eauto.
      constructor 2; eauto.
      intros x; apply Stump_ext with (2 := H x).
      intros l; split.
      + right; eauto.
      + intros [ | (y & m & (<- & <-)%app_inj_tail_iff & ?) ]; auto.
        now destruct l.
   Qed.

    Fact Stump_cons_inv Γ x r : Stump Γ → Γ (x::r) → Γ r.
    Proof.
      induction 1 as [ Γ H1 | Γ H1 H2 IH2 ] in x, r |- *; simpl; auto.
      + now intros ?%H1.
      + destruct (list_snoc_inv r) as [ -> | (? & ? & ->) ]; eauto.
    Qed.

    Fact Stump_app_inv Γ l r : Stump Γ → Γ (l++r) → Γ r.
    Proof.
      intros H; induction l; simpl; auto.
      intros ?%(Stump_cons_inv _ _ H); eauto.
    Qed.

    Definition pred_list_lift P m := ∃l, list_embed eq l m ∧ P l.

    Notation "↟ P" := (pred_list_lift P) (at level 0, right associativity, format "↟ P").

    Fact pred_list_lift_monotonic P x l : ↟P l → ↟P (x::l).
    Proof.
      intros (m & []); exists m; split; auto.
      now constructor 3.
    Qed.

    Notation "φ 'meets' P" := (∃n, ↟P ⟨φ|n⟩) (at level 50).

    Hypothesis BT' : ∀P, (∀φ, ∃n, P ⟨φ|n⟩) → ∃Γ, Stump Γ ∧ ∀φ, ∃n, Γ∩₁P ⟨φ|n⟩.

    Fact pred_lift_good R l : good R l ↔ ↟(good R) l.
    Proof.
      split.
      + exists l; split; auto; apply Forall2_embed.
        clear H; induction l; eauto.
      + intros (m & H1 & H2); revert H2 H1.
        induction 1 as [ x y m H1 | x m H1 IH1 ] in l |- *.
        * intros (m1 & ? & m2 & -> & <- & H2)%list_embed_inv_left.
          destruct list_embed_in_left_inv
            with (1 := H2) (2 := H1)
            as (? & ? & <-); eauto.
        * intros (m1 & ? & m2 & -> & <- & H2)%list_embed_inv_left; eauto.
    Qed.

    Definition afS_secures R Γ := ∀φ, ∃n, Γ∩₁(good R) ⟨φ|n⟩.

    Theorem Brouwer'_afS R : afₛ R → Stump ⧫ afS_secures R.
    Proof.
      intros HR.
      destruct BT' with (P := good R) as (Γ & H1 & H2).
      + intros phi; destruct (HR phi) as (i & j & []).
        exists (S j); apply good_pfx_rev.
        exists i, j; split; auto; lia.
      + exists Γ; split; auto.
    Qed.

    (** This lemma is difficult:
         1) you need to get it as the right generalization for Stump Γ → afS_secures R Γ → af R
         2) you need to realize that you must discriminate on Γ [a], which is possible
            because Stumps are decidable subsets *)

    Lemma Stump_good_af R Γ l : Stump Γ → (∀φ, ∃n, Γ ⟨φ|n⟩ ∧ good R (⟨φ|n⟩++l)) → af (R⇈l).
    Proof.
      induction 1 as [ Γ H1 | Γ H1 H2 IH2 ] in l |- *; intros H.
      + constructor 1. 
        intros x ?.
        now destruct (H (λ _, x)) as (_ & ?%H1 & _).
      + constructor 2; intros a.
        (* We use the emptyness of λ l, Γ (l++[a]) to discriminate between n = 0 or not
           in the ∃n of hypothesis H for any φ starting such that φ 0 = a *)
        destruct Stump_empty_dec with (1 := H2 a) as [ Ha | Ha ].
        * (* Γ [a] holds hence we can do something with the case n = 0 *) 
          apply IH2 with (l := _::_) (x := a).
          intros phi.
          destruct (H (a⋅phi)) as ([ | n] & H3 & H4).
          - exists 0; auto.
          - rewrite pfx_rev_S in H3, H4.
            rewrite app_ass in H4.
            eauto.
        * (* Since Γ (_++[a]) → False, we use H on the constant function λ _, a *)
          destruct (H (λ _, a)) as ([ | n ] & H3 & H4).
          - constructor 1; left; apply rel_lift_rel_iff_good; auto.
          - rewrite pfx_rev_S in H3.
            now apply Ha in H3.
    Qed.

    Theorem afStump_af R : Stump ⧫ afS_secures R → af R.
    Proof.
      intros (G & H1 & H2); apply Stump_good_af with (1 := H1) (l := []).
      intros phi.
      destruct (H2 phi) as (n & []); eauto.
    Qed.

    Theorem Brouwers_alt_Thesis_equivalences R :
          (af R → afₛ R)
        ∧ (afₛ R → Stump ⧫ afS_secures R)
        ∧ (Stump ⧫ afS_secures R → af R).
    Proof.
      repeat split.
      + apply af_afₛ.
      + apply Brouwer'_afS.
      + apply afStump_af.
    Qed.

  End using_Brouwer_thesis'.

  Section bar_secures.

    Variables (P : rel₁ (list X)) (HP : ∀ x l, P l → P (x::l)).

    Local Fact Pmonotonic l r : P r → P (l++r).
    Proof. induction l; eauto. Qed.

    Definition barS_secures l Γ := ∀φ, ∃n, Γ ⟨φ|n⟩ ∧ P (⟨φ|n⟩++l).

    Lemma Stump_barS_secures_bar l : Stump ⧫ barS_secures l → bar P l.
    Proof.
      intros (Γ & H1 & H2); revert H1 H2.
      induction 1 as [ Γ H1 | Γ H1 H2 IH2 ] in l |- *; intros H.
      + constructor 2; intros a.
        now destruct (H (λ _, a)) as (_ & ?%H1 & _).
      + constructor 2; intros a.
        (* We use the emptyness of λ l, Γ (l++[a]) to discriminate between n = 0 or not
           in the ∃n of hypothesis H for any φ starting such that φ 0 = a *)
        destruct Stump_empty_dec with (1 := H2 a) as [ Ha | Ha ].
        * (* Γ [a] holds hence we can do something with the case n = 0 *) 
          apply IH2 with (l := _::_) (x := a).
          intros phi.
          destruct (H (a⋅phi)) as ([ | n] & H3 & H4).
          - exists 0; simpl; auto.
          - rewrite pfx_rev_S in H3, H4.
            rewrite app_ass in H4.
            eauto.
        * (* Since Γ (_++[a]) → False, we use H on the constant function λ _, a *)
          destruct (H (λ _, a)) as ([ | n ] & H3 & H4).
          - constructor 1; auto.
          - rewrite pfx_rev_S in H3.
            now apply Ha in H3.
    Qed.

    Lemma Stump_monotonic_bar Γ : Stump Γ → (∀φ, ∃n, Γ∩₁P ⟨φ|n⟩) → bar P [].
    Proof.
      intros H1 H2.
      apply Stump_barS_secures_bar.
      exists Γ; split; auto.
      intros phi.
      destruct (H2 phi) as (n & []).
      exists n; split; auto.
      now rewrite <- app_nil_end.
    Qed.

    Hypothesis (Pdec :  ∀l, P l + ¬ P l)
               (Pwdec : ∀l, P l ∨ ¬ P l).

    Definition bar_secures :=
    fix loop l ω :=
      match ω with
      | leaf   => P l
      | node ρ => ∀a, loop (a::l) (ρ a)
      end.

    Fact bar_dec_bar_secures l : bar P l → { ω | bar_secures l ω }.
    Proof.
      intros H%bar_Acc; revert l H.
      refine (fix loop l d { struct d } := _).
      destruct (Pdec l) as [ Hl | Hl ].
      + now exists leaf.
      + exists (node (fun a => proj1_sig (loop (a::l) (@Acc_inv _ _ _ d (a::l) (conj eq_refl Hl))))).
        simpl; intros a.
        apply (proj2_sig _).
    Qed.

    Definition barₛ_secures l ω := ∀φ, P (⟨φ|φ↗ω⟩++l).

    Fact bar_secures_barₛ_secures l ω : bar_secures l ω → barₛ_secures l ω.
    Proof.
      induction ω as [ | ρ IH ] in l |- *; intros H phi.
      + now simpl in *.
      + simpl WFT_ht; rewrite pfx_rev_S, app_ass.
        apply IH with (l := _::_), H.
    Qed.

    Fact barₛ_secures_barS_secures l ω : barₛ_secures l ω → barS_secures l (stump ω⁺¹).
    Proof.
      intros H phi.
      exists phi↗ω.
      split; auto.
      apply stump_pfx_rev.
    Qed.

    Definition suffix l s := exists m, l = m++s.

    Fact bar_app l r : bar P r → bar P (l++r).
    Proof.
      induction l; auto; simpl.
      intro; apply bar_inv_mono; auto.
    Qed.

    (* We need to capture stump ω⁺¹ where
        ω is the one computed by 
         bar_bar_secures P l : bar P l → { ω | bar_secures P l ω } 
         ie the inductive structure of the bar P l predicate *)

    Definition mks l m := ~ P (m++l).

    Fact bar_mks_Stump l : bar P l → Stump (mks l).
    Proof.
      induction 1 as [ | l Hl IHl ].
      + constructor 1.
        intros ? []; now apply Pmonotonic.
      + destruct (Pwdec l).
        * constructor 1.
          intros ? []; now apply Pmonotonic.
        * constructor 2.
          - assumption.
          - intros a.
            generalize (IHl a).
            apply Stump_ext.
            intros m; unfold mks.
            rewrite app_ass; simpl; tauto.
    Qed.

    Fact bar_rec_wdec l φ : bar P l → P l ∨ ∃n, ¬ P (⟨φ|n⟩++l) ∧ P (⟨φ|S n⟩++l).
    Proof.
      induction 1 as [ l Hl | l _ IHl ] in φ |- *.
      + now left.
      + destruct (Pwdec l) as [ Hl | Hl ].
        * now left.
        * right.
          destruct (IHl (φ 0) (↓φ))
            as [ H | (n & H1 & H2) ].
          - exists 0; split; auto.
          - exists (S n); do 2 rewrite pfx_rev_S.
            rewrite !app_ass; auto.
    Qed.

    Lemma bar_barS_secures l : bar P l → Stump ⧫ barS_secures l.
    Proof.
      exists (Stump_lift (mks l)); split.
      + now apply Stump_lift_correct, bar_mks_Stump.
      + intros phi. 
        destruct bar_rec_wdec with (φ := phi) (1 := H)
          as [ Hl | (n & H1 & H2) ].
        * exists 0; split; auto; left; auto.
        * exists (S n); split; auto.
          rewrite pfx_rev_S. 
          right.
          exists (phi 0), ⟨↓phi|n⟩; split; auto.
          red.
    Admitted.
           
          red.
intros phi.
        Search bar.


    Fact mks_nil r : mks r [].
    Admitted.

    Fact mks_equiv x r l : mks (x::r) l <-> mks r (l++[x]).
    Admitted.

    Fact bar_mks_Stump r : bar P r → Stump (mks r).
    Proof.
      induction 1 as [ r Hr | r Hr IHr ].
      + constructor 1.
        intros m [ [] | [H1 H2] ].
        * now apply Pmonotonic.
        * destruct m as [ | x m ]; auto.
          now apply H2, Pmonotonic.
      + constructor 2.
        * apply mks_nil.
        * intros x.
          generalize (IHr x).
          apply Stump_ext.
          intros; apply mks_equiv.
    Admitted.

    Definition sprefix r m := exists l, l <> [] /\ m = l++r.

    Definition mkStmp l := λ m :=
      ~ P (m++l) \/ P (m++l) /\ forall p, sprefix p m -> ~ P (p++l).

    Fact bar_mkStump P l : bar P l -> Stump (mkStmp P l).
    Proof.
      induction 1 as [ l Hl | l Hl IHl ].
      + constructor 2.
        * right; split; auto.
          now intros p ([] & H1 & H2).
        * intros a; constructor 1.
          intros m [ H | [ H1 H2 ] ].
          - (*monotonicity *) admit.
          - apply (H2 []); auto.
            exists (m++[a]); split.
            ++ now destruct m.
            ++ now rewrite app_ass.
      + constructor 2.
        * (* decide P l \/ ~ P l *) admit.
        * intros a.
          specialize (IHl a).
          revert IHl.
          apply Stump_ext.
          intros m; split; unfold mkStmp;
            intros [ H | (H1 & H2) ].
          - left; now rewrite app_ass.
          - right; rewrite app_ass; split; auto.
            intros p (r & H3 & H4).
left. split.

      ~ P l \/ P l /\ match l with [] => True | _::l => ~ P l end.

    Fact bar_mkStmp P l : bar P 

    (* This one seems difficult to get ... *)

    Definition make_Stump R l :=
      match l with
      | []   => True
      | x::l => ~ good R l
      end.

    (* make_Stump (True) l <-> length l <= 2 

       what could be a positive criteria ? *)

    Lemma af_make_Stump R : af R -> (forall x y, R x y \/ ~ R x y) -> Stump (make_Stump R) /\ afS_secures R (make_Stump R).
    Proof.
      induction 1 as [ R HR | R HR IHR ]; intros Rdec; split.
      + constructor 2; simpl; auto.
        intros x; constructor 2; simpl.
        1: now intros ?%good_nil_inv.
        intros y; constructor 2; simpl.
        1: now intros ?%good_sg_inv.
        intros z; simpl.
        constructor 1.
        intros [ | a l ]; simpl; intros H; apply H.
        * constructor 1 with x; simpl; auto.
        * rewrite app_ass; apply good_app_left.
          constructor 1 with x; simpl; auto.
      + intros phi; exists 2; split; simpl.
        * now intros ?%good_sg_inv.
        * constructor 1 with (phi 0); simpl; auto.
      + constructor 2; simpl; auto.
        intros x.
        destruct (IHR x) as (H1 & H2).
        * admit.
        * revert H1.
          apply Stump_ext.
          intros [ | z l ]; simpl.
          Search good app.
          - rewrite good_nil_inv; tauto.
          - rewrite good_rel_lift_rev_iff.
            admit.
      + intros phi.
    Admitted.

    Lemma af_afStump R : af R → ∃Γ, Stump Γ ∧ afS_secures R Γ.
    Proof.
      induction 1 as [ R HR | R HR IHR ].
      + exists (stump leaf⁺¹⁺¹⁺¹); split.
        * apply stump_is_Stump.
        * intros phi; exists 2; split.
          - right; exists (phi 0), [phi 1]; split; auto.
            right; exists (phi 1), []; split; auto.
            now left.
          - constructor 1 with (phi 0); simpl; eauto.
      + exists (fun l => l = [] \/ exists x m, l = m++[x] /\ exists Γ, Stump Γ /\ afS_secures R↑x Γ /\ Γ l); split.
        * constructor 2; auto.
          intros x.
          destruct (IHR x) as (G & H1 & H2).
          apply Stump_ext with (Γ := λ l, ∃ Γ, Stump Γ ∧ afS_secures R↑x Γ ∧ Γ (l ++ [x])).
          - intros l; split.
            ++ right; exists x, l; auto.
            ++ intros [ C | (y & m & (<- & <-)%app_inj_tail & H) ]; auto.
               now destruct l.
          - admit.
        * admit.
    Admitted. 

  Check Brouwers_alt_Thesis_equivalences.

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

