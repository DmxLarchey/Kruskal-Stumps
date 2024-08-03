(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

From Coq Require Import Arith Lia List Utf8.

From KruskalAfType
  Require Import base notations pfx_rev almost_full.

Require Import wft.

Set Implicit Arguments.

Import lift_notations ListNotations.

Section af_secure_Type.

  Variable (X : Type).

  Implicit Types (R : rel₂ X) (P : rel₁ (list X)) (φ : nat → X) (ω : WFT X) (l : list X).

  (** The existence of a good pair below n can be characterized
      by the inductive predicate "good R" applied to the prefix
      ⟨φ|n⟩ := [φₙ₋₁;...;φ₀] of the infinite sequence φ.

        good R [φₙ₋₁;...;φ₀] ↔ ∃ i < j < n, R φᵢ φⱼ *)

  Local Remark good_vs_good_pairs R φ n : good R ⟨φ|n⟩ ↔ ∃ i j, i < j < n ∧ R (φ i) (φ j).
  Proof. apply good_pfx_rev. Qed.

  (* Using a WFT as a mesure of the almost fullness of binary relation *)
  Fixpoint af_secures R t :=
    match t with
    | leaf   => ∀ x y, R x y
    | node ρ => ∀a, af_secures R↑a (ρ a)
    end.

  Fact af_secures_af R ω : af_secures R ω → af R.
  Proof. 
    induction ω in R |- *; simpl.
    + now constructor 1.
    + constructor 2; eauto.
  Qed.

  Definition afₛ R := ∀φ, { n | ∃ i j, i < j < n ∧ R (φ i) (φ j) }.

  Definition afₛ_secures R ω := ∀φ, ∃ i j, i < j < φ↗ω ∧ R (φ i) (φ j).

  Fact afₛ_secures_afₛ R ω : afₛ_secures R ω → afₛ R.
  Proof. intros H phi; exists (phi↗ω); apply H. Qed.

  (* We need to generalize the following way to get af_secures → afₛ_secures below *)
  Lemma af_secures_good R ω l φ : af_secures (R⇈l) ω → good R (⟨φ|φ↗ω⁺¹⁺¹⟩ ++ l).
  Proof.
    induction ω as [ | ρ IH ] in l, φ |- *; intros H.
    + simpl.
      specialize (H (φ 0) (φ 1)).
      apply rel_lift_rel_iff_good in H as [ | [ (z & []) | H ] ].
      * repeat constructor; auto.
      * now constructor 2; constructor 1 with z.
      * constructor 1 with (φ 0); simpl; auto.
    + simpl WFT_ht; rewrite pfx_rev_S, app_ass.
      apply IH with (l := _::_), H.
  Qed.

  Corollary af_secures_afₛ_secures R ω : af_secures R ω → afₛ_secures R ω⁺¹⁺¹.
  Proof. 
    intros ? ?.
    apply good_pfx_rev.
    rewrite app_nil_end.
    now apply af_secures_good.
  Qed.

  (* We need to generalize the following way to get afₛ_secures → af_secures below *)
  Lemma good_af_secures R ω l : (∀φ, good R (⟨φ|φ↗ω⟩ ++ l)) → af_secures (R⇈l) ω⁺¹.
  Proof.
    induction ω as [ | ρ IH ] in l |- *; intros H.
    + simpl in H; left; apply rel_lift_rel_iff_good; left; auto.
    + intros a.
      apply IH with (l := _::_).
      intros phi.
      specialize (H (a⋅phi)).
      simpl WFT_ht in H.
      now rewrite pfx_rev_S, app_ass in H.
  Qed.

  Corollary afₛ_secures_af_secures R ω : afₛ_secures R ω → af_secures R ω⁺¹.
  Proof.
    intros H; apply good_af_secures with (l := []).
    intro; rewrite <- app_nil_end; apply good_pfx_rev, H.
  Qed.

  Remark FunChoice_type (F : X → WFT X → Prop) : (∀u, {v | F u v}) → {f | ∀u, F u (f u)}.
  Proof. intros f; exists (fun u => proj1_sig (f u)); intro; apply (proj2_sig _). Qed.

  (* Using FunChoice_type, provable for Σ-types (Type-bounded existential quantifiers),
     we easily get af → af_secures for some WFT X, when Base := Type *)
  Lemma af_af_secures R : af R → { ω | af_secures R ω }.
  Proof.
    induction 1 as [ | ? _ (ρ & ?)%FunChoice_type ].
    + now exists leaf.
    + now exists (node ρ).
  Qed.

  (* Hence the equivalence between the inductive af predicate and the existence
     of a witness (AF complexity measure) for either af securing R or afₛ securing R *)
  Theorem af_secures_equivalences R : 
          ( af R                    → { ω | afₛ_secures R ω } )
        * ( { ω | afₛ_secures R ω } → { ω | af_secures R ω } )
        * ( { ω | af_secures R ω }  → af R ).
  Proof.
    repeat split.
    + intros (? & ?%af_secures_afₛ_secures)%af_af_secures; eauto.
    + intros (? & ?%afₛ_secures_af_secures); eauto.
    + now intros (? & ?%af_secures_af).
  Qed.

  Definition bar_secures P :=
    fix loop l ω :=
      match ω with
      | leaf   => P l
      | node ρ => ∀a, loop (a::l) (ρ a)
      end.

  Hint Constructors bar : core.

  Fact bar_secures_bar P l ω : bar_secures P l ω → bar P l.
  Proof. induction ω in l |- *; simpl; eauto. Qed.

  Fact bar_bar_secures P l : bar P l → { ω | bar_secures P l ω }.
  Proof.
    induction 1 as [ | ? _ (ρ & ?)%FunChoice_type ].
    + now exists leaf.
    + now exists (node ρ).
  Qed.

  Definition barₛ_secures P l ω := ∀φ, P (⟨φ|φ↗ω⟩++l).

  Fact bar_secures_barₛ_secures P l ω : bar_secures P l ω → barₛ_secures P l ω.
  Proof.
    induction ω as [ | ρ IH ] in l |- *; intros H phi.
    + now simpl in *.
    + simpl WFT_ht; rewrite pfx_rev_S, app_ass.
      apply IH with (l := _::_), H.
  Qed.

  Variables (P : rel₁ (list X)) (HP : ∀ x l, P l → P (x::l)).

  Fact barₛ_secures_bar_secures l ω : barₛ_secures P l ω → bar_secures P l ω⁺¹.
  Proof.
    induction ω as [ | ρ IH ] in l |- *; intros H; simpl.
    + intros a; apply HP, (H (λ _, a)).
    + intros a; apply IH.
      intros phi.
      specialize (H (a⋅phi)).
      simpl WFT_ht in H.
      now rewrite pfx_rev_S, app_ass in H.
  Qed.

End af_secure_Type.
