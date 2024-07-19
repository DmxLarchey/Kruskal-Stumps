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

From KruskalHigmanType
  Require Import tactics.

Set Implicit Arguments.

Import lift_notations ListNotations.

Notation "↓ φ" := (λ n, φ (S n)) (at level 0, right associativity, format "↓ φ").
Notation "a ⋅ φ" := (λ n, match n with 0 => a | S n => φ n end) (at level 0, right associativity, format "a ⋅ φ").

Section WFT.

  Variables (X : Type).

 Implicit Type (R : rel₂ X) (P : rel₁ (list X)).

  Inductive WFT := 
    | leaf : WFT 
    | node : (X → WFT) → WFT.

  Fixpoint af_secures R t :=
    match t with
    | leaf   => ∀ x y, R x y
    | node ρ => ∀a, af_secures R↑a (ρ a)
    end.

  Fact af_secures_af R : { t | af_secures R t } → af R.
  Proof.
    intros (t & Ht). 
    induction t in R, Ht |- *; simpl.
    + now constructor 1.
    + constructor 2; eauto.
  Qed.

  Fact af_af_secured R : af R → { t | af_secures R t }.
  Proof.
    induction 1 as [ R HR | R HR IHR ].
    + now exists leaf.
    + exists (node (fun x => proj1_sig (IHR x))).
      simpl; intros a.
      apply (proj2_sig (IHR _)).
  Qed.

  Definition bar_secures P :=
    fix loop l t :=
      match t with
      | leaf   => P l
      | node ρ => ∀a, loop (a::l) (ρ a)
      end.

  Fact bar_secures_bar P l : { t | bar_secures P l t } → bar P l.
  Proof.
    intros (t & Ht).
    induction t in l, Ht |- *; simpl.
    + now constructor 1.
    + constructor 2; eauto.
  Qed.

  Fact bar_bar_secures P l : bar P l → { t | bar_secures P l t }.
  Proof.
    induction 1 as [ | l _ IHl ].
    + now exists leaf.
    + exists (node (fun x => proj1_sig (IHl x))); simpl.
      intro; apply (proj2_sig (IHl _)).
  Qed.

  Fact bar_secures_lift R x l t : bar_secures (good R↑x) l t → bar_secures (good R) (l++[x]) t.
  Proof.
    induction t as [ | ρ IH ] in R, x, l |- *; simpl.
    + apply good_rel_lift.
    + intros H ?; apply IH with (1 := H _).
  Qed.

  Implicit Type φ : nat → X.

  Fixpoint WFT_lift t :=
    match t with
    | leaf   => node (λ _, leaf)
    | node ρ => node (λ a, WFT_lift (ρ a))
    end.

  Fixpoint WFT_ht φ t :=
    match t with
    | leaf   => 0
    | node ρ => 1 + WFT_ht ↓φ (ρ (φ 0))
    end.

  Fact WFT_lift_ht φ t : WFT_ht φ (WFT_lift t) = 1 + WFT_ht φ t.
  Proof. induction t in φ |- *; simpl; auto. Qed.

  Fact af_secures_bar_secures R t : af_secures R t → bar_secures (good R) [] (WFT_lift (WFT_lift t)).
  Proof.
    induction t as [ | ρ IH ] in R |- *; simpl.
    + intros ? x ?; constructor 1 with x; simpl; auto.
    + intros H ?; apply bar_secures_lift with (l := []), IH, H.
  Qed.

  Fact bar_secures_bound P l t φ : bar_secures P l t → P (pfx_rev φ (WFT_ht φ t)++l).
  Proof.
    induction t as [ | ρ IH ] in l, φ |- *; intros HP; auto.
    simpl WFT_ht; rewrite pfx_rev_S, app_ass.
    apply IH, HP.
  Qed.

  Fact bar_secures_nil_bound P t φ : bar_secures P [] t → P (pfx_rev φ (WFT_ht φ t)).
  Proof. intros; rewrite app_nil_end; now apply bar_secures_bound. Qed.

  Fact af_secures_good_bound R t φ : af_secures R t → good R (pfx_rev φ (2+WFT_ht φ t)).
  Proof.
    intros ?%af_secures_bar_secures.
    apply bar_secures_nil_bound with (φ := φ) in H.
    now rewrite !WFT_lift_ht in H.
  Qed.

  Fact bar_secures_af_secures R l t : bar_secures (good R) l t → af_secures (R⇈l) t.
  Proof.
    induction t as [ | ρ IH ] in l |- *; simpl.
    + intros; apply rel_lift_rel_iff_good; auto.
    + intros; now apply IH with (l := _::_).
  Qed.

  Fact af_secures_bound R t φ : af_secures R t → ∃ i j, i < j < 2+WFT_ht φ t ∧ R (φ i) (φ j).
  Proof. intros; now apply good_pfx_rev, af_secures_good_bound. Qed.

  Theorem brouwer_bar P l t : (∀φ, P (pfx_rev φ (1+WFT_ht φ t)++l)) → bar_secures P l (WFT_lift t).
  Proof.
    induction t as [ | f IHf ] in l |- *; intros Hf.
    + simpl in Hf |- *.
      intros a; apply (Hf (fun _ => a)).
    + simpl plus in Hf; simpl.
      intros a.
      apply IHf.
      intros phi.
      specialize (Hf (a⋅phi)).
      rewrite pfx_rev_S in Hf.
      rewrite app_ass in Hf.
      apply Hf.
  Qed.

  Theorem brouwer_af R t : (∀φ, good R (pfx_rev φ (WFT_ht φ t))) → af_secures R (WFT_lift t).
  Proof.
    intros H.
    apply bar_secures_af_secures with (l := []), brouwer_bar.
    intro phi; rewrite <- app_nil_end; constructor 2; auto.
  Qed.

  Theorem bar_brouwer P l : bar P l → { t | ∀φ, P (pfx_rev φ (WFT_ht φ t)++l) }.
  Proof.
    intros (t & Ht)%bar_bar_secures.
    exists t.
    induction t as [ | f IHf ] in l, Ht |- *; intros phi; simpl in Ht; auto.
    simpl WFT_ht; rewrite pfx_rev_S, app_ass.
    apply IHf with (l := _::l); auto.
  Qed.

  Theorem af_brouwer R : af R → { t | ∀φ, good R (pfx_rev φ (WFT_ht φ t)) }.
  Proof.
    intros (t & Ht)%af_iff_bar_good_nil%bar_brouwer.
    exists t; intros phi.
    specialize (Ht phi).
    now rewrite <- app_nil_end in Ht.
  Qed.

  Fixpoint stump (t : WFT) : list X → Prop :=
    match t with 
    | leaf   => λ _, False
    | node ρ => λ l, l = [] ∨ ∃ x l', l = l'++[x] ∧ stump (ρ x) l'
    end.

  Fact stump_ht t φ n : stump t (pfx_rev φ n) → n < WFT_ht φ t.
  Proof.
    induction t as [ | ρ IH ] in φ, n |- *; simpl.
    + easy.
    + intros [ E | (x & l' & E & H) ].
      * destruct n; lia || easy.
      * destruct n as [ | n ].
        1: now destruct l'.
        rewrite pfx_rev_S in E.
        apply app_inj_tail in E as []; subst.
        apply IH in H; lia.
  Qed.

  Definition Brouwer_thesis :=
          ∀P : list X → Prop, 
               (∀φ, (∃n, P (pfx_rev φ n)))
             → ∃t, ∀φ, ∃n, P (pfx_rev φ n) ∧ stump t (pfx_rev φ n).

  Theorem Brouwer_thesis_monotonic : 
          Brouwer_thesis
        → ∀P : list X → Prop, 
               (∀ l r, P r → P (l++r))
             → (∀φ, ∃n, P (pfx_rev φ n))
             → ∃t, ∀φ, P (pfx_rev φ (WFT_ht φ t)).
  Proof.
    intros BT P Pmono HP.
    destruct (BT P) as (t & Ht); auto.
    exists t; intros phi.
    destruct (Ht phi) as (h & H1 & H2).
    apply stump_ht in H2.
    replace (WFT_ht phi t) with ((WFT_ht phi t-h)+h) by lia.
    rewrite pfx_rev_plus.
    now apply Pmono.
  Qed.

  Theorem Brouwer_af : Brouwer_thesis → ∀R, (∀φ, (∃n, good R (pfx_rev φ n))) → ∃t, af_secures R t.
  Proof.
    intros B R HR.
    destruct (Brouwer_thesis_monotonic B) with (2 := HR) as (t & Ht).
    + intros; now apply good_app_left.
    + exists (WFT_lift t); now apply brouwer_af.
  Qed.

End WFT.

Arguments leaf {X}.

Definition AFC X := option (WFT X).

Definition has_AFC X (R : rel₂ X) c :=
  match c with
  | None   => X → False
  | Some t => af_secures R t
  end.

Fact has_AFC_af X R c : @has_AFC X R c → af R.
Proof.
  destruct c; simpl.
  + apply af_secures_af.
  + intros H; constructor 1; intros x; exfalso; eauto.
Qed.

Fact af_has_AFC X R : @af X R → { c | has_AFC R c }.
Proof.
  intros (t & Ht)%af_af_secured.
  now exists (Some t).
Qed.

Inductive lt_AFC  : ∀{X}, AFC X → ∀{Y}, AFC Y → Type :=
  | lt_AFC_0 X Y : @lt_AFC X None Y (Some leaf)
  | lt_AFC_1 X ρ a : @lt_AFC X (Some (ρ a)) X (Some (node ρ)).

Print eq_rect.

Fact lt_AFC_inv X c Y d :
     @lt_AFC X c Y d 
   → match d with
     | None          => False : Type
     | Some leaf     => c = None : Type
     | Some (node ρ) => { e : Y = X & { a : Y | c = eq_rect _ AFC (Some (ρ a)) _ e } }
     end.
Proof.
  destruct 1; auto.
  exists eq_refl; simpl; eauto.
Qed.

Section wf_lt_AFC.

  Variables (P : ∀{X}, AFC X → Type)
            (HP : ∀X (c : AFC X), (∀Y (d : AFC Y), lt_AFC d c → P d) → P c).

  Local Fact P_None X : @P X None.
  Proof.
    apply HP.
    intros ? ? []%lt_AFC_inv.
  Qed.

  Hint Resolve P_None : core.

  Theorem wf_lt_AFC X (c : AFC X) : P c.
  Proof.
    destruct c as [ t | ].
    + induction t as [ | ρ IH ].
      * apply HP.
        intros ? ? ->%lt_AFC_inv; eauto.
      * apply HP.
        intros ? ? (e & a & ->)%lt_AFC_inv.
        subst; simpl; auto.
    + apply P_None.
  Qed.

End wf_lt_AFC.

