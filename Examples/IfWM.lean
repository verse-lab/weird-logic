import Mathlib.Computability.ContextFreeGrammar

import Lgtm.Hyper.ProofMode
import Lgtm.Hyper.ArraysFun
import Lgtm.Unary.Lang
import Lgtm.Experiments.HyperCommon

import WeirdLogic.Gram
import WeirdLogic.WLogic
import WeirdLogic.WTriple
import WeirdLogic.WUtil

open Unary prim val trm
open ContextFreeGrammar

namespace WeirdLogic.Example0

/- L -> trm1 | trm 2

  L = {(trm1|trm2)}

  regular + if rule -/
def trm1 : trm := [lang| fun ⸨xl: Loc⸩ ⸨yl: Loc⸩ => let xx := !xl in let yy := !yl in let temp0 := xx + yy in yl := temp0]
def trm2 : trm := [lang| fun ⸨xl: Loc⸩ ⸨yl: Loc⸩ => let xx := !xl in let yy := !yl in let temp0 := xx - yy in yl := temp0]
def r1 : ContextFreeRule trm String :=
  {
    input := "L",
    output := [Symbol.terminal trm1],
  }

def r2 : ContextFreeRule trm String :=
  {
    input := "L",
    output := [Symbol.terminal trm2],
  }

def cfg1 : ContextFreeGrammar trm :=
  {
    NT := String,
    initial := "L",
    rules := Finset.mk {r1, r2} (by unfold r1 r2 trm1 trm2 trm_funs; simp; unfold trm_funs; simp; unfold trm_funs; simp  )
  }

def l1 : Language trm := cfg1.language

lang_def' WeirdLogic.Example0.prog_c1 :=
  fun ⸨xl: Loc⸩ ⸨yl: Loc⸩ ⸨pb:Val⸩ =>
    let xx := !xl in
    let yy := !yl in
    if pb > 10 then
      let temp0 := xx + yy in
      yl := temp0
    else
      let temp1 := xx - yy in
      yl := temp1

def pay_index' := @Set.univ payload
abbrev lang := List trm

def cfg_expand : Set ( List (Symbol T N)) :=
  {
    [Symbol.terminal trm1],[Symbol.terminal trm2]
  }

  -- {
  --   c | cfg1.Generates c
  -- }

def pay_index1 : Set payload :=
  {
    p | p > 10 ∧ p ∈ pay_index'
  }

def pay_index2 : Set payload :=
  {
    p | p <= 10 ∧ p ∈ pay_index'
  }

def pay_index : Set (trm × payload) :=
  {
    ([lang|()],p) | p ∈ pay_index'
  }

def lang_list_index' : Set lang :=
  {l | (trm_to_symbol_list l) ∈ cfg_expand }

def lang_index' : Set trm :=
  -- {trm1, trm2}
  {squeeze_trm t | t ∈ lang_list_index'}

def lang_index : Set (trm × payload ):=
  { (l,0) | l ∈ lang_index' }

lemma lang_unfold :
  lang_list_index' = {[trm1],[trm2]} := by
  unfold lang_list_index' trm_to_symbol_list cfg_expand -- Generates Derives Produces expand_trm
  ext l
  simp
  constructor
  {
    intro h
    induction h with
    | inl h1 =>
      left
      cases l with
      | nil => simp at h1
      | cons x xs => simp at h1; rcases h1 with ⟨h10,h11⟩ ; subst x ; rcases xs with _ | _ <;> simp [trm_to_symbol_list] at *
    | inr h2 =>
      right
      cases l with
      | nil => aesop
      | cons x xs => simp at h2; unfold trm_to_symbol_list at h2; rcases h2 with ⟨h10,h11⟩ ; subst x ; rcases xs with _ | _ <;> simp [trm_to_symbol_list] at *
  }
  {
    intro h
    induction h with
    | inl h1=> rw [h1]; aesop
    | inr h2=> rw [h2]; aesop
  }

lemma lang_index'_unfold :
  lang_index' = {trm1,trm2} := by
  unfold lang_index' squeeze_trm
  rw [lang_unfold]
  simp_all only [Set.mem_insert_iff, Set.mem_singleton_iff, exists_eq_or_imp, exists_eq_left]
  ext x : 1
  simp_all only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  apply Iff.intro
  · intro a
    cases a with
    | inl h =>
      subst h
      simp_all only [true_or]
    | inr h_1 =>
      subst h_1
      simp_all only [or_true]
  · intro a
    cases a with
    | inl h =>
      subst h
      simp_all only [true_or]
    | inr h_1 =>
      subst h_1
      simp_all only [or_true]

def cfg1_left : ContextFreeGrammar trm :=
  {
    NT := String,
    initial := "L",
    rules := Finset.mk {r1} (by unfold r1 trm1; simp)
  }
def cfg1_right : ContextFreeGrammar trm :=
  {
    NT := String,
    initial := "L",
    rules := Finset.mk {r2} (by unfold r2 trm2; simp)
  }

def lang_set1 : Set trm :=
  {trm1}
def lang_set2 : Set trm :=
  {trm2}

lemma pay_index_union_univ :
  pay_index1 ∪ pay_index2 = pay_index'
  := by
  unfold pay_index1 pay_index2 pay_index'
  simp
  ext x
  simp
  exact Int.lt_or_le 10 x


lemma lang_index_union_univ :
  lang_set2 ∪ lang_set1 = lang_index'
  := by
  unfold lang_set1 lang_set2
  rw [lang_index'_unfold]
  simp

def inLang1 (a : (trm × payload)ˡ) : Prop :=
    a.lab = 1 ∧ a.val.1 ∈ lang_set1

def inLang2 (a : (trm × payload)ˡ) : Prop :=
    a.lab = 1 ∧ a.val.1 ∈ lang_set2

set_option maxRecDepth 2000 in
set_option maxHeartbeats 6400000 in
lemma ifwm_spec (xv : ℤ) (yv : ℤ):
  {
    [∗ in ⟪0,pay_index⟫ ∪ ⟪1,lang_index⟫ | xl ~~> xv ∗ yl ~~> yv]
  }
  [0| p in pay_index => prog_c1(⸨xl: Loc⸩, ⸨yl: Loc⸩, ⟨p.val.2⟩)]
  [1| l in lang_index => l.val.fst(⸨xl: Loc⸩, ⸨yl: Loc⸩)]
  { v,
    fun h => ∀ l ∈ lang_index, ∃ p ∈ pay_index , h ⟨1, l⟩= h ⟨0, p⟩
  }
  := by
  unfold LGTM.triple
  rw [← bighstar_hhstar_disj_dir (s₁ := {⟨0,(default_trm,p)⟩ | p ∈ pay_index1} ∪ {⟨ 1,(l,default_payload)⟩ | l ∈ lang_set1}) (s₂ := {⟨0,(default_trm,p)⟩ | p ∈ pay_index2} ∪ {⟨ 1, (l,default_payload)⟩ | l ∈ lang_set2} )]
  rotate_left
  { apply disjoint_iff.mpr
    unfold lang_set1 lang_set2
    simp
    apply pair_insert_disjoin=>//
    apply disjoint_iff.mpr; simp
    apply pair_set_union_index_right
    unfold pay_index1 pay_index2; aesop
    unfold trm1 trm2 trm_funs; simp; unfold trm_funs; simp; unfold trm_funs; simp;
  }
  {
    conv_rhs =>  rw [Set.union_right_comm, ←Set.union_assoc]
    conv_rhs =>  rw [pair_set_union_index_eq_left pay_index1 pay_index2 pay_index' _ pay_index_union_univ]; rw [Set.union_assoc, Set.union_comm]
    conv_rhs =>  rw [pair_set_union_index_eq_right lang_set2 lang_set1 lang_index' _ lang_index_union_univ]; rw [Set.union_comm]
    unfold pay_index lang_index labSet
    simp
  }
  dsimp only
  /- Step 1: GrmDisj -/
  apply weird_grmdisj_lemma_safe
    (s1 := {x | ∃ l ∈ lang_set1, (l, default_payload) = x})
    (s2 := {x | ∃ l ∈ lang_set2, (l, default_payload) = x})
    (s'1 := {x | ∃ p ∈ pay_index1, (default_trm, p) = x})
    (s'2 := {x | ∃ p ∈ pay_index2, (default_trm, p) = x})=>//
  · simp; apply disjoint_label_set.mpr; simp
  · apply pair_set_union_left
    unfold lang_set1 lang_set2
    unfold trm1 trm2 trm_funs; simp; unfold trm_funs; simp; unfold trm_funs; simp;
  · unfold lang_index
    rw [lang_index'_unfold]
    apply pair_set_union_eq_right
    unfold lang_set1 lang_set2; aesop
  · apply pair_set_union_right
    unfold pay_index1 pay_index2; aesop
  · apply pair_set_union_eq_left
    apply pay_index_union_univ
  · simp [hhlocalE, labSet]
  /- left part -/
  · unfold lang_set1
    /- Step 2: Lang -/
    apply weird_lang_lemma=>//
    { apply disjoint_label_set.mpr; aesop}
    /- Step 3: Payload -/
    rw [← bighstar_hhstar_disj_dir (s₁ := {⟨0,(default_trm,p)⟩ | p ∈ pay_index1 \ {20}}) (s₂ := {⟨0,(default_trm,20)⟩} ∪ {⟨ 1, (l,default_payload)⟩ | l ∈ lang_set1} )]
    rotate_left
    { apply disjoint_iff.mpr
      unfold lang_set1
      aesop }
    {
      unfold pay_index1 pay_index' lang_set1; simp
      apply congr_arg
      ext x
      constructor
      · rintro ⟨p, hp_pos, rfl⟩
        by_cases h10 : p = 20=>//
      · rintro (rfl | ⟨p, ⟨hp_pos, hp_ne⟩, rfl⟩)=>//
     }
    apply weird_payload_index_lemma (pr := (default_trm, 20)) =>//
    { apply disjoint_label_set.mpr; aesop}
    /- first 1/4 -/
    { unfold pay_index1 pay_index';
      simp
      dsimp [LGTM.wp, LGTM.SHTs.htrm]
      rw [hwp_ht_eq (ht₂ := (fun (p : (trm × payload)ˡ) => prog_c1.trm_call [xl, yl, [lang| ⟨p.val.2⟩]]))] --remove union set
      on_goal 2=> simp only [Set.EqOn, fun_insert, Set.union_empty] ; intro a b ; simp only [b, reduceIte]
      unfold prog_c1 --; yapp
      apply ywp_lemma_funs (tfunc := fun _ => prog_c1) (ts := fun (p : (trm × payload)ˡ) => [xl, yl, [lang| ⟨p.val.2⟩]])
      intro _ ; rfl ; intro _ ; rfl ; intros ; rfl ; intros ; simp [get_vars, type_match]
      simp  [Unary.func_call_ctx_prepare]
      all_goals
        try simp [isubstE, Unary.reduce_call_isubst];
        try simp [wpgen]
        try simp [AList.lookup, List.mkAlist, List.eraseP, List.dlookup]
      apply hwp_of_hwpgen
      simp [subst, subst.go]
      ylet;
      have eq : ({x | ∃ (p : payload), (10 < p ∧ ¬p = 20) ∧ ⟨0, (default_trm, p)⟩ = x} : Set (trm × payload)ˡ)
        = (⟪0, {x | ∃ p, 10 < p ∧ (default_trm, p) = x} \ {(default_trm, 20)}⟫ : Set (trm × payload)ˡ)
        := by
        ext a ; rcases a with ⟨l, ⟨a, b⟩⟩ ; simp ; aesop
          -- ext
      rw [eq] ; clear eq --; yapp htriple_get
      rw [←bighstar_hhstar]
      apply htriple_conseq_frame ; apply htriple_get (v := fun _ => xv) ; apply hhimpl_refl
      ysimp
      ywp ; ylet
      rw [hhstar_comm]
      apply htriple_conseq_frame ; apply htriple_get (v := fun _ => yv) ; apply hhimpl_refl
      ysimp
      ywp; ylet
      apply htriple_conseq_frame ; apply htriple_gt ; ysimp
      ysimp
      simp [subst, subst.go]

      rw [hwp_ht_eq (ht₂ := (fun a ↦
      [lang|
        if true then
          let temp0 := xv + yv in
          yl := temp0
        else
          let temp1 := xv - yv in
          yl := temp1]))]
      on_goal 2=> simp only [Set.EqOn, fun_insert, Set.union_empty] ; rintro ⟨l, ⟨a , b⟩⟩ bb ; congr ; simp at bb ⊢ ; aesop
      ywp ; yif
      on_goal 2=> intro a ; contradiction
      intro _
      ywp; ylet;
      rw [bighstar_hhstar]; dsimp

      apply htriple_conseq_frame (H₂ := [∗i in ⟪0, {x | ∃ p, 10 < p ∧ (default_trm, p) = x} \ {(default_trm, 20)}⟫| xl ~~> xv ∗ yl ~~> yv]); apply htriple_binop (v₁ := fun _ => val_int xv) (v₂ := fun _ => val_int yv) (v := fun _ => val_int (xv + yv));
      · intro a ha ; apply evalbinop.evalbinop_add
      · rw [hhstar_hhempty_l]; apply hhimpl_refl
      ysimp
      simp [subst, subst.go]

      rw [←bighstar_hhstar, hhstar_comm];
      apply htriple_conseq_frame (H₂ := [∗i in ⟪0, {x | ∃ p, 10 < p ∧ (default_trm, p) = x} \ {(default_trm, 20)}⟫| xl ~~> xv]); apply htriple_set (hv := fun _ => yv) ; apply hhimpl_refl
      ysimp

      rw [bighstar_hhstar]; simp
      unfold bighstar bighstarDef hsingle hhimpl
      simp
      intro ha pre aa hlab --hpay hgt0 heq hvalnot
      specialize pre aa
      have ain : ¬ aa ∈ ⟪0, {x | ∃ p, 10 < p ∧ (default_trm, p) = x} \ {(default_trm, 20)}⟫ := by
        simp;
        intro h_in hx hgt hheq
        have := hlab h_in hx hgt hheq
        exact this
      simp [ain] at pre
      rw [pre]
    }
    /- second 1/4 -/
    { rw [unsimp_singleton_set]
      rw [← weird_fix_lang (p := default_payload)]
      simp only [LGTM.SHT]
      rw [← weird_fix_payload2 (pv := 20)]

      unfold lang_set1
      unfold default_payload; simp
      yin 0: ywp; ylet; simp [subst, subst.go]
      rw [← Set.union_singleton, ← bighstar_hhstar_disj]
      on_goal 2=> simp
      repeat rw [← hhsingle.eq_1]
      apply htriple_conseq_frame (H₂ := yl ~⟨x in ⟪0, {(default_trm, 20)}⟫⟩~> yv ∗ [∗i in {⟨1, (trm1, 0)⟩}| xl ~~> xv ∗ yl ~~> yv]); apply htriple_get (v := fun _ => xv) ;
      { rw [←bighstar_hhstar]; ysimp; rw [labSet]; simp }
      ysimp
      simp only [OfNat.ofNat, Int.ofNat]; simp
      ywp; ylet; simp [subst, subst.go];
      apply htriple_conseq_frame (H₂ := xl ~⟨x in ⟪0, {(default_trm, 20)}⟫⟩~> xv ∗ [∗i in {⟨1, (trm1, 0)⟩}| xl ~~> xv ∗ yl ~~> yv]); apply htriple_get (v := fun _ => yv) ;
      { ysimp}
      ysimp
      ywp; ylet
      apply htriple_conseq_frame ; apply htriple_gt ; ysimp
      ysimp; simp only [OfNat.ofNat, Zero.zero, Int.ofNat]; simp
      ywp; yif
      on_goal 2=> intro a ; contradiction
      intro _;
      ystep
      apply htriple_conseq_frame; apply htriple_set (hv := fun _ => yv) ; ysimp
      ysimp

      dsimp [LGTM.wp, LGTM.SHTs.htrm]
      rw [hwp_ht_eq (ht₂ := (fun (p : (trm × payload)ˡ) => trm1.trm_call [xl, yl]))]
      on_goal 2=>
        unfold trm1 labSet; simp [Set.EqOn, fun_insert, Set.union_empty];

      rw [←hhstar_assoc, bighstar_hhstar, hhstar_comm]
      dsimp
      apply ywp_lemma_funs (tfunc := fun _ => trm1) (ts := fun (p : (trm × payload)ˡ) => [xl, yl])
      intro _ ; rfl ; intro _ ; rfl ; intros ; rfl ; intros ; simp [get_vars, type_match]
      simp  [Unary.func_call_ctx_prepare]
      all_goals
        try simp [isubstE, Unary.reduce_call_isubst]; --(try simp [Unary.isubst, Unary.isubst.go])--; (srw ?Unary.guard_pos; all_goals try rfl)
        try simp [wpgen]
        try simp [AList.lookup, List.mkAlist, List.eraseP, List.dlookup]
      ywp; ylet; simp [subst, subst.go]

      rw [←bighstar_hhstar, hhstar_assoc]
      apply htriple_conseq_frame (H₂ := [∗i in {⟨1, (trm1, 0)⟩}| yl ~~> yv] ∗ [∗i in ⟪0, {(default_trm, 20)}⟫| yl ~~> val_int (xv + yv) ∗ xl ~~> xv] ); apply htriple_get (v := fun _ => xv);
      { repeat rw [labSet]; simp; rw [labSet]; simp }
      ysimp

      ywp; ylet; simp [subst, subst.go]
      rw [hhstar_comm_assoc]
      apply htriple_conseq_frame (H₂ :=  xl ~⟨x in ⟪1, {(trm1, 0)}⟫⟩~> xv ∗ [∗i in ⟪0, {(default_trm, 20)}⟫| yl ~~> val_int (xv + yv) ∗ xl ~~> xv] ); apply htriple_get (v := fun _ => yv);
      { unfold hhsingle labSet; simp}
      ysimp

      ystep

      apply htriple_conseq_frame (H₂ := xl ~⟨x in ⟪1, {(trm1, 0)}⟫⟩~> xv ∗ [∗i in ⟪0, {(default_trm, 20)}⟫| yl ~~> val_int (xv + yv) ∗ xl ~~> xv]); apply htriple_set (hv := fun _ => yv);
      { ysimp;}
      ysimp

      rw [←hhstar_assoc, bighstar_hhstar]; simp
      rw [bighstar_hhstar_disj]
      on_goal 2=> apply disjoint_label_set.mpr; simp

      unfold bighstar bighstarDef
      simp;
      unfold HStar.hStar instHStarHProp; simp; unfold hstar hsingle; simp
      intro hh hl
      have hl1 := hl ⟨1, (trm1, 0)⟩
      have hl2 := hl ⟨0, (default_trm, 20)⟩
      simp_all
    }
  /- Right Part -/
  ·
    unfold lang_set2
    set H₃ := (fun h : hheap (trm × payload)ˡ =>
        hlocal (⟪0, {x | ∃ p ∈ pay_index1, (default_trm, p) = x}⟫ ∪ ⟪1, {x | ∃ l ∈ lang_set1, (l, default_payload) = x}⟫) h ∧
        ∀ ll ∈ {x | ∃ l ∈ lang_set1, (l, default_payload) = x},
        ∃ pp ∈ {x | ∃ p ∈ pay_index1, (default_trm, p) = x}, h ⟨1, ll⟩ = h ⟨0, pp⟩) with hH3

    dsimp
    rw [unsimp_singleton_set]
    rw [← weird_fix_lang (p := default_payload)]
    -- rw [hH4]
    rw [← bighstar_hhstar_disj]
    rw [← bighstar_hhstar_disj_dir (s₁ := {x | ∃ p ∈ pay_index2 \ {-10}, ⟨0, (default_trm, p)⟩ = x}) (s₂ := {⟨0, (default_trm, -10)⟩})]=>//
    rotate_left
    have eq: ( {⟨0, (default_trm, -10)⟩} : Set (trm × payload)ˡ )= ({ x | ∃ p ∈ ({-10} : Set payload), ⟨0, (default_trm, p)⟩ = x} : Set (trm × payload)ˡ):= by simp
    rw [eq]; clear eq
    rw [pair_set_union_index_eq_left]; simp; unfold pay_index2 pay_index'; simp
    rw [hhstar_symbol_replace]
    rw [hhstar_assoc]
    rw [hhstar_comm_assoc]
    /- ********** have to separate pay_index in the postcondition  -/
    apply weird_payload_index_lemma2
      (pr := (default_trm, -10))
      (s₁ := {x | ∃ p ∈ pay_index2, (default_trm, p) = x})
      (s₃ := pay_index)
      (H₁ := [∗i in {x | ∃ p ∈ pay_index2 \ {-10}, ⟨0, (default_trm, p)⟩ = x}| xl ~~> xv ∗ yl ~~> yv])=>//
    { apply disjoint_label_set.mpr; simp}
    { unfold pay_index pay_index2 pay_index'; simp }
    /- Third 1/4 -/
    { unfold pay_index2 pay_index';
      simp
      dsimp [LGTM.wp, LGTM.SHTs.htrm]
      rw [hwp_ht_eq (ht₂ := (fun (p : (trm × payload)ˡ) => prog_c1.trm_call [xl, yl, [lang| ⟨p.val.2⟩]]))] --remove union set
      on_goal 2=> simp only [Set.EqOn, fun_insert, Set.union_empty] ; intro a b ; simp only [b, reduceIte]
      unfold prog_c1 --; yapp
      apply ywp_lemma_funs (tfunc := fun _ => prog_c1) (ts := fun (p : (trm × payload)ˡ) => [xl, yl, [lang| ⟨p.val.2⟩]])
      intro _ ; rfl ; intro _ ; rfl ; intros ; rfl ; intros ; simp [get_vars, type_match]
      simp  [Unary.func_call_ctx_prepare]
      all_goals
        try simp [isubstE, Unary.reduce_call_isubst]; --(try simp [Unary.isubst, Unary.isubst.go])--; (srw ?Unary.guard_pos; all_goals try rfl)
        try simp [wpgen]
        try simp [AList.lookup, List.mkAlist, List.eraseP, List.dlookup]
      apply hwp_of_hwpgen
      simp [subst, subst.go]
      ylet
      have eq : ({x | ∃ (p : payload), (p ≤ 10 ∧ ¬p = -10) ∧ ⟨0, (default_trm, p)⟩ = x} : Set (trm × payload)ˡ)
        = (⟪0, {x | ∃ p, p ≤ 10 ∧ (default_trm, p) = x} \ {(default_trm, -10)}⟫ : Set (trm × payload)ˡ)
        := by
        ext a ; rcases a with ⟨l, ⟨a, b⟩⟩ ; simp ; aesop
          -- ext
      rw [eq] ; clear eq --; yapp htriple_get
      rw [←bighstar_hhstar]
      apply htriple_conseq_frame ; apply htriple_get (v := fun _ => xv) ; apply hhimpl_refl
      ysimp
      ywp ; ylet
      rw [hhstar_comm]
      apply htriple_conseq_frame ; apply htriple_get (v := fun _ => yv) ; apply hhimpl_refl
      ysimp
      ywp; ylet
      apply htriple_conseq_frame ; apply htriple_gt ; ysimp
      ysimp
      simp [subst, subst.go]

      rw [hwp_ht_eq (ht₂ := (fun a ↦
      [lang|
        if false then
          let temp0 := xv + yv in
          yl := temp0
        else
          let temp1 := xv - yv in
          yl := temp1]))]
      on_goal 2=> simp only [Set.EqOn, fun_insert, Set.union_empty] ; rintro ⟨l, ⟨a , b⟩⟩ bb ; congr ; simp at bb ⊢ ; aesop
      ywp ; yif
      on_goal 1=> intro a ; contradiction
      intro _

      ywp; ylet;
      rw [bighstar_hhstar]; dsimp

      apply htriple_conseq_frame (H₂ := [∗i in ⟪0, {x | ∃ p ≤ 10, (default_trm, p) = x} \ {(default_trm, -10)}⟫| xl ~~> xv ∗ yl ~~> yv]); apply htriple_binop (v₁ := fun _ => val_int xv) (v₂ := fun _ => val_int yv) (v := fun _ => val_int (xv - yv));
      · intro a ha ; apply evalbinop.evalbinop_sub
      · rw [hhstar_hhempty_l]; apply hhimpl_refl
      ysimp
      simp [subst, subst.go]

      rw [←bighstar_hhstar, hhstar_comm];
      apply htriple_conseq_frame; apply htriple_set (hv := fun _ => yv) ; apply hhimpl_refl
      ysimp

      rw [bighstar_hhstar]
      unfold bighstar bighstarDef hsingle hhimpl
      simp
      intro ha pre aa hlab --hpay hgt0 heq hvalnot
      specialize pre aa
      have ain : ¬ aa ∈ ⟪0, {x | ∃ p, p ≤ 10 ∧ (default_trm, p) = x} \ {(default_trm, -10)}⟫ := by
        simp;
        intro h_in hx hgt hheq
        have := hlab h_in hx hgt hheq
        exact this
      simp [ain] at pre
      rw [pre]
    }
    /- Final 1/4 -/
    dsimp
    have payeq : pay_index \ ({x | ∃ p ∈ pay_index2, (default_trm, p) = x} \ {(default_trm, -10)}) = {x | ∃ p ∈ pay_index1 ∪ {-10}, (default_trm, p) = x} := by
      unfold pay_index pay_index1 pay_index2 pay_index'
      simp
      ext x
      unfold default_trm
      simp only [Set.mem_diff, Set.mem_setOf_eq, Set.mem_singleton_iff, not_and, not_exists, not_le]
      constructor
      · rintro ⟨⟨p, rfl⟩, h⟩
        by_cases hp : p ≤ 10
        · by_cases hp10 : p = -10
          · left; simp [hp10]    -- case p = -10
          · right
            have hh : (∃ p_1 ≤ 10, ([lang| ()], p_1) = ([lang| ()], p)) := by
              use p
            specialize h hh
            simp [h]; simp_all
        · right; use p; simp [hp]; simp_all
      · intro h
        rcases h with (rfl | ⟨a, ha_pos, ha_eq⟩)
        · constructor
          use -10
          simp
        · constructor
          use a
          have tmp : (∃ p ≤ 10, ([lang| ()], p) = x) = False := by
            simp
            rw [←ha_eq]
            simp
            intro x hx_le0 hxeq
            rw [hxeq] at hx_le0
            linarith
          simp [tmp]
    rw [payeq]; clear payeq
    set H₅ := fun x h : hheap (trm × payload)ˡ => ∀ ll ∈ lang_index, ∃ pp ∈ {x | ∃ p ∈ pay_index1 ∪ {-10}, (default_trm, p) = x}, h ⟨1, ll⟩ = h ⟨0, pp⟩ with hH5
    rw [← weird_fix_payload2 (pv := -10)]
    unfold default_payload; dsimp
    rw [hhstar_comm, hhstar_assoc]
    yin 0: ywp; ylet; simp [subst, subst.go]
    rw [← hhstar_symbol_replace (hH₁ := [∗i in {⟨1, (trm2, 0)⟩}| xl ~~> xv ∗ yl ~~> yv]) (hH₂ := H₃)]
    rw [←bighstar_hhstar, hhstar_assoc]
    apply htriple_conseq_frame (H₂ := [∗i in {⟨0, (default_trm, -10)⟩}| yl ~~> yv] ∗ hhstar [∗i in {⟨1, (trm2, 0)⟩}| xl ~~> xv ∗ yl ~~> yv] H₃); apply htriple_get (v := fun _ => xv)
    { ysimp; rw [labSet]; simp }
    ysimp
    simp only [OfNat.ofNat, Int.ofNat]; simp
    ywp; ylet; simp [subst, subst.go];

    rw [hhstar_comm_assoc]
    apply htriple_conseq_frame (H₂ := xl ~⟨x in ⟪0, {(default_trm, -10)}⟫⟩~> xv ∗ hhstar [∗i in {⟨1, (trm2, 0)⟩}| xl ~~> xv ∗ yl ~~> yv] H₃); apply htriple_get (v := fun _ => yv)
    { ysimp; rw [labSet]; simp }
    ysimp
    simp only [OfNat.ofNat, Int.ofNat]; simp
    ywp; ylet; simp [subst, subst.go];

    apply htriple_conseq_frame ; apply htriple_gt ; ysimp
    ysimp; simp only [OfNat.ofNat, Zero.zero, Int.ofNat]; simp
    ywp; yif
    on_goal 1=> intro a ; contradiction
    intro _;

    ywp; ylet;
    rw [bighstar_hhstar]; dsimp

    apply htriple_conseq_frame; apply htriple_binop (v₁ := fun _ => val_int xv) (v₂ := fun _ => val_int yv) (v := fun _ => val_int (xv - yv));
    · intro a ha ; apply evalbinop.evalbinop_sub
    · rw [hhstar_hhempty_l]; apply hhimpl_refl
    ysimp
    simp [subst, subst.go]

    rw [←bighstar_hhstar, hhstar_comm, ←bighstar_hhstar, hhstar_assoc, hhstar_comm_assoc];
    apply htriple_conseq_frame; apply htriple_set (hv := fun _ => yv) ; apply hhimpl_refl
    ysimp


    dsimp [LGTM.wp, LGTM.SHTs.htrm]
    rw [hwp_ht_eq (ht₂ := (fun (p : (trm × payload)ˡ) => trm2.trm_call [xl, yl]))]
    on_goal 2=> unfold trm2; simp [Set.EqOn, fun_insert, Set.union_empty];
    apply ywp_lemma_funs (tfunc := fun _ => trm2) (ts := fun (p : (trm × payload)ˡ) => [xl, yl])
    intro _ ; unfold trm2 trm_funs; simp ;
    intro _ ; rfl ; intros ; rfl ; intros ; simp [get_vars, type_match];
    simp  [Unary.func_call_ctx_prepare]
    all_goals
      try simp [isubstE, Unary.reduce_call_isubst]; --(try simp [Unary.isubst, Unary.isubst.go])--; (srw ?Unary.guard_pos; all_goals try rfl)
      try simp [wpgen]
      try simp [AList.lookup, List.mkAlist, List.eraseP, List.dlookup]
    ywp; ylet; simp [subst, subst.go]
    rw [hhstar_comm]

    rw [hhstar_assoc, hhstar_comm_assoc]
    rw [hhstar_symbol_replace,hhstar_assoc,hhstar_assoc]
    rw [← hhstar_symbol_replace (hH₁ := H₃)]
    set H₄ := ([∗i in ⟪0, {(default_trm, -10)}⟫| xl ~~> xv] ∗ yl ~⟨a in ⟪0, {(default_trm, -10)}⟫⟩~> val_int (xv - yv)) with hH4
    apply htriple_conseq_frame (H₂ := [∗i in {⟨1, (trm2, 0)⟩}| yl ~~> yv] ∗ hhstar H₃ H₄); apply htriple_get (v := fun _ => xv);
    { repeat rw [labSet]; simp;}
    ysimp

    ywp; ylet; simp [subst, subst.go]
    apply htriple_conseq_frame (H₂ := [∗i in {⟨1, (trm2, 0)⟩}| xl ~~> xv] ∗ hhstar H₃ H₄); apply htriple_get (v := fun _ => yv);
    { rw [hhstar_comm_assoc] ; unfold labSet; simp}
    ysimp

    rw [labSet]; simp

    ywp; ylet; simp [subst, subst.go]
    apply htriple_conseq_frame; apply htriple_binop (v₁ := fun _ => val_int xv) (v₂ := fun _ => val_int yv) (v := fun _ => val_int (xv - yv));
    · intro a ha ; apply evalbinop.evalbinop_sub
    · rw [hhstar_hhempty_l]; apply hhimpl_refl
    ysimp

    apply htriple_conseq_frame; apply htriple_set (hv := fun _ => yv) ; apply hhimpl_refl
    ysimp

    -- Last step: prove Q' ===> Q
    rw [←hhstar_assoc, bighstar_hhstar]; simp
    unfold H₄ labSet; clear H₄ hH4 H₅ hH5; simp
    rw [bighstar_hhstar]; simp
    rw [hhstar_symbol_replace, hhstar_comm_assoc, hstar_comm (H2 := xl ~~> xv ), bighstar_hhstar_disj]
    on_goal 2 => simp
    simp

    unfold H₃
    rw [labSet]; dsimp
    unfold lang_set1 lang_index; simp
    rw [← lang_index_union_univ]
    unfold lang_set1 lang_set2; simp
    unfold default_payload

    simp [labSet, insert, Set.insert, pay_index1, hlocal]
    rw [Set.setOf_or, ← bighstar_hhstar_disj]
    on_goal 2=> simp
    simp only [Set.setOf_eq_eq_singleton]
    dsimp [hhimpl, HStar.hStar, instHStarHhProp, hhstar, bighstar, bighstarDef]
    rintro h ⟨hh1, hh_, ⟨hlo, ⟨a, ha, hk⟩⟩, ⟨hh2, hh3, hs1, hs2, heq, hdj1⟩, ⟨heq_, hdj2⟩⟩
    subst h hh_
    open Classical in simp [Set.mem_singleton_iff] at hs1 hs2
    constructor
    · exists default_trm, a
      constructor ; aesop
      simp [hk] ; congr! 1
      have hs1' := hs1 ⟨1, (trm1, 0)⟩
      have hs1'' := hs1 ⟨0, (default_trm, a)⟩
      have hs2' := hs2 ⟨1, (trm1, 0)⟩
      have hs2'' := hs2 ⟨0, (default_trm, a)⟩
      rcases ha with ⟨ha1, ha2⟩
      simp at hs1' hs1'' hs2' hs2''
      split at hs1'' ; linarith
      split at hs2'
      next h => simp [trm1, trm2, trm_funs] at h
      rw [hs1', hs1'', hs2', hs2'']
    · exists default_trm, -10
      constructor ; aesop
      simp [hk] ; congr! 1
      repeat rw [hlo]
      · simp
      · simp ; intros ; linarith
      · intro h ; simp [trm1, trm2, trm_funs] at h
      · simp
      · have hs1' := hs1 ⟨1, (trm2, 0)⟩
        have hs1'' := hs1 ⟨0, (default_trm, -10)⟩
        have hs2' := hs2 ⟨1, (trm2, 0)⟩
        have hs2'' := hs2 ⟨0, (default_trm, -10)⟩
        simp at hs1' hs1'' hs2' hs2''
        rw [hs1', hs2'']
        simp; clear hs1' hs2''
        unfold hstar hsingle at hs1'' hs2'
        rcases hs1'' with ⟨ hhh1,hhh2,hs11, hs12,hs13,hs14⟩
        rcases hs2' with ⟨ hhh3,hhh4,hs21, hs22,hs23,hs24⟩
        simp_all


end WeirdLogic.Example0
