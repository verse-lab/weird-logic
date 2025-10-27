import Mathlib.Computability.ContextFreeGrammar

import Lgtm.Hyper.ProofMode
import Lgtm.Hyper.ArraysFun
import Lgtm.Unary.Lang
import Lgtm.Experiments.HyperCommon

import WeirdLogic.Gram
import WeirdLogic.WLogic
import WeirdLogic.WTriple
import WeirdLogic.Util
import WeirdLogic.Hete

open Unary prim val trm
open ContextFreeGrammar

namespace WeirdLogic

/- L -> trm1 | trm 2 -/
def trm1 : trm := [lang| fun ⸨xk: Loc⸩ => let xx := !xk in let temp0 := xx + 1 in xk := temp0]
def trm2 : trm := [lang| fun ⸨xr: Loc⸩ => let xx := !xr in let temp0 := xx + 2 in xr := temp0]
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
    rules := Finset.mk {r1, r2} (by unfold r1 r2 trm1 trm2 trm_funs; simp  )
  }

def l1 : Language trm := cfg1.language

lang_def' prog_c1 :=
  fun ⸨y: Loc⸩ ⸨a:Val⸩ =>
    let xx := !y in
    if a > 0 then
      y := xx + 1
    else
      y := xx + 2

def pay_index' := @Set.univ payload
abbrev lang := List trm

def cfg_expand : Set ( List (Symbol T N)) :=
  {
    [Symbol.terminal trm1],[Symbol.terminal trm2]
  }
  -- {
  --   [Symbol.terminal trm0, Symbol.terminal trm1],[Symbol.terminal trm0, Symbol.terminal trm2]
  -- }
  -- {
  --   c | cfg1.Generates c
  -- }

-- cfg_expand \ {x=x+1}

def pay_index1 : Set payload :=
  {
    p | p > 0 ∧ p ∈ pay_index'
  }

def pay_index2 : Set payload :=
  {
    p | p <= 0 ∧ p ∈ pay_index'
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
      | cons x xs => simp at h1; rcases h1 with ⟨h10,h11⟩ ; sorry
    | inr h2 =>
      right
      cases l with
      | nil => aesop
      | cons x xs => simp at h2; unfold trm_to_symbol_list at h2; sorry
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

#check Language.instMembershipList
#check l1
#print LGTM.SHT.mk
#check LGTM.triple

variable (xptr : loc) (x_ptr : ℤ -> ℤ)

-- lemma example4_spec_origin(f : ℤ -> val):
--   {
--     [∗ in Set.univ | H ] ∗ arr⟨⋆⟩(xptr , i in 1 =>f i)
--   }
--   [0| p in pay_index => prog_c1(⟨val_int (Sum.getRight! p.val)⟩)]
--   [1| l in lang_index => ⟦Sum.getLeft! l.val⟧]
--   { v,
--     fun h => ∀ l ∈ lang_index', ∃ p , h ⟨1, Sum.inl l⟩ = h ⟨0, Sum.inr p⟩
--   } := by
--   unfold LGTM.triple
--   sorry


abbrev default_payload : payload:= 0
abbrev default_trm : trm := [lang|()]

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
  exact Int.lt_or_le 0 x


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
lemma example4_spec (xv : ℤ):
  {
    xl ~⟨i in {⟨0,p⟩ | p ∈ pay_index} ∪ {⟨1,l⟩ | l ∈ lang_index}⟩~> xv
  }
  [0| p in pay_index => prog_c1(⸨xl: Loc⸩, ⟨p.val.2⟩)]
  [1| l in lang_index => l.val.fst(⸨xl: Loc⸩)]
  { v,
    fun h => ∀ l ∈ lang_index, ∃ p ∈ pay_index , h ⟨1, l⟩= h ⟨0, p⟩
  }
  := by
  unfold LGTM.triple hhsingle
  rw [← bighstar_hhstar_disj_dir (s₁ := {⟨0,(default_trm,p)⟩ | p ∈ pay_index1} ∪ {⟨ 1,(l,default_payload)⟩ | l ∈ lang_set1}) (s₂ := {⟨0,(default_trm,p)⟩ | p ∈ pay_index2} ∪ {⟨ 1, (l,default_payload)⟩ | l ∈ lang_set2} )]
  rotate_left
  { apply disjoint_iff.mpr
    unfold lang_set1 lang_set2
    simp
    apply pair_insert_disjoin=>//
    apply disjoint_iff.mpr; simp
    apply pair_set_union_index_right
    unfold pay_index1 pay_index2; aesop
    unfold trm1 trm2 trm_funs; aesop
  }
  {
    conv_rhs =>  rw [Set.union_right_comm, ←Set.union_assoc]
    conv_rhs =>  rw [pair_set_union_index_eq_left pay_index1 pay_index2 pay_index' _ pay_index_union_univ]; rw [Set.union_assoc, Set.union_comm]
    conv_rhs =>  rw [pair_set_union_index_eq_right lang_set2 lang_set1 lang_index' _ lang_index_union_univ]; rw [Set.union_comm]
    rw [pair_wrap_eq_right _ default_trm pay_index' pay_index ]
    rw [pair_wrap_eq_left _ default_payload lang_index' lang_index]
    · unfold lang_index default_payload; simp
    · unfold lang_index; aesop
    · unfold pay_index default_trm; aesop
    · unfold pay_index; aesop
  }
  /- Step 1: GrmDisj -/
  apply weird_grmdisj_lemma_safe
    (s1 := {x | ∃ l ∈ lang_set1, (l, default_payload) = x})
    (s2 := {x | ∃ l ∈ lang_set2, (l, default_payload) = x})
    (s'1 := {x | ∃ p ∈ pay_index1, (default_trm, p) = x})
    (s'2 := {x | ∃ p ∈ pay_index2, (default_trm, p) = x})=>//
  · simp; apply disjoint_label_set.mpr; simp
  · apply pair_set_union_left
    unfold lang_set1 lang_set2
    unfold trm1 trm2 trm_funs; simp
  · unfold lang_index
    rw [lang_index'_unfold]
    apply pair_set_union_eq_right
    unfold lang_set1 lang_set2; aesop
  · apply pair_set_union_right
    unfold pay_index1 pay_index2; aesop
  · apply pair_set_union_eq_left
    apply pay_index_union_univ
  /- left part -/
  · unfold lang_set1
    /- Step 2: Lang -/
    apply weird_lang_lemma=>//
    { apply disjoint_label_set.mpr; aesop}
    /- Step 3: Payload -/
    rw [← bighstar_hhstar_disj_dir (s₁ := {⟨0,(default_trm,p)⟩ | p ∈ pay_index1 \ {10}}) (s₂ := {⟨0,(default_trm,10)⟩} ∪ {⟨ 1, (l,default_payload)⟩ | l ∈ lang_set1} )]
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
        by_cases h10 : p = 10=>//
      · rintro (rfl | ⟨p, ⟨hp_pos, hp_ne⟩, rfl⟩)=>//
     }
    apply weird_payload_index_lemma (pr := (default_trm, 10)) =>//
    { apply disjoint_label_set.mpr; aesop}
    /- first 1/4 -/
    { unfold pay_index1 pay_index';
      simp
      dsimp [LGTM.wp, LGTM.SHTs.htrm]
      rw [hwp_ht_eq (ht₂ := (fun (p : (trm × payload)ˡ) => prog_c1.trm_call [xl, [lang| ⟨p.val.2⟩]]))] --remove union set
      on_goal 2=> simp only [Set.EqOn, fun_insert, Set.union_empty] ; intro a b ; simp only [b, reduceIte]
      unfold prog_c1 --; yapp
      apply ywp_lemma_funs (tfunc := fun _ => prog_c1) (ts := fun (p : (trm × payload)ˡ) => [xl, [lang| ⟨p.val.2⟩]])
      intro _ ; rfl ; intro _ ; rfl ; intros ; rfl ; intros ; simp [get_vars, type_match]
      -- unfold prog_c1
      simp  [Unary.func_call_ctx_prepare]
      all_goals
        try simp [isubstE, Unary.reduce_call_isubst]; --(try simp [Unary.isubst, Unary.isubst.go])--; (srw ?Unary.guard_pos; all_goals try rfl)
        try simp [wpgen]
        -- try simp [substE, Unary.reduce_call_subst]; (srw ?Unary.subst ?Unary.subst.go ?Unary.subst /==/- ?Unary.guard_pos; all_goals try rfl-/)
        -- try simp [substlE, Unary.reduce_call_substl]; (srw ?Unary.substl ?Unary.substl.go ?Unary.substl /==/- ?Unary.guard_pos; all_goals try rfl-/)
        try simp [AList.lookup, List.mkAlist, List.eraseP, List.dlookup]
      apply hwp_of_hwpgen
      -- all_goals try simp [hwpgen]
      simp [subst, subst.go]
      ylet
      have eq : ({x | ∃ (p : payload), (0 < p ∧ ¬p = 10) ∧ ⟨0, (default_trm, p)⟩ = x} : Set (trm × payload)ˡ)
        = (⟪0, {x | ∃ p, 0 < p ∧ (default_trm, p) = x} \ {(default_trm, 10)}⟫ : Set (trm × payload)ˡ)
        := by
        ext a ; rcases a with ⟨l, ⟨a, b⟩⟩ ; simp ; aesop
          -- ext
      rw [eq] ; clear eq --; yapp htriple_get
      apply htriple_conseq ; apply htriple_get (v := fun _ => xv) ; apply hhimpl_refl
      ysimp
      ywp ; ylet
      apply htriple_conseq_frame ; apply htriple_gt ; ysimp
      ysimp ; simp [subst, subst.go]

      rw [hwp_ht_eq (ht₂ := (fun a ↦
      [lang|
        if true then
          let temp1 := xv + 1 in
          xl := temp1
        else
          let temp2 := xv + 2 in
          xl := temp2]))]
      on_goal 2=> simp only [Set.EqOn, fun_insert, Set.union_empty] ; rintro ⟨l, ⟨a , b⟩⟩ bb ; congr ; simp at bb ⊢ ; aesop
      ywp ; yif
      on_goal 2=> intro a ; contradiction
      intro _
      ystep
      apply htriple_conseq ; apply htriple_set (hv := fun _ => xv) ; apply hhimpl_refl
      ysimp
      unfold hhsingle bighstar bighstarDef hsingle hhimpl
      simp
      intro ha pre aa hlab --hpay hgt0 heq hvalnot
      specialize pre aa
      have ain : ¬ aa ∈ ⟪0, {x | ∃ p, 0 < p ∧ (default_trm, p) = x} \ {(default_trm, 10)}⟫ := by
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
      rw [← weird_fix_payload1 (pv := 10)]

      unfold lang_set1
      unfold default_payload; simp
      yin 0: ywp; ylet; simp [subst, subst.go]
      rw [← Set.union_singleton, ← bighstar_hhstar_disj]
      on_goal 2=> simp
      repeat rw [← hhsingle.eq_1]
      apply htriple_conseq_frame (H₂ := xl ~⟨i in {⟨1, (trm1, 0)⟩}⟩~> xv); apply htriple_get (v := fun _ => xv) ;
      { ysimp; rw [labSet]; simp }
      ysimp
      simp only [OfNat.ofNat, Int.ofNat]; simp
      ywp; ylet; simp [subst, subst.go];
      apply htriple_conseq_frame ; apply htriple_gt ; ysimp
      ysimp; simp only [OfNat.ofNat, Zero.zero, Int.ofNat]; simp
      ywp; yif
      on_goal 2=> intro a ; contradiction
      intro _;
      ystep
      apply htriple_conseq_frame (H₂ := xl ~⟨i in {⟨1, (trm1, 0)⟩}⟩~> xv) ; apply htriple_set (hv := fun _ => xv) ; ysimp
      ysimp

      dsimp [LGTM.wp, LGTM.SHTs.htrm]
      rw [hwp_ht_eq (ht₂ := (fun (p : (trm × payload)ˡ) => [lang| fun ⸨xk: Loc⸩ => let xx := !xk in let temp0 := xx + 1 in xk := temp0].trm_call [xl]))]
      on_goal 2=> unfold trm1; simp [Set.EqOn, fun_insert, Set.union_empty];
      apply ywp_lemma_funs (tfunc := fun _ => trm1) (ts := fun (p : (trm × payload)ˡ) => [xl])
      intro _ ; rfl ; intro _ ; rfl ; intros ; rfl ; intros ; simp [get_vars, type_match]
      simp  [Unary.func_call_ctx_prepare]
      all_goals
        try simp [isubstE, Unary.reduce_call_isubst]; --(try simp [Unary.isubst, Unary.isubst.go])--; (srw ?Unary.guard_pos; all_goals try rfl)
        try simp [wpgen]
        -- try simp [substE, Unary.reduce_call_subst]; (srw ?Unary.subst ?Unary.subst.go ?Unary.subst /==/- ?Unary.guard_pos; all_goals try rfl-/)
        -- try simp [substlE, Unary.reduce_call_substl]; (srw ?Unary.substl ?Unary.substl.go ?Unary.substl /==/- ?Unary.guard_pos; all_goals try rfl-/)
        try simp [AList.lookup, List.mkAlist, List.eraseP, List.dlookup]
      ywp; ylet; simp [subst, subst.go]
      rw [hhstar_comm]
      apply htriple_conseq_frame (H₂ := xl ~⟨a in {⟨0, (default_trm, 10)⟩}⟩~> val_int (xv + 1 )); apply htriple_get (v := fun _ => xv);
      { repeat rw [labSet]; simp; rw [labSet]; simp }
      ysimp
      ystep
      apply htriple_conseq_frame (H₂ := xl ~⟨a in {⟨0, (default_trm, 10)⟩}⟩~> val_int (xv + 1 )); apply htriple_set (hv := fun _ => xv);
      { ysimp; rw [labSet]; simp }
      ysimp
      rw [bighstar_hhstar_disj, Set.union_singleton]
      on_goal 2=> rw [labSet]; simp
      rw [labSet]; simp

      unfold hhimpl
      unfold bighstar bighstarDef
      simp;
      intro hh hl
      have hl1 := hl ⟨1, (trm1, 0)⟩
      have hl2 := hl ⟨0, (default_trm, 10)⟩
      simp_all
      rw [hl1, hl2]
    }
  /- Right Part -/
  · unfold lang_set2
    set H₃ := (fun h : hheap (trm × payload)ˡ =>
        ∀ ll ∈ {x | ∃ l ∈ lang_set1, (l, default_payload) = x},
        ∃ pp ∈ {x | ∃ p ∈ pay_index1, (default_trm, p) = x}, h ⟨1, ll⟩ = h ⟨0, pp⟩) with hH3
    set H₄ := [∗i in ({x | ∃ p ∈ pay_index2, ⟨0, (default_trm, p)⟩ = x} : Set (trm × payload)ˡ) ∪ ({x | ∃ l ∈ ({trm2}: Set trm), ⟨1, (l, default_payload)⟩ = x} : Set (trm × payload)ˡ)| (fun i ↦ xl) i ~~> (fun i ↦ xv) i] with hH4
    dsimp
    -- have weakenH3 : H₃ ==> fun (h : (hheap (trm × payload)ˡ))=> ∀ ll ∈ {x | ∃ l ∈ lang_set1, (l, default_payload) = x}, ∃ pp ∈ pay_index, h ⟨1, ll⟩ = h ⟨0, pp⟩ := by
    --   rw [hH3]
    --   intro hh
    --   apply hheap_weaken_forall'
    --   unfold pay_index pay_index' pay_index1 pay_index' default_trm
    --   simp
    -- rw [hhstar_symbol_replace]
    -- have reH3 := hhimpl_frame_l H₃ (fun (h : (hheap (trm × payload)ˡ))=> ∀ ll ∈ {x | ∃ l ∈ lang_set1, (l, default_payload) = x}, ∃ pp ∈ pay_index, h ⟨1, ll⟩ = h ⟨0, pp⟩) H₄ weakenH3
    -- rw [← hhstar_symbol_replace]
    -- rw [← hhstar_symbol_replace] at reH3
    -- apply hhimpl_trans=>//
    have pre1 : {x | ∃ l ∈ lang_set2, (l, default_payload) = x} ∪ {x | ∃ l ∈ lang_set1, (l, default_payload) = x} = lang_index := by sorry
    have pre2 : {x | ∃ p ∈ pay_index2, (default_trm, p) = x} ∪ {x | ∃ p ∈ pay_index1, (default_trm, p) = x} = pay_index := by sorry
    have pre3 : Disjoint {x | ∃ l ∈ lang_set2, (l, default_payload) = x} {x | ∃ l ∈ lang_set1, (l, default_payload) = x} := by sorry
    have pre4 : Disjoint {x | ∃ p ∈ pay_index2, (default_trm, p) = x} {x | ∃ p ∈ pay_index1, (default_trm, p) = x} := by sorry
    have strongQ := hqstar_disjoint_lang_index_eq lang_index pay_index
      {x | ∃ l ∈ lang_set2, (l, default_payload) = x} {x | ∃ l ∈ lang_set1, (l, default_payload) = x}
      {x | ∃ p ∈ pay_index2, (default_trm, p) = x} {x | ∃ p ∈ pay_index1, (default_trm, p) = x}
      pre1 pre2 pre3 pre4
    have strongwp := weird_wp_conseq [{ s := ⟪0, {x | ∃ p ∈ pay_index2, (default_trm, p) = x}⟫, ht := fun p ↦ prog_c1.trm_call [xl, [lang| ⟨p.val.2⟩]] }, { s := ⟪1, {x | ∃ l ∈ ({trm2} : Set trm), (l, default_payload) = x}⟫, ht := fun l ↦ l.val.1.trm_call [xl] }]
      (hqstar
        (fun hv' h ↦
          ∀ ll ∈ {x | ∃ l ∈ lang_set2, (l, default_payload) = x},
            ∃ pp ∈ {x | ∃ p ∈ pay_index2, (default_trm, p) = x}, h ⟨1, ll⟩ = h ⟨0, pp⟩)
        fun h ↦
        ∀ ll ∈ {x | ∃ l ∈ lang_set1, (l, default_payload) = x},
          ∃ pp ∈ {x | ∃ p ∈ pay_index1, (default_trm, p) = x}, h ⟨1, ll⟩ = h ⟨0, pp⟩)
      (fun hv' h ↦ ∀ ll ∈ lang_index, ∃ pp ∈ pay_index, h ⟨1, ll⟩ = h ⟨0, pp⟩)
      strongQ
    apply hhimpl_trans_r=>//
    clear strongwp strongQ pre1 pre2 pre3 pre4

    -- rotate_left
    -- { unfold lang_index
    --   rw [←lang_index_union_univ]
    --   unfold lang_set1 lang_set2 default_payload
    --   aesop
    -- }
    -- {
    --   unfold lang_set1 lang_set2
    --   unfold trm1 trm2 trm_funs
    --   simp
    -- }
    rw [hqstar_symbol_replace]
    have wpfram := LGTM.wp_frame
      (sht := [{ s := ⟪0, {x | ∃ p ∈ pay_index2, (default_trm, p) = x}⟫, ht := fun p ↦ prog_c1.trm_call [xl, [lang| ⟨p.val.2⟩]] }, { s := ⟪1, {x | ∃ l ∈ ({trm2} : Set trm), (l, default_payload) = x}⟫, ht := fun l ↦ l.val.1.trm_call [xl] }] )
      ((fun hv' (h:hheap (trm × payload)ˡ) => ∀ ll ∈ {x | ∃ l ∈ lang_set2, (l, default_payload) = x}, ∃ pp ∈ {x | ∃ p ∈ pay_index2, (default_trm, p) = x}, h ⟨1, ll⟩ = h ⟨0, pp⟩))
      (fun h ↦ ∀ ll ∈ {x | ∃ l ∈ lang_set1, (l, default_payload) = x}, ∃ pp ∈ {x | ∃ p ∈ pay_index1, (default_trm, p) = x}, h ⟨1, ll⟩ = h ⟨0, pp⟩)
    apply hhimpl_trans_r=>//
    rw [hhstar_symbol_replace]
    rw [hhstar_comm (hH₂ := H₄) (hH₁ := H₃)]
    apply hhimpl_frame_l
    rw [hH4]
    clear wpfram hH4 hH3 H₃ H₄

    rw [unsimp_singleton_set]
    rw [← weird_fix_lang (p := default_payload)]
    rw [← bighstar_hhstar_disj]
    rw [← bighstar_hhstar_disj_dir (s₁ := {x | ∃ p ∈ pay_index2 \ {-10}, ⟨0, (default_trm, p)⟩ = x}) (s₂ := {⟨0, (default_trm, -10)⟩})]=>//
    rotate_left
    have eq: ( {⟨0, (default_trm, -10)⟩} : Set (trm × payload)ˡ )= ({ x | ∃ p ∈ ({-10} : Set payload), ⟨0, (default_trm, p)⟩ = x} : Set (trm × payload)ˡ):= by simp
    rw [eq]; clear eq
    rw [pair_set_union_index_eq_left]; simp; unfold pay_index2 pay_index'; simp

    rw [hhstar_assoc]
    apply weird_payload_index_lemma2
      (pr := (default_trm, -10))
      (s₁ := {x | ∃ p ∈ pay_index2, (default_trm, p) = x})
      (H₁ := [∗i in {x | ∃ p ∈ pay_index2 \ {-10}, ⟨0, (default_trm, p)⟩ = x}| xl ~~> xv])=>//
    { apply disjoint_label_set.mpr; simp}
    /- Third 1/4 -/
    { unfold pay_index2 pay_index';
      simp
      dsimp [LGTM.wp, LGTM.SHTs.htrm]
      rw [hwp_ht_eq (ht₂ := (fun (p : (trm × payload)ˡ) => prog_c1.trm_call [xl, [lang| ⟨p.val.2⟩]]))] --remove union set
      on_goal 2=> simp only [Set.EqOn, fun_insert, Set.union_empty] ; intro a b ; simp only [b, reduceIte]
      unfold prog_c1 --; yapp
      apply ywp_lemma_funs (tfunc := fun _ => prog_c1) (ts := fun (p : (trm × payload)ˡ) => [xl, [lang| ⟨p.val.2⟩]])
      intro _ ; rfl ; intro _ ; rfl ; intros ; rfl ; intros ; simp [get_vars, type_match]
      -- unfold prog_c1
      simp  [Unary.func_call_ctx_prepare]
      all_goals
        try simp [isubstE, Unary.reduce_call_isubst]; --(try simp [Unary.isubst, Unary.isubst.go])--; (srw ?Unary.guard_pos; all_goals try rfl)
        try simp [wpgen]
        try simp [AList.lookup, List.mkAlist, List.eraseP, List.dlookup]
      apply hwp_of_hwpgen
      simp [subst, subst.go]
      ylet
      have eq : ({x | ∃ (p : payload), (p ≤ 0 ∧ ¬p = -10) ∧ ⟨0, (default_trm, p)⟩ = x} : Set (trm × payload)ˡ)
        = (⟪0, {x | ∃ p, p ≤ 0 ∧ (default_trm, p) = x} \ {(default_trm, -10)}⟫ : Set (trm × payload)ˡ)
        := by
        ext a ; rcases a with ⟨l, ⟨a, b⟩⟩ ; simp ; aesop
          -- ext
      rw [eq] ; clear eq --; yapp htriple_get
      apply htriple_conseq ; apply htriple_get (v := fun _ => xv) ; apply hhimpl_refl
      ysimp
      ywp ; ylet
      apply htriple_conseq_frame ; apply htriple_gt ; ysimp
      ysimp ; simp [subst, subst.go]

      rw [hwp_ht_eq (ht₂ := (fun a ↦
      [lang|
        if false then
          let temp1 := xv + 1 in
          xl := temp1
        else
          let temp2 := xv + 2 in
          xl := temp2]))]
      on_goal 2=> simp only [Set.EqOn, fun_insert, Set.union_empty] ; rintro ⟨l, ⟨a , b⟩⟩ bb ; congr ; simp at bb ⊢ ; aesop
      ywp ; yif
      on_goal 1=> intro a ; contradiction
      intro _
      ystep
      apply htriple_conseq ; apply htriple_set (hv := fun _ => xv) ; apply hhimpl_refl
      ysimp
      unfold hhsingle bighstar bighstarDef hsingle hhimpl
      simp
      intro ha pre aa hlab --hpay hgt0 heq hvalnot
      specialize pre aa
      have ain : ¬ aa ∈ ⟪0, {x | ∃ p, p ≤ 0 ∧ (default_trm, p) = x} \ {(default_trm, -10)}⟫ := by
        simp;
        intro h_in hx hgt hheq
        have := hlab h_in hx hgt hheq
        exact this
      simp [ain] at pre
      rw [pre]
    }
    /- Final 1/4 -/
    dsimp
    rw [← weird_fix_payload1 (pv := -10)]
    unfold default_payload; simp
    yin 0: ywp; ylet; simp [subst, subst.go]
    -- rw [← hhstar_symbol_replace (hH₁ := [∗i in {⟨1, (trm2, 0)⟩}| xl ~~> xv]) (hH₂ := H₃)]
    -- apply htriple_conseq_frame (H₂ := hhstar [∗i in {⟨1, (trm2, 0)⟩}| xl ~~> xv] H₃); apply htriple_get (v := fun _ => xv) ;
    apply htriple_conseq_frame (H₂ := [∗i in {⟨1, (trm2, 0)⟩}| xl ~~> xv]); apply htriple_get (v := fun _ => xv) ;
    { ysimp; rw [labSet]; simp }
    ysimp
    simp only [OfNat.ofNat, Int.ofNat]; simp
    ywp; ylet; simp [subst, subst.go];
    apply htriple_conseq_frame ; apply htriple_gt ; ysimp
    ysimp; simp only [OfNat.ofNat, Zero.zero, Int.ofNat]; simp
    ywp; yif
    on_goal 1=> intro a ; contradiction
    intro _;
    ystep
    apply htriple_conseq_frame (H₂ := [∗i in {⟨1, (trm2, 0)⟩}| xl ~~> xv]) ; apply htriple_set (hv := fun _ => xv) ; ysimp
    ysimp

    dsimp [LGTM.wp, LGTM.SHTs.htrm]
    rw [hwp_ht_eq (ht₂ := (fun (p : (trm × payload)ˡ) => [lang| fun ⸨xr: Loc⸩ => let xx := !xr in let temp0 := xx + 2 in xr := temp0].trm_call [xl]))]
    on_goal 2=> unfold trm2; simp [Set.EqOn, fun_insert, Set.union_empty];
    apply ywp_lemma_funs (tfunc := fun _ => trm2) (ts := fun (p : (trm × payload)ˡ) => [xl])
    intro _ ; unfold trm2 trm_funs; simp ;
    intro _ ; rfl ; intros ; rfl ; intros ; simp [get_vars, type_match]
    simp  [Unary.func_call_ctx_prepare]
    all_goals
      try simp [isubstE, Unary.reduce_call_isubst]; --(try simp [Unary.isubst, Unary.isubst.go])--; (srw ?Unary.guard_pos; all_goals try rfl)
      try simp [wpgen]
      try simp [AList.lookup, List.mkAlist, List.eraseP, List.dlookup]
    ywp; ylet; simp [subst, subst.go]
    rw [hhstar_comm]
    -- rw [hhstar_symbol_replace (hH₁ := [∗i in {⟨1, (trm2, 0)⟩}| xl ~~> xv]) (hH₂ := H₃)]
    -- rw [hhstar_assoc]
    -- rw [← hhstar_symbol_replace (hH₁ := H₃)]
    have eq : (xl ~⟨a in ⟪OfNat.ofNat (OfNat.ofNat (OfNat.ofNat 0)), {(default_trm, -10)}⟫⟩~> val_int (xv + 2)) = (xl ~⟨a in ⟪0, {(default_trm, -10)}⟫⟩~> val_int (xv + 2)) := by
      simp
    rw [eq]; clear eq
    apply htriple_conseq_frame (H₂ := [∗i in {⟨0, (default_trm, -10)⟩}| xl ~~> val_int (xv + 2)]); apply htriple_get (v := fun _ => xv);
    { repeat rw [labSet]; simp; rw [labSet]; unfold hhsingle; simp; }
    ysimp
    ystep
    apply htriple_conseq_frame (H₂ := [∗i in {⟨0, (default_trm, -10)⟩}| xl ~~> val_int (xv + 2)]); apply htriple_set (hv := fun _ => xv);
    { ysimp}
    ysimp

    rw [bighstar_hhstar_disj, Set.union_singleton]
    on_goal 2=> rw [labSet]; simp
    rw [labSet]; simp
    unfold lang_set2; simp
    unfold hhimpl
    unfold bighstar bighstarDef
    simp;
    intro hh hl
    have hl1 := hl ⟨1, (trm2, 0)⟩
    have hl2 := hl ⟨0, (default_trm, -10)⟩
    simp_all
    rw [hl1, hl2]

#check Function.partialInv_left
#print bighstar_hhstar_disj

-- lemma hharray_disj (s₁ : Set α) (f : ℤ → val):
--   arr⟨s₁⟩(p , x in n =>f x) ∗ arr⟨⋆ \ s₁⟩(p , x in n =>f x) = arr⟨⋆⟩(p , x in n =>f x) :=by
--   have tmp : arr⟨⋆⟩(p , x in n =>f x) = arr⟨s₁ ∪ (⋆ \ s₁)⟩(p , x in n =>f x) := by
--     congr!
--     exact Eq.symm (Set.union_diff_cancel' (fun ⦃a⦄ a ↦ a) fun ⦃a⦄ a ↦ trivial)
--   rw [tmp]
--   unfold hharrayFun
--   apply eq_comm.mpr
--   symm
--   apply bighstar_hhstar_disj (s₂ := ⋆ \ s₁)=>//
--   exact Set.disjoint_sdiff_right

-- lemma example4_spec_hete (f : ℤ -> val):
--   {
--     -- ⊤
--     -- [∗ in Set.univ | H ] ∗
--     arr⟨⋆⟩(xptr , i in 1 =>f i) -- replace it
--   }
--   [0| Sum.inr| p in pay_index' => prog_c1(⟨f 1⟩, ⟨p.val⟩)]
--   [1| Sum.inl| l in lang_index' => ⟦l.val⟧]

--   { v,
--     fun h => ∀ ll ∈ lang_index', ∃ pp , pp ∈ pay_index' ∧ h ⟨1, Sum.inl ll⟩ = h ⟨0, Sum.inr pp⟩
--   } := by
--   unfold LGTM.triple
--   unfold LGTM.HSHT.mkSHT LGTM.Labeled.map Set.image
--   dsimp
--   stop
--   apply weird_grmdisj_lemma
--     (s' := left_lang_index)
--     (H := arr⟨⟪0,⋆ ⟫⟩(xptr , i in 1 =>f i))
--     (H₁ := arr⟨⟪1,left_lang_index⟫⟩(xptr , i in 1 =>f i))
--     (H₂ := arr⟨⟪1,right_lang_index⟫⟩(xptr , i in 1 =>f i))
--     (HH := arr⟨⋆⟩(xptr , i in 1 =>f i))
--     =>//
--   · unfold labSet pay_index; simp_all
--   · unfold labSet lang_index lang_index'; simp_all
--   · unfold left_lang_index lang_index
--     simp_all
--   · sorry
--   · sorry
--   · sorry
--   /- left part: goes to false branch-/
--   · set pay_s := { p | p<=0 ∧ p ∈ pay_index'}
--     set pay_s' : Set (trm ⊕ payload) := (fun p => Sum.inr p) '' pay_s
--     set hsub := pay_index' \ pay_s
--     set hsub_sum : Set (trm ⊕ payload)ˡ := (fun p => ⟨0, Sum.inr p⟩) '' hsub
--     set H₁ := arr⟨hsub_sum⟩(xptr , i in 1 =>f i)
--     set H₂ := arr⟨⋆ \ hsub_sum⟩(xptr , i in 1 =>f i)
--     have trans_pre : H₁ ∗ H₂ = arr⟨⋆⟩(xptr , i in 1 =>f i) := by
--       unfold H₁ H₂
--       apply hharray_disj (s₁ := hsub_sum)
--       aesop
--     rw [← trans_pre]
--     apply weird_weaken_lemma (s := pay_index) (s'' := lang_index \ {(Sum.inl [lang| x := x + 1])}) (s' := pay_s') (H₁ := H₁) (H₂ := H₂) =>//
--     · unfold labSet pay_index; simp_all
--     · unfold pay_index pay_s'
--       aesop
--     · simp_all
--       apply Set.disjoint_iff_inter_eq_empty.mpr
--       aesop
--     /- left part: solvable using ystep and yif if can do case analysis inside ht -/
--     · simp_all; unfold H₁ hsub_sum
--       apply ysubst_lemma («σ» := Sum.getRight!)=>//
--       sorry
--     /- right part: shrink payload to p<=0 -/
--     · simp
--       sorry
--   /- right part: goes to true branch-/
--   · set pay_s := { p | p>0 ∧ p ∈ pay_index'}
--     set pay_s' : Set (trm ⊕ payload) := (fun p => Sum.inr p) '' pay_s
--     set hsub := pay_index' \ pay_s
--     set hsub_sum : Set (trm ⊕ payload)ˡ := (fun p => ⟨0, Sum.inr p⟩) '' hsub
--     set H₁ := arr⟨hsub_sum⟩(xptr , i in 1 =>f i)
--     set H₂ := arr⟨⋆ \ hsub_sum⟩(xptr , i in 1 =>f i)
--     have trans_pre : H₁ ∗ H₂ = arr⟨⋆⟩(xptr , i in 1 =>f i) := by
--       unfold H₁ H₂
--       apply hharray_disj (s₁ := hsub_sum)
--       aesop
--     rw [← trans_pre]
--     apply weird_weaken_lemma (s := pay_index) (s'' := {(Sum.inl [lang| x := x + 1])}) (s' := pay_s') (H₁ := H₁) (H₂ := H₂) =>//
--     · unfold labSet pay_index; simp_all
--     · unfold pay_index pay_s'
--       simp_all
--     · simp_all
--       apply Set.disjoint_iff_inter_eq_empty.mpr
--       aesop
--     /- left part: solvable using ystep and yif if can do case analysis inside ht-/
--     · unfold H₁ LGTM.wp prog_c1
--       simp_all
--       -- cases hpi : Function.partialInv (fun x : payloadˡ => ⟨x.lab, Sum.inr x.val⟩) a
--       apply weird_index_subst_left
--       sorry
--     /- right part: shrink p to p>0-/
--     · unfold H₂
--       sorry


end WeirdLogic
