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
def trm0 : trm := [lang| xx := !y]
def trm1 : trm := [lang| y := xx + 1]
def trm2 : trm := [lang| y := xx + 2]
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
    rules := Finset.mk {r1, r2} (by unfold r1 r2 trm1 trm2; simp)
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
    [Symbol.terminal trm0, Symbol.terminal trm1],[Symbol.terminal trm0, Symbol.terminal trm2]
  }
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
  {squeeze_trm t | t ∈ lang_list_index'}

def lang_index : Set (trm × payload ):=
  { (l,0) | l ∈ lang_index' }

lemma lang_unfold :
  lang_list_index' = {[trm0, trm1],[trm0, trm2]} := by
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
  lang_index' = {trm_seq trm0 trm1,trm_seq trm0 trm2} := by
  unfold lang_index' squeeze_trm
  rw [lang_unfold]
  aesop

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
  {trm_seq trm0 trm1}
def lang_set2 : Set trm :=
  {trm_seq trm0 trm2}

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
  unfold lang_set1 lang_set2 lang_index'
  unfold lang_list_index' cfg_expand squeeze_trm
  simp
  sorry

set_option maxRecDepth 2000 in
set_option maxHeartbeats 6400000 in
lemma example4_spec (xv : ℤ):
  {
    xl ~⟨i in {⟨0,p⟩ | p ∈ pay_index} ∪ {⟨1,l⟩ | l ∈ lang_index}⟩~> xv
  }
  [0| p in pay_index => prog_c1(⸨xl: Loc⸩, ⟨p.val.2⟩)]
  [1| l in lang_index => ⟦l.val.1⟧]
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
    unfold trm1 trm2; aesop
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
    unfold trm1 trm2; simp
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
    { rw [unsimp_singleton_set]
      rw [← weird_fix_lang (p := default_payload)]
      rw [← weird_fix_payload1 (pv := 10)]
      unfold lang_set1
      -- unfold bighstar bighstarDef
      -- have qframe : (fun (x : hval (trm × payload)ˡ) ( h : hheap (trm × payload)ˡ) => h ⟨1, (trm0.trm_seq trm1, default_payload)⟩ = h ⟨0, (default_trm, 10)⟩) ===>
      --   fun v: hval  (trm × payload)ˡ =>
      --   (fun h =>
      --     ∀ (a : (trm × payload)ˡ),
      --       if a ∈ {⟨0, (default_trm, 10)⟩} then
      --         h ⟨1, (trm0.trm_seq trm1, default_payload)⟩ = h ⟨0, (default_trm, 10)⟩
      --       else h a = hEmpty a)
      --  := by sorry
      -- dsimp [LGTM.wp, LGTM.SHTs.htrm]
      unfold default_payload; simp
      -- have eq : [∗i in ({⟨1, (trm0.trm_seq trm1, 0)⟩, ⟨0, (default_trm, 10)⟩} : Set (trm × payload)ˡ) | xl ~~> xv] = [∗i in {⟨1, (trm0.trm_seq trm1, 0)⟩}| xl ~~> xv] ∗ [∗i in {⟨0, (default_trm, 10)⟩}| xl ~~> xv] := by
      --   unfold bighstar bighstarDef HStar.hStar instHStarHhProp hhstar
      --     sorry
      -- rw [eq]
      -- have eq : {⟨0, (default_trm, 10)⟩, ⟨1, (trm0.trm_seq trm1, 0)⟩} = (⟪0, {(default_trm, 10)}⟫ ∪ ⟪1, {(trm0.trm_seq trm1, 0)}⟫) := by
      --   unfold labSet; simp; aesop
      -- have eq : xl ~⟨x in ⟪0, ({(default_trm, 10)} : Set (trm × payload)) ⟫⟩~> xv ∗ xl ~⟨x in ⟪1, ({(trm0.trm_seq trm1, 0)} : Set (trm × payload))⟫⟩~> xv =
      --   xl ~⟨x in ⟪0, ({(default_trm, 10), (trm0.trm_seq trm1, 0)} : Set (trm × payload)) ⟫⟩~> xv := by
      --   unfold hhsingle
      yin 0: ywp; ylet; simp [subst, subst.go];
      apply htriple_conseq; apply htriple_get (v := fun _ => xv) ; -- wrong
      stop
      apply htriple_get (v := fun _ => xv);
      apply htriple_frame

      erw [yfocus_lemma 0]
      on_goal 2=> simp; apply disjoint_label_set.mpr; simp
      dsimp
      ystep; ysimp

      stop
      apply ywp_lemma_funs=>//
      intro _; simp;
      stop
      apply hwp_of_hwpgen
      -- yin 1: ywp;
      ystep
    }
  · dsimp
    unfold lang_set2
    have eq :
      (fun hv' =>
      hhstar (fun h : hheap (trm × payload)ˡ =>  ∀ ll ∈ lang_set1, ∃ pp ∈ pay_index1,  h ⟨1, (ll,0)⟩ = h ⟨0, (default_trm,pp) ⟩)
      (fun h : hheap (trm × payload)ˡ =>  ∀ ll ∈ lang_set2, ∃ pp ∈ pay_index2,  h ⟨1, (ll,0)⟩ = h ⟨0, (default_trm,pp) ⟩) )
       ===>
       (fun hv' h : hheap (trm × payload)ˡ => ∀ ll ∈ lang_index, ∃ pp ∈ pay_index, h ⟨1, ll⟩ = h ⟨0, pp⟩):= by
      sorry
    stop
    apply htriple_conseq
    rw [eq]
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

#check Function.partialInv_left
#print bighstar_hhstar_disj
-- #check ystep

lemma hharray_disj (s₁ : Set α) (f : ℤ → val):
  arr⟨s₁⟩(p , x in n =>f x) ∗ arr⟨⋆ \ s₁⟩(p , x in n =>f x) = arr⟨⋆⟩(p , x in n =>f x) :=by
  have tmp : arr⟨⋆⟩(p , x in n =>f x) = arr⟨s₁ ∪ (⋆ \ s₁)⟩(p , x in n =>f x) := by
    congr!
    exact Eq.symm (Set.union_diff_cancel' (fun ⦃a⦄ a ↦ a) fun ⦃a⦄ a ↦ trivial)
  rw [tmp]
  unfold hharrayFun
  apply eq_comm.mpr
  symm
  apply bighstar_hhstar_disj (s₂ := ⋆ \ s₁)=>//
  exact Set.disjoint_sdiff_right

def left_lang_index : Set (trm ⊕ payload):= {l:trm ⊕ payload |
      match l with
      | Sum.inl t => t = [lang| x := x + 1] ∧ cfg1.Generates (expand_trm t)
      | Sum.inr _ => False}

def right_lang_index : Set (trm ⊕ payload):= {l:trm ⊕ payload |
      match l with
      | Sum.inl t => t = [lang| x := x + 2] ∧ cfg1.Generates (expand_trm t)
      | Sum.inr _ => False}

lemma example4_spec_hete (f : ℤ -> val):
  {
    -- ⊤
    -- [∗ in Set.univ | H ] ∗
    arr⟨⋆⟩(xptr , i in 1 =>f i) -- replace it
  }
  [0| Sum.inr| p in pay_index' => prog_c1(⟨f 1⟩, ⟨p.val⟩)]
  [1| Sum.inl| l in lang_index' => ⟦l.val⟧]

  { v,
    fun h => ∀ ll ∈ lang_index', ∃ pp , pp ∈ pay_index' ∧ h ⟨1, Sum.inl ll⟩ = h ⟨0, Sum.inr pp⟩
  } := by
  unfold LGTM.triple
  unfold LGTM.HSHT.mkSHT LGTM.Labeled.map Set.image
  dsimp
  stop
  apply weird_grmdisj_lemma
    (s' := left_lang_index)
    (H := arr⟨⟪0,⋆ ⟫⟩(xptr , i in 1 =>f i))
    (H₁ := arr⟨⟪1,left_lang_index⟫⟩(xptr , i in 1 =>f i))
    (H₂ := arr⟨⟪1,right_lang_index⟫⟩(xptr , i in 1 =>f i))
    (HH := arr⟨⋆⟩(xptr , i in 1 =>f i))
    =>//
  · unfold labSet pay_index; simp_all
  · unfold labSet lang_index lang_index'; simp_all
  · unfold left_lang_index lang_index
    simp_all
  · sorry
  · sorry
  · sorry
  /- left part: goes to false branch-/
  · set pay_s := { p | p<=0 ∧ p ∈ pay_index'}
    set pay_s' : Set (trm ⊕ payload) := (fun p => Sum.inr p) '' pay_s
    set hsub := pay_index' \ pay_s
    set hsub_sum : Set (trm ⊕ payload)ˡ := (fun p => ⟨0, Sum.inr p⟩) '' hsub
    set H₁ := arr⟨hsub_sum⟩(xptr , i in 1 =>f i)
    set H₂ := arr⟨⋆ \ hsub_sum⟩(xptr , i in 1 =>f i)
    have trans_pre : H₁ ∗ H₂ = arr⟨⋆⟩(xptr , i in 1 =>f i) := by
      unfold H₁ H₂
      apply hharray_disj (s₁ := hsub_sum)
      aesop
    rw [← trans_pre]
    apply weird_weaken_lemma (s := pay_index) (s'' := lang_index \ {(Sum.inl [lang| x := x + 1])}) (s' := pay_s') (H₁ := H₁) (H₂ := H₂) =>//
    · unfold labSet pay_index; simp_all
    · unfold pay_index pay_s'
      aesop
    · simp_all
      apply Set.disjoint_iff_inter_eq_empty.mpr
      aesop
    /- left part: solvable using ystep and yif if can do case analysis inside ht -/
    · simp_all; unfold H₁ hsub_sum
      apply ysubst_lemma («σ» := Sum.getRight!)=>//
      sorry
    /- right part: shrink payload to p<=0 -/
    · simp
      sorry
  /- right part: goes to true branch-/
  · set pay_s := { p | p>0 ∧ p ∈ pay_index'}
    set pay_s' : Set (trm ⊕ payload) := (fun p => Sum.inr p) '' pay_s
    set hsub := pay_index' \ pay_s
    set hsub_sum : Set (trm ⊕ payload)ˡ := (fun p => ⟨0, Sum.inr p⟩) '' hsub
    set H₁ := arr⟨hsub_sum⟩(xptr , i in 1 =>f i)
    set H₂ := arr⟨⋆ \ hsub_sum⟩(xptr , i in 1 =>f i)
    have trans_pre : H₁ ∗ H₂ = arr⟨⋆⟩(xptr , i in 1 =>f i) := by
      unfold H₁ H₂
      apply hharray_disj (s₁ := hsub_sum)
      aesop
    rw [← trans_pre]
    apply weird_weaken_lemma (s := pay_index) (s'' := {(Sum.inl [lang| x := x + 1])}) (s' := pay_s') (H₁ := H₁) (H₂ := H₂) =>//
    · unfold labSet pay_index; simp_all
    · unfold pay_index pay_s'
      simp_all
    · simp_all
      apply Set.disjoint_iff_inter_eq_empty.mpr
      aesop
    /- left part: solvable using ystep and yif if can do case analysis inside ht-/
    · unfold H₁ LGTM.wp prog_c1
      simp_all
      -- cases hpi : Function.partialInv (fun x : payloadˡ => ⟨x.lab, Sum.inr x.val⟩) a
      apply weird_index_subst_left
      sorry
    /- right part: shrink p to p>0-/
    · unfold H₂
      sorry

end WeirdLogic
