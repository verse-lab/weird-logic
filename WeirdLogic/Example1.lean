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

def trm1 : trm := [lang| x := x + 1]
def trm2 : trm := [lang| x := x + 2]
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

lang_def prog_c1 :=
  fun ⸨x: Val⸩ ⸨a:Val⸩ =>
    if a > 0 then
      x := x + 1
    else
      x := x + 2

def pay_index' := @Set.univ payload
abbrev lang := List trm

def cfg_expand : Set ( List (Symbol T N)) :=
  {
    [Symbol.terminal [lang| x:=x+1]],[Symbol.terminal [lang| x:=x+2]]
  }
  -- {
  --   c | cfg1.Generates c
  -- }

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
  lang_list_index' = {[[lang| x:=x+1]],[[lang| x:=x+2]]} := by
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
      | cons x xs => simp at h1; unfold trm_to_symbol_list at h1; aesop
    | inr h2 =>
      right
      cases l with
      | nil => aesop
      | cons x xs => simp at h2; unfold trm_to_symbol_list at h2; aesop
  }
  {
    intro h
    induction h with
    | inl h1=> rw [h1]; aesop
    | inr h2=> rw [h2]; aesop
  }

lemma lang_index'_unfold :
  lang_index' = {[lang| x:=x+1],[lang| x:=x+2]} := by
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
  {[lang| x := x + 1]}
def lang_set2 : Set trm :=
  {[lang| x := x + 2]}

lemma arr_union_eq (f : ℤ -> val):
  s = s₁ ∪ s₂ ->
  Disjoint s₁ s₂ ->
  arr⟨s⟩(xptr , i in 1 =>f i) = arr⟨s₁⟩(xptr , i in 1 =>f i) ∗ arr⟨s₂⟩(xptr , i in 1 =>f i) := by
  move=> unio disj
  unfold hharrayFun
  rw [unio]
  apply eq_comm.mpr
  apply bighstar_hhstar_disj=>//

lemma example4_spec (f : ℤ -> val):
  {
    -- [∗ in Set.univ | H ] ∗
    arr⟨{⟨0,p⟩ | p ∈ pay_index}⟩(xptr , i in 1 =>f i) ∗
    arr⟨{⟨1,l⟩ | l ∈ lang_index}⟩(xptr , i in 1 =>f i)
  }
  [0| p in pay_index => prog_c1(⸨xptr: Loc⸩, ⟨p.val.2⟩)]
  [1| l in lang_index => ⟦l.val.1⟧]
  { v,
    fun h => ∀ l ∈ lang_index, ∃ p ∈ pay_index , h ⟨1, l⟩ = h ⟨0, p⟩
  }
  := by
  unfold LGTM.triple
  rw [hhstar_comm]
  rw [arr_union_eq (s₁ := {⟨ 1,(l,default_payload)⟩ | l ∈ lang_set1}) (s₂ := {⟨ 1, (l,default_payload)⟩ | l ∈ lang_set2}) ]
  rotate_left
  {
    unfold lang_index default_payload lang_set1 lang_set2
    rw [lang_index'_unfold]
    aesop
  }
  { apply disjoint_iff.mpr
    unfold lang_set1 lang_set2
    aesop
   }
  rw [hhstar_comm]
  apply weird_grmdisj_lemma' (s' := {([lang| x := x + 2],0)}) (s'' := pay_index) (s := lang_index)
    (HH := arr⟨{⟨0,p⟩ | p ∈ pay_index}⟩(xptr , i in 1 =>f i))
    (H₂ := arr⟨{⟨ 1,(l,default_payload)⟩ | l ∈ lang_set2}⟩(xptr , i in 1 =>f i))
    (H₁ := arr⟨{⟨ 1, (l,default_payload)⟩ | l ∈ lang_set1}⟩(xptr , i in 1 =>f i))=>//
  · unfold lang_index
    rw [lang_index'_unfold]
    aesop
  · simp; apply disjoint_label_set.mpr; aesop
  /- left part -/
  · rw [arr_union_eq (s₁ := {⟨0,(default_trm,p)⟩ | p ∈ pay_index1}) (s₂ := {⟨0,(default_trm,p)⟩ | p ∈ pay_index2})]
    rotate_left
    { unfold pay_index pay_index' pay_index1 pay_index2 default_trm pay_index'
      simp
      ext x
      constructor
      · intro ⟨a, ha⟩
        by_cases h : 0 < a
        · left
          use a
        · right
          use a
          exact ⟨le_of_not_gt h, ha⟩
      · intro hx
        cases hx with
        | inl h₁ => aesop
        | inr h₂ => aesop
        }
    {
      apply disjoint_iff.mpr
      simp
      unfold pay_index1 pay_index2 pay_index'
      ext x
      constructor
      · intro ⟨⟨p₁, hp₁_mem, hx₁⟩, ⟨p₂, hp₂_mem, hx₂⟩⟩
        have : p₁ = p₂ := by
          injection (hx₁.trans hx₂.symm)
          aesop
        subst this
        have hcontr : ¬ (p₁ > 0 ∧ p₁ ≤ 0) := by
          intro h
          exact not_lt_of_ge h.2 h.1
        exact hcontr ⟨hp₁_mem.1, hp₂_mem.1⟩
      · intro h
        cases h
    }
    rw [hhstar_assoc]
    apply weird_weaken_lemma' (s' := {(default_trm,p) | p ∈ pay_index1}) (s := pay_index)
      (H₁ := arr⟨{⟨0,(default_trm,p)⟩ | p ∈ pay_index1}⟩(xptr , i in 1 =>f i))=>//
    · unfold pay_index1 pay_index' pay_index pay_index'
      simp
    · apply disjoint_label_set.mpr; simp
    · /- part 1: sht_prog only -/
      unfold pay_index1 pay_index' pay_index pay_index'
      simp
      sorry
    · /- part 2: if-true case -/
      have simp_lang : lang_index \ {([lang| x := x + 2],0)} = {([lang| x:=x+1],0)} := by
        unfold lang_index
        rw [lang_index'_unfold]
        aesop
      rw [simp_lang]
      apply weird_lang_lemma'=>//
      { simp; apply disjoint_label_set.mpr; aesop }
      apply weird_payload_lemma' (pr := (default_trm, 10))=>//
      { simp; apply disjoint_label_set.mpr; aesop }
      simp
      -- rw [← weird_fix_lang]
      sorry
  /- right part -/
  · sorry

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
    arr⟨⋆⟩(xptr , i in 1 =>f i)
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
