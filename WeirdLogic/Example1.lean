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


-- -- def SHT_wpmk (label : Set (α ⊕ β)) (i : β) (t : trm) : @SHT (α ⊕ β) :=
-- --   { s := label,
-- --     ht := fun i => [lang|t] }

-- /- (fun $i:ident => [lang|$t]) -/
-- syntax "[" num "| " ident " rin " term " => " lang "]" : sht

-- macro_rules
--   | `(sht| [$n | $i rin $s => $t]) => `(LGTM.SHT.mk ⟪$n, $s⟫ (fun $i:ident => [lang|$t]))


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

def pay_index : Set (trm ⊕ payload) :=
  {p:trm ⊕ payload |
  match p with
    | Sum.inl _ => False
    | Sum.inr _ => True
  }
def lang_index : Set (trm ⊕ payload ):=
  {l:trm ⊕ payload |
    match l with
    | Sum.inl t => cfg1.Generates (expand_trm t)
    | Sum.inr _ => False}

abbrev pay_index' := @Set.univ payload

def lang_index' : Set trm :=
  {l | cfg1.Generates (expand_trm l) }

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

lemma example4_spec_origin(f : ℤ -> val):
  {
    [∗ in Set.univ | H ] ∗ arr⟨⋆⟩(xptr , i in 1 =>f i)
  }
  [0| p in pay_index => prog_c1(⟨val_int (Sum.getRight! p.val)⟩)]
  [1| l in lang_index => ⟦Sum.getLeft! l.val⟧]
  { v,
    fun h => ∀ l ∈ lang_index', ∃ p , h ⟨1, Sum.inl l⟩ = h ⟨0, Sum.inr p⟩
  } := by
  unfold LGTM.triple
  sorry

lemma example4_spec (f : ℤ -> val):
  LGTM.triple
  [{ s := ⟪0, pay_index⟫, ht := fun p ↦ prog_c1.trm_call [(Sum.getRight! p.val)] },
    { s := ⟪1, lang_index⟫, ht := fun l ↦ (Sum.getLeft! l.val) }]
  ( [∗ in Set.univ | H ] ∗ arr⟨⋆⟩(xptr , i in 1 =>f i))
  (fun v => fun h => (∀ l ∈ { ll | Sum.inl l ∈ lang_index}, ∃ p ∈ { pp | Sum.inr pp ∈ pay_index}, h ⟨1, Sum.inl l⟩ = h ⟨0, Sum.inr p⟩))
  := by
  unfold LGTM.triple
  simp_all
  unfold prog_c1
  sorry

abbrev default_payload : payload:= 0
abbrev default_trm : trm := [lang|()]

def pay_idx_prod : Set (trm × payload) :=
  {
    ([lang|()],p) | p ∈ @Set.univ payload
  }
def lang_set : Set trm :=
  {l | cfg1.Generates (expand_trm l)}

def lang_set1 : Set trm :=
  {[lang| x := x + 1]}
def lang_set2 : Set trm :=
  {[lang| x := x + 2]}
def lang_idx_prod : Set (trm × payload ):=
  { (l, 0) | l ∈ lang_set}

lemma example4_spec' (f : ℤ -> val):
  {
    -- [∗ in Set.univ | H ] ∗
    arr⟨⋆⟩(xptr , i in 1 =>f i)
  }
  [0| p in pay_idx_prod => prog_c1(⸨xptr: Loc⸩, ⟨p.val.2⟩)]
  [1| l in lang_idx_prod => ⟦l.val.1⟧]
  { v,
    fun h => ∀ l ∈ lang_idx_prod, ∃ p ∈ pay_idx_prod , h ⟨1, l⟩ = h ⟨0, p⟩
  }
  := by
  unfold LGTM.triple
  apply weird_grmdisj_lemma' (s' := {([lang| x := x + 1],0)}) (s'' := pay_idx_prod) (s := lang_idx_prod)
    (HH := arr⟨{⟨0,p⟩ | p ∈ pay_idx_prod}⟩(xptr , i in 1 =>f i))
    (H₂ := arr⟨{⟨ 1,(l,default_payload)⟩ | l ∈ lang_set2}⟩(xptr , i in 1 =>f i))
    (H₁ := arr⟨{⟨ 1, (l,default_payload)⟩ | l ∈ lang_set1}⟩(xptr , i in 1 =>f i))=>//
  · unfold lang_idx_prod lang_set expand_trm; simp; sorry
  · simp; apply disjoint_label_set.mpr; aesop
  · sorry
  /- left part -/
  · sorry
  /- right part -/
  · sorry

#check Function.partialInv_left
#print bighstar_hhstar_disj
-- #check ystep

lemma hharray_disj (s₁ s₂ : Set α) (f : ℤ → val):
  arr⟨s₁⟩(p , x in n =>f x) ∗ arr⟨⋆ \ s₁⟩(p , x in n =>f x) = arr⟨⋆⟩(p , x in n =>f x) :=by
  sorry

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
  apply weird_grmdisj_lemma
    (s' := left_lang_index) (s := lang_index) (s'' := pay_index)
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
