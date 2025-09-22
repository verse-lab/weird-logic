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
  fun ⸨a:Val⸩ =>
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

#check Function.partialInv_left
#print bighstar_hhstar_disj
-- #check ystep

lemma hharray_disj (s₁ s₂ : Set α) (f : ℤ → val):
  arr⟨s₁⟩(p , x in n =>f x) ∗ arr⟨⋆ \ s₁⟩(p , x in n =>f x) = arr⟨⋆⟩(p , x in n =>f x) :=by
  sorry

lemma example4_spec_hete (f : ℤ -> val):
  {
    -- ⊤
    -- [∗ in Set.univ | H ] ∗
    arr⟨⋆⟩(xptr , i in 1 =>f i)
  }
  [0| Sum.inr| p in pay_index' => prog_c1(⟨val_int p.val⟩)]
  [1| Sum.inl| l in lang_index' => ⟦l.val⟧]

  { v,
    -- fun h => ∀ ll , ∃ pp , Sum.inl ll ∈ lang_index ∧ Sum.inr pp ∈ pay_index ∧ h ⟨1, Sum.inl ll⟩ = h ⟨0, Sum.inr pp⟩
    fun h => ∀ ll , ll ∈ lang_index' ∧ ∃ pp , pp ∈ pay_index' ∧ h ⟨1, Sum.inl ll⟩ = h ⟨0, Sum.inr pp⟩
  } := by
  unfold LGTM.triple
  unfold LGTM.HSHT.mkSHT LGTM.Labeled.map Set.image
  dsimp
  apply weird_grmdisj_lemma (s' := {(Sum.inl [lang| x := x + 1])}) (s'' := pay_index) (s := lang_index)=>//
  · unfold labSet pay_index; simp_all
  · unfold labSet lang_index lang_index'; simp_all
  · simp_all
    srw Set.disjoint_iff_inter_eq_empty Set.eq_empty_iff_forall_not_mem=>x//==
    aesop
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
      srw Set.disjoint_iff_inter_eq_empty Set.eq_empty_iff_forall_not_mem=>x//==
      aesop
    /- left part:-/
    · simp_all
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
      srw Set.disjoint_iff_inter_eq_empty Set.eq_empty_iff_forall_not_mem=>x//==
      aesop
    /- left part-/
    · unfold H₁ LGTM.wp
      simp_all
      -- cases hpi : Function.partialInv (fun x : payloadˡ => ⟨x.lab, Sum.inr x.val⟩) a
      sorry
    /- right part: shrink p to p>0-/
    · unfold H₂
      sorry


end WeirdLogic
