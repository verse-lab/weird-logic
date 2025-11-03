import WeirdLogic.Wlgtm

open Lean Lean.Expr Lean.Meta Qq
open Elab Command Term Meta Tactic
open Classical trm val prim

local macro "LabType" : term => `(ℕ)

-- open prim val trm

-- lemma arr_union_eq (f : ℤ -> val):
--   s = s₁ ∪ s₂ ->
--   Disjoint s₁ s₂ ->
--   arr⟨s⟩(xptr , i in 1 =>f i) = arr⟨s₁⟩(xptr , i in 1 =>f i) ∗ arr⟨s₂⟩(xptr , i in 1 =>f i) := by
--   move=> unio disj
--   unfold hharrayFun
--   rw [unio]
--   apply eq_comm.mpr
--   apply bighstar_hhstar_disj=>//

#check heap
#check bighstar_hhstar_disj
#check bighstar_hhadd
#check Set.diff_union_of_subset

open EmptyPCM in
lemma bighstar_hhstar_disj_dir
   {hH : α -> hProp} {s₁ s₂ s: Set α} :
    Disjoint s₁ s₂ ->
    s = s₁ ∪ s₂ ->
    [∗ i in s₁ | hH i] ∗ [∗ i in s₂ | hH i] = [∗ i in s | hH i] := by
    move=>dj un ;rw [un]
    srw -hhaddE; apply bighstar_hhadd_disj; exact dj

lemma pair_set_union_right ( p₁ p₂ : Set α ) ( d : β ) :
  p₁ ∩ p₂ = ∅ ->
  {x | ∃ p ∈ p₁, (d, p) = x} ∩ {x | ∃ p ∈ p₂, (d, p) = x} = ∅ := by
  move=> h
  ext x
  simp
  intro p1 hp1 dph1 p2 hp2
  subst dph1
  simp_all only [Prod.mk.injEq, true_and]
  intro heq
  have hmem : p1 ∈ p₁ ∩ p₂ := ⟨hp1, heq ▸ hp2⟩
  rw [h] at hmem
  exact hmem

lemma pair_set_union_index_right (i : ℕ) ( p₁ p₂ : Set α) ( d : β ) :
  p₁ ∩ p₂ = ∅ ->
  {x : (β × α)ˡ | ∃ p ∈ p₁, ⟨i, (d, p)⟩ = x} ∩ {x | ∃ p ∈ p₂, ⟨i,(d, p)⟩ = x} = ∅ := by
  move=> h
  ext x
  simp
  intro p1 hp1 dph1 p2 hp2
  subst dph1
  simp
  intro heq
  have hmem : p1 ∈ p₁ ∩ p₂ := ⟨hp1, heq ▸ hp2⟩
  rw [h] at hmem
  exact hmem

lemma pair_set_union_left ( p₁ p₂ : Set α ) ( d : β ) :
  p₁ ∩ p₂ = ∅ ->
  {x | ∃ p ∈ p₁, (p, d) = x} ∩ {x | ∃ p ∈ p₂, (p, d) = x} = ∅ := by
  move=> h
  ext x
  simp
  intro p1 hp1 dph1 p2 hp2
  subst dph1
  simp_all only [Prod.mk.injEq, and_true]
  intro heq
  have hmem : p1 ∈ p₁ ∩ p₂ := ⟨hp1, heq ▸ hp2⟩
  rw [h] at hmem
  exact hmem

lemma pair_set_union_index_left (i : ℕ) ( p₁ p₂ : Set α) ( d : β ) :
  p₁ ∩ p₂ = ∅ ->
  {x : (α × β)ˡ | ∃ p ∈ p₁, ⟨i, (p, d)⟩ = x} ∩ {x | ∃ p ∈ p₂, ⟨i,(p, d)⟩ = x} = ∅ := by
  move=> h
  ext x
  simp
  intro p1 hp1 dph1 p2 hp2
  subst dph1
  simp
  intro heq
  have hmem : p1 ∈ p₁ ∩ p₂ := ⟨hp1, heq ▸ hp2⟩
  rw [h] at hmem
  exact hmem

lemma pair_set_union_eq_left ( p₁ p₂ p₃ : Set α ) ( d : β ) :
  p₁ ∪ p₂ = p₃ ->
  {x | ∃ p ∈ p₁, (d, p) = x} ∪ {x | ∃ p ∈ p₂, (d, p) = x} = {x | ∃ p ∈ p₃, (d, p) = x} := by
  move=> h
  aesop

lemma pair_set_union_eq_right ( p₁ p₂ p₃ : Set α ) ( d : β ) :
  p₁ ∪ p₂ = p₃ ->
  {x | ∃ p ∈ p₁, (p, d) = x} ∪ {x | ∃ p ∈ p₂, (p, d) = x} = {x | ∃ p ∈ p₃, (p, d) = x} := by
  move=> h
  aesop

lemma pair_set_union_index_eq_left ( p₁ p₂ p₃ : Set α ) ( d : β ) :
  p₁ ∪ p₂ = p₃ ->
  {x : (β × α)ˡ | ∃ p ∈ p₁, ⟨i, (d, p)⟩ = x} ∪ {x | ∃ p ∈ p₂, ⟨i, (d, p)⟩ = x} = {x | ∃ p ∈ p₃, ⟨i, (d, p)⟩ = x} := by
  move=> h
  aesop

lemma pair_set_union_index_eq_right ( p₁ p₂ p₃ : Set α ) ( d : β ) :
  p₁ ∪ p₂ = p₃ ->
  {x : (α × β)ˡ | ∃ p ∈ p₁, ⟨i, (p, d)⟩ = x} ∪ {x | ∃ p ∈ p₂, ⟨i, (p, d)⟩ = x} = {x | ∃ p ∈ p₃, ⟨i, (p, d)⟩ = x} := by
  move=> h
  aesop

lemma pair_insert_disjoin ( p₁ p₂ : Set α) ( a b : α) :
  Disjoint p₁ p₂ ->
  a ≠ b ->
  a ∉ p₂ ->
  b ∉ p₁ ->
  insert a p₁ ∩ insert b p₂ = ∅ := by
  move => dj ne na nb
  ext x
  simp [Set.ext_iff, Set.mem_insert_iff]
  intro h
  constructor
  · aesop
  · intro h2
    by_cases h3 : x = a
    · rw [h3] at h2
      contradiction
    · simp_all only [ne_eq, false_or]
      have contra := Set.disjoint_iff.mp dj
      simp_all only [Set.subset_empty_iff]
      have hx : x ∈ p₁ ∩ p₂ := ⟨h, h2⟩
      rw [contra] at hx
      exact hx

lemma psnd_eq ( d : β) ( s: Set (α × β)):
  (∀ p ∈ s, p.snd = d) ->
  ∀ b a, (a, b) ∈ s → d = b := by
  intro hp b a hba
  specialize hp (a, b) hba
  simp_all

lemma pair_wrap_eq_left {α β : Type} (i : ℕ) (d : β) (s' : Set α) (s : Set (α × β)) :
  (∀ p ∈ s, p.snd = d) ->
  (Prod.fst) '' s = s' ->
  {x : (α × β)ˡ| ∃ p ∈ s, ⟨i, p⟩ = x} = {x | ∃ p ∈ s', ⟨i, (p, d)⟩ = x} := by
  intro p hfst
  ext x
  simp [Set.mem_setOf_eq]
  constructor
  · simp
    intro a b hba hiba
    use a
    constructor
    · aesop
    · have db_eq : d = b := psnd_eq d s p b a hba
      rw [db_eq]
      exact hiba
  · simp
    intro a hs hida
    use a, d
    constructor
    · have ⟨b, hb⟩ : ∃ b, (a, b) ∈ s := by
        rw [← hfst] at hs
        aesop
      have db_eq : d = b := psnd_eq d s p b a hb
      rw [db_eq]
      exact hb
    · exact hida

lemma pfst_eq ( d : β) ( s: Set (β × α)):
  (∀ p ∈ s, p.fst = d) ->
  ∀ b a, (b, a) ∈ s → d = b := by
  intro hp b a hba
  specialize hp (b, a) hba
  simp_all

lemma pair_wrap_eq_right {α β : Type} (i : ℕ) (d : β) (s' : Set α) (s : Set (β × α)) :
  (∀ p ∈ s, p.fst = d )->
  (Prod.snd) '' s = s' ->
  {x : (β × α)ˡ| ∃ p ∈ s, ⟨i, p⟩ = x} = {x | ∃ p ∈ s', ⟨i, (d, p)⟩ = x} := by
  intro p hsnd
  ext x
  simp [Set.mem_setOf_eq]
  constructor
  · simp
    intro b a hba hiba
    use a
    constructor
    · aesop
    · have db_eq : d = b := pfst_eq d s p b a hba
      rw [db_eq]
      exact hiba
  · simp
    intro a hs hida
    use d, a
    constructor
    · have ⟨b, hb⟩ : ∃ b, (b, a) ∈ s := by
        rw [← hsnd] at hs
        aesop
      have db_eq : d = b := pfst_eq d s p b a hb
      rw [db_eq]
      exact hb
    · exact hida

lemma unsimp_singleton_set ( t : trm) ( p : β) :
  {x | ∃ l ∈ ({t} : Set trm), (l, p) = x} = {(t, p)} := by
  simp

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
