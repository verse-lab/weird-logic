import WeirdLogic.Gram
import WeirdLogic.WTriple
import WeirdLogic.WUtil
-- import WeirdLogic.Util

import Lgtm.Common.Util

open Lean Lean.Expr Lean.Meta Qq
open Elab Command Term Meta Tactic
open Classical trm val prim

local macro "LabType" : term => `(ℕ)

/- ********************************** Rules ************************************** -/

#check LGTM.wp
#check FindLabel
#check yfocus_set_lemma

#check hhimpl_hhforall_r

lemma hheap_weaken (α β: Type) (i j : ℕ) (h : hheap (Labeled (α ⊕ β))) (P P₁ : Set (α ⊕ β)) (ll : α) (hsub : P₁ ⊆ P):
  (∃ p, Sum.inr p ∈ P₁ ∧ h ⟨j, Sum.inl ll ⟩= h ⟨i, Sum.inr p⟩) → ∃ p, Sum.inr p ∈ P ∧ h ⟨j, Sum.inl ll ⟩= h ⟨i, Sum.inr p⟩ := by
  aesop

lemma hheap_weaken_forall (α β: Type) (i j : ℕ) (h : hheap (Labeled (α ⊕ β))) (P P₁ : Set (α ⊕ β)) (l : Set α) (hsub : P₁ ⊆ P):
  (∀ ll ∈ l, ∃ p, Sum.inr p ∈ P₁ ∧ h ⟨j, Sum.inl ll ⟩= h ⟨i, Sum.inr p⟩) → ∀ ll ∈ l, ∃ p, Sum.inr p ∈ P ∧ h ⟨j, Sum.inl ll ⟩= h ⟨i, Sum.inr p⟩ := by
  intro hle l
  move=> hl
  apply hheap_weaken
  exact hsub
  simp_all only

lemma hheap_exists_superset (h : hheap (Labeled α )) (P P₁: Set α ):
  P₁ ⊆ P ->
  (∃ p ∈ P₁, h ⟨j, l⟩ = h ⟨i, p⟩ )->
  ∃ p ∈ P, h ⟨j, l⟩ = h ⟨i, p⟩ := by
  move=> sub h1
  rcases h1 with ⟨p1, hp1, hp2⟩
  use p1
  aesop

lemma hheap_weaken_forall' (α : Type) (i j : ℕ) (h : hheap (Labeled α )) (P P₁ L: Set α ) (hsub : P₁ ⊆ P):
  (∀ ll ∈ L, ∃ p ∈ P₁, h ⟨j, ll ⟩= h ⟨i, p⟩) → ∀ ll ∈ L, ∃ p ∈ P, h ⟨j, ll ⟩= h ⟨i, p⟩ := by
  intro hle l
  move=> hl
  specialize hle l hl
  aesop

#check Unary.wp_conseq

lemma weird_weaken_mid_post_lemma (i j : ℕ) (s' s s'': Set (α ⊕ β)) (sht_prog sht_lang : LGTM.SHT):
  sht_prog.s = ⟪i, s⟫ ->
  sht_lang.s = ⟪ j, s''⟫ ->
  s' ⊆ s -> Disjoint sht_prog.s sht_lang.s ->
  LGTM.wp [sht_prog, sht_lang] (fun _ h => ∀ ll ∈ {l | Sum.inl l ∈ s''}, ∃ pp, Sum.inr pp ∈ s' ∧ h ⟨j, Sum.inl ll ⟩= h ⟨i, Sum.inr pp⟩)
  ==> LGTM.wp [sht_prog, sht_lang] (fun _ h => ∀ ll ∈ {l | Sum.inl l ∈ s''}, ∃ pp, Sum.inr pp ∈ s ∧ h ⟨j, Sum.inl ll ⟩= h ⟨i, Sum.inr pp⟩) := by
  move=> _ _ subst *
  apply weird_wp_conseq
  intro x h
  simp
  intro w
  apply hheap_weaken_forall
  · aesop
  · intro ll'
    specialize w ll'
    intro hll
    have h₁ : Sum.inl ll' ∈ s'' := hll
    specialize w h₁
    aesop

lemma weird_weaken_mid_post_lemma' (α : Type) (i j : ℕ) (s' s s'': Set α) (sht_prog sht_lang : LGTM.SHT):
  sht_prog.s = ⟪i, s⟫ ->
  sht_lang.s = ⟪ j, s''⟫ ->
  s' ⊆ s -> Disjoint sht_prog.s sht_lang.s ->
  LGTM.wp [sht_prog, sht_lang] (fun _ h => ∀ ll ∈ s'', ∃ pp ∈ s', h ⟨j, ll ⟩= h ⟨i, pp⟩)
  ==> LGTM.wp [sht_prog, sht_lang] (fun _ h => ∀ ll ∈ s'', ∃ pp ∈ s, h ⟨j, ll ⟩= h ⟨i, pp⟩) := by
  move=> _ _ subst *
  apply weird_wp_conseq
  intro x h
  intro w
  apply hheap_weaken_forall'=>//

lemma lang_singleton_forall_eq (i j : ℕ) (s s': Set α ) (l : α ) (h : hheap αˡ ):
  s = {l} ->
  ∀ ll ∈ s, ∃ pp ∈ s', h ⟨j, ll ⟩= h ⟨i, pp⟩ =
  ∃ pp ∈ s', h ⟨j, l ⟩= h ⟨i, pp⟩ := by
  move=>single
  aesop

#check heval_nonrel
#print bighstarDef
#check hhstar
#print hheap
#check Set.mem_singleton_iff

lemma weird_heap_sub_left (i j : ℕ) (Q : hhProp (α ⊕ β)ˡ) (s s' s'': Set (α ⊕ β)) :
  i ≠ j ->
  hhlocal (⟪i, s⟫ \ ⟪i, s'⟫ ) Q ->
  hhstar Q
  (fun h => ∀ ll ∈ {l | Sum.inl l ∈ s''}, ∃ pp,
    Sum.inr pp ∈ s' ∧ h ⟨j, Sum.inl ll ⟩= h ⟨i, Sum.inr pp⟩)
  ==>
  (fun h => ∀ ll ∈ {l | Sum.inl l ∈ s''}, ∃ pp,
    Sum.inr pp ∈ s' ∧ h ⟨j, Sum.inl ll ⟩= h ⟨i, Sum.inr pp⟩)  := by
  unfold hhstar hhlocal hlocal
  intro ij hl
  move=> hh hs
  rcases hs with ⟨ hh1, hh2, ⟨ hs1,hs2,hs3, hs4 ⟩ ⟩
  subst hh
  simp
  specialize hl _ hs1
  intro ll lin
  rw [hl]
  · simp at hs2
    specialize hs2 ll lin
    rcases hs2 with ⟨pp, hs21, hs22⟩
    exists pp
    rw [hl]
    simp_all
    simp
    aesop
  · aesop

lemma weird_heap_sub_right (i j : ℕ) (Q : hhProp (α ⊕ β)ˡ) (s s' s'': Set (α ⊕ β)) :
  i ≠ j ->
  hhlocal (⟪i, s⟫ \ ⟪i, s'⟫ ) Q ->
  hhstar (fun h => ∀ ll ∈ {l | Sum.inl l ∈ s''}, ∃ pp,
    Sum.inr pp ∈ s' ∧ h ⟨j, Sum.inl ll ⟩= h ⟨i, Sum.inr pp⟩) Q
  ==>
  (fun h => ∀ ll ∈ {l | Sum.inl l ∈ s''}, ∃ pp,
    Sum.inr pp ∈ s' ∧ h ⟨j, Sum.inl ll ⟩= h ⟨i, Sum.inr pp⟩)  := by
  unfold hhstar hhlocal hlocal
  intro ij hl
  move=> hh hs
  rcases hs with ⟨ hh1, hh2, ⟨ hs1,hs2,hs3, hs4 ⟩ ⟩
  subst hh
  simp
  specialize hl _ hs2
  intro ll lin
  rw [hl]
  · simp at hs1
    specialize hs1 ll lin
    rcases hs1 with ⟨pp, hs11, hs12⟩
    exists pp
    rw [hl]
    simp_all
    simp
    aesop
  · aesop

lemma weird_heap_sub_right' (i j : ℕ) (Q : hhProp αˡ) (s s' s'': Set α) :
  i ≠ j ->
  hhlocal (⟪i, s⟫ \ ⟪i, s'⟫ ) Q ->
  hhstar (fun h => ∀ ll ∈ {l | l ∈ s''}, ∃ pp,
     pp ∈ s' ∧ h ⟨j, ll ⟩= h ⟨i, pp⟩) Q
  ==>
  (fun h => ∀ ll ∈ {l |  l ∈ s''}, ∃ pp,
    pp ∈ s' ∧ h ⟨j, ll ⟩= h ⟨i, pp⟩)  := by
  unfold hhstar hhlocal hlocal
  intro ij hl
  move=> hh hs
  rcases hs with ⟨ hh1, hh2, ⟨ hs1,hs2,hs3, hs4 ⟩ ⟩
  subst hh
  simp
  specialize hl _ hs2
  intro ll lin
  rw [hl]
  · simp at hs1
    specialize hs1 ll lin
    rcases hs1 with ⟨pp, hs11, hs12⟩
    exists pp
    rw [hl]
    simp_all
    simp
    aesop
  · aesop

lemma weird_heap_sub_right_fix_lang' (i j : ℕ) (Q : hhProp αˡ) (s s': Set α) :
  i ≠ j ->
  hhlocal (⟪i, s⟫ \ ⟪i, s'⟫ ) Q ->
  hhstar (fun h => ∃ pp,
     pp ∈ s' ∧ h ⟨j, ll ⟩= h ⟨i, pp⟩) Q
  ==>
  (fun h => ∃ pp,
    pp ∈ s' ∧ h ⟨j, ll ⟩= h ⟨i, pp⟩)  := by
  unfold hhstar hhlocal hlocal
  intro ij hl
  move=> hh hs
  rcases hs with ⟨ hh1, hh2, ⟨ hs1,hs2,hs3, hs4 ⟩ ⟩
  subst hh
  simp
  specialize hl _ hs2
  rw [hl]
  · rcases hs1 with ⟨pp, hs11, hs12⟩
    exists pp
    rw [hl]
    simp_all
    simp
    aesop
  · aesop

lemma weird_heap_sub_left' (i j : ℕ) (Q : hhProp αˡ) (s s' s1 s'1: Set α) :
  i ≠ j ->
  hhlocal ((⟪i, s⟫ \ ⟪i, s1⟫ ) ∪ (⟪j, s'⟫ \ ⟪j, s'1⟫ )) Q ->
  (fun h => ∀ ll ∈ {l |  l ∈ s1}, ∃ pp,
    pp ∈ s'1 ∧ h ⟨j, ll ⟩= h ⟨i, pp⟩) ==>
  hhstar (fun h => ∀ ll ∈ {l | l ∈ s1}, ∃ pp,
     pp ∈ s'1 ∧ h ⟨j, ll ⟩= h ⟨i, pp⟩) Q
   := by
   stop
  unfold hhstar hhlocal hlocal
  intro ij hl
  move=> hh hs
  rcases hs with ⟨ hh1, hh2, ⟨ hs1,hs2,hs3, hs4 ⟩ ⟩
  subst hh
  simp
  specialize hl _ hs2
  intro ll lin
  rw [hl]
  · simp at hs1
    specialize hs1 ll lin
    rcases hs1 with ⟨pp, hs11, hs12⟩
    exists pp
    rw [hl]
    simp_all
    simp
    aesop
  · aesop

#check hhprop_disjoint_comm

lemma swap_hqstar  (H' : @hval α → @hhProp α) (H₂ H : @hhProp α):
  H' = (fun _ => H ) ->
  hqstar H' H₂ = fun _ ↦ hhstar H₂ H := by
  unfold hqstar hhstar
  dsimp only [HStar.hStar]
  unfold hhstar
  move=> hh
  simp
  ext x h
  constructor
  move=> hl
  rcases hl with ⟨hlh, ⟨ hlb1,hlb2,⟨ hlb3, hlb4, hlb5⟩ ⟩ ⟩
  · use hlb2
    constructor=>//
    use hlh
    constructor=>//
    constructor
    · rw [hlb4]; apply hunion_comm_of_hdisjoint; unfold hdisjoint; exact hlb5
    · intro a
      apply Finmap.Disjoint.symm
      apply hlb5
  · rcases hl with ⟨hlh, ⟨ hlb1,hlb2,⟨ hlb3, hlb4, hlb5⟩ ⟩ ⟩
    substs H'
    simp
    use hlb2
    constructor=>//
    use hlh
    constructor=>//
    constructor=>//
    · rw [hlb4]; apply hunion_comm_of_hdisjoint; unfold hdisjoint; exact hlb5
    · intro a
      apply Finmap.Disjoint.symm
      apply hlb5

/- ********************************** Weaken Rule ************************************** -/

/- s' is the part to keep (P' in weaken rule) -/
lemma weird_weaken_lemma  (s' s s'': Set (α ⊕ β)) (sht_prog sht_lang : LGTM.SHT):
  sht_prog.s = ⟪0, s⟫ ->
  sht_lang.s = ⟪1, s''⟫ ->
  s' ⊆ s -> Disjoint sht_prog.s sht_lang.s ->
  H₁ ==> LGTM.wp [⟨⟪0, s \ s'⟫, sht_prog.ht⟩] (fun _ => fun h ↦ ∀ a ∉ ⟪0, s \ s'⟫, h a = ∅ ) ->
  H₂ ==> LGTM.wp [⟨⟪0, s'⟫, sht_prog.ht⟩, sht_lang]
    (fun _ h => ∀ ll ∈ {l | Sum.inl l ∈ s''}, ∃ pp, Sum.inr pp ∈ s' ∧ h ⟨1, Sum.inl ll ⟩= h ⟨0, Sum.inr pp⟩) ->
  H₁ ∗ H₂ ==> LGTM.wp [sht_prog, sht_lang]
  (fun _ h => ∀ ll ∈ {l | Sum.inl l ∈ s''}, ∃ pp, Sum.inr pp ∈ s ∧ h ⟨1, Sum.inl ll ⟩= h ⟨0, Sum.inr pp⟩) := by
  move=> prog lang subs disj part1 part2
  intro h12
  move=> H12
  apply weird_weaken_mid_post_lemma=>//
  set Qp1 : hval (α ⊕ β)ˡ → hhProp (α ⊕ β)ˡ:= fun _ => (fun h ↦ ∀ ll ∈ {l | Sum.inl l ∈ s''}, ∃ pp, Sum.inr pp ∈ s' ∧ h ⟨1, Sum.inl ll⟩ = h ⟨0, Sum.inr pp⟩)
  set B : hhProp (α ⊕ β)ˡ:= fun h ↦ ∀ a ∉ ⟪0, s \ s'⟫, h a = ∅
  set B' : hval (α ⊕ β)ˡ → hhProp (α ⊕ β)ˡ:= fun _ => B
  apply weird_wp_conseq (Q1 := whqstar Qp1 B)
  · unfold whqstar B Qp1
    intro x
    simp
    move=> hc hcon
    apply weird_heap_sub_right (s := s) (s'' := s'') (Q := B)=>//
    · unfold hhlocal hlocal B
      intro h
      dsimp
      aesop
    · unfold B
      simp_all
  apply well_formed_focus_lemma (idx := 0) (l := 0) (shts := [sht_prog, sht_lang]) (s' := s') (s := s) (H := B' ∗ H₂) (R := H₁ ∗ H₂) (Q := Qp1 ∗ B)=>//
  · simp_all; apply disjoint_label_set.mpr; aesop
  · have part11 := (hhimpl_frame_l (hH₃ := H₂) (hH₁ := H₁) (hH₂ := LGTM.wp [{ s := ⟪0, s \ s'⟫, ht := sht_prog.ht }] B'))
    specialize part11 part1
    simp
    apply hhimpl_trans (h₁ := H₁ ∗ H₂ ) ( h₂ := ((LGTM.wp [{ s := ⟪0, s \ s'⟫, ht := sht_prog.ht }] B') ∗ H₂)) (h₃ := LGTM.wp [{ s := ⟪0, s \ s'⟫, ht := sht_prog.ht }] (B' ∗ H₂))
    · exact part11
    · have form1 := LGTM.wp_frame (Q := B') (H := H₂) (sht := [{ s := ⟪0, s \ s'⟫, ht := sht_prog.ht }])
      convert form1
  intro x
  have part21 := (hhimpl_frame_l (hH₃ := B) (hH₁ := H₂) (hH₂ := LGTM.wp [{ s := ⟪0, s'⟫, ht := sht_prog.ht }, sht_lang] Qp1))
  specialize part21 part2
  simp
  unfold B'
  rw [hhstar_comm]
  apply hhimpl_trans (h₁ := H₂ ∗ B) ( h₂ := LGTM.wp [{ s := ⟪0, s'⟫, ht := sht_prog.ht }, sht_lang] Qp1 ∗ B) (h₃ := LGTM.wp [{ s := ⟪0, s ∩ s'⟫, ht := sht_prog.ht }, sht_lang] (Qp1 ∗ B))
  · exact part21
  · have form2 := LGTM.wp_frame ( Q := Qp1) (H := B) (sht := [{ s := ⟪0, s'⟫, ht := sht_prog.ht }, sht_lang])
    convert form2
    aesop

/- Prod version: s' is the part to keep (P' in weaken rule) -/
lemma weird_weaken_lemma' (s' s s'': Set α) (sht_prog sht_lang : LGTM.SHT):
  sht_prog.s = ⟪0, s⟫ ->
  sht_lang.s = ⟪1, s''⟫ ->
  s' ⊆ s -> Disjoint sht_prog.s sht_lang.s ->
  H₁ ==> LGTM.wp [⟨⟪0, s \ s'⟫, sht_prog.ht⟩] (fun _ => fun h ↦ ∀ a ∉ ⟪0, s \ s'⟫, h a = ∅ ) ->
  H₂ ==> LGTM.wp [⟨⟪0, s'⟫, sht_prog.ht⟩, sht_lang]
    (fun _ h => ∀ ll ∈ s'', ∃ pp ∈ s', h ⟨1,ll⟩= h ⟨0, pp⟩ ) ->
  H₁ ∗ H₂ ==> LGTM.wp [sht_prog, sht_lang]
  (fun _ h => ∀ ll ∈ s'', ∃ pp ∈ s, h ⟨1, ll ⟩= h ⟨0, pp⟩) := by
  move=> prog lang subs disj part1 part2
  intro h12
  move=> H12
  apply weird_weaken_mid_post_lemma'=>//
  set Qp1 : hval αˡ → hhProp αˡ:= fun _ => (fun h ↦ ∀ ll ∈ s'', ∃ pp ∈ s', h ⟨1, ll⟩ = h ⟨0, pp⟩)
  set B : hhProp αˡ:= fun h ↦ ∀ a ∉ ⟪0, s \ s'⟫, h a = ∅
  set B' : hval αˡ → hhProp αˡ:= fun _ => B
  apply weird_wp_conseq (Q1 := whqstar Qp1 B)
  · unfold whqstar B Qp1
    intro x
    simp
    move=> hc hcon
    apply weird_heap_sub_right' (s := s) (s'' := s'') (Q := B)=>//
    · unfold hhlocal hlocal B
      intro h
      dsimp
      aesop
    · unfold B
      simp_all
  apply well_formed_focus_lemma (idx := 0) (l := 0) (shts := [sht_prog, sht_lang]) (s' := s') (s := s) (H := B' ∗ H₂) (R := H₁ ∗ H₂) (Q := Qp1 ∗ B)=>//
  · simp_all; apply disjoint_label_set.mpr; aesop
  · have part11 := (hhimpl_frame_l (hH₃ := H₂) (hH₁ := H₁) (hH₂ := LGTM.wp [{ s := ⟪0, s \ s'⟫, ht := sht_prog.ht }] B'))
    specialize part11 part1
    simp
    apply hhimpl_trans (h₁ := H₁ ∗ H₂ ) ( h₂ := ((LGTM.wp [{ s := ⟪0, s \ s'⟫, ht := sht_prog.ht }] B') ∗ H₂)) (h₃ := LGTM.wp [{ s := ⟪0, s \ s'⟫, ht := sht_prog.ht }] (B' ∗ H₂))
    · exact part11
    · have form1 := LGTM.wp_frame (Q := B') (H := H₂) (sht := [{ s := ⟪0, s \ s'⟫, ht := sht_prog.ht }])
      convert form1
  intro x
  have part21 := (hhimpl_frame_l (hH₃ := B) (hH₁ := H₂) (hH₂ := LGTM.wp [{ s := ⟪0, s'⟫, ht := sht_prog.ht }, sht_lang] Qp1))
  specialize part21 part2
  simp
  unfold B'
  rw [hhstar_comm]
  apply hhimpl_trans (h₁ := H₂ ∗ B) ( h₂ := LGTM.wp [{ s := ⟪0, s'⟫, ht := sht_prog.ht }, sht_lang] Qp1 ∗ B) (h₃ := LGTM.wp [{ s := ⟪0, s ∩ s'⟫, ht := sht_prog.ht }, sht_lang] (Qp1 ∗ B))
  · exact part21
  · have form2 := LGTM.wp_frame ( Q := Qp1) (H := B) (sht := [{ s := ⟪0, s'⟫, ht := sht_prog.ht }, sht_lang])
    convert form2
    aesop

#check hwp_union
#check LGTM.wp_cons
#check eval_conseq

lemma htrm_subset_eq (l : ℕ) (s s' : Set α) ( t: htrm αˡ ) (sht_lang sht_lang': LGTM.SHT) (x: αˡ):
  s' ⊆ s ->
  sht_lang'.s = ⟪l, s'⟫ ->
  sht_lang.s = ⟪l, s⟫->
  sht_lang.ht x = sht_lang'.ht x := by
  move=> sub s1 s2
  sorry

lemma weird_strengthen_lang' (s : Set (α ⊕ β)) (sht_prog sht_lang sht_lang': LGTM.SHT) :
  sht_prog.s = ⟪0, s''⟫ ->
  sht_lang'.s = ⟪1, s'⟫ ->
  sht_lang.s = ⟪1, s⟫ ->
  s' ⊆ s ->
  LGTM.wp [sht_prog, sht_lang] (fun _ h => ∀ ll ∈ {l | Sum.inl l ∈ s},  ∃ pp, Sum.inr pp ∈ s'' ∧ h ⟨1, Sum.inl ll ⟩= h ⟨0, Sum.inr pp⟩)
  ==> LGTM.wp [sht_prog, sht_lang'] (fun _ h => ∀ ll ∈ {l | Sum.inl l ∈ s'},  ∃ pp, Sum.inr pp ∈ s'' ∧ h ⟨1, Sum.inl ll ⟩= h ⟨0, Sum.inr pp⟩)
  --  ∗ ∀ a ∈ ⟪1, s \ s'⟫,

  := by
  sorry

#check hwp_conseq
#check yfocus_set_lemma_eq
#check yunfocus_lemma

/- Lang Strengthen Rule
Intuition: If the triple holds in a larger set L (<1,s>), then it must hold in a smaller set L' (<1,s'>).
-/
lemma weird_strengthen_lang (s : Set (α ⊕ β)) (sht_prog sht_lang sht_lang': LGTM.SHT) :
  sht_prog.s = ⟪0, s''⟫ ->
  sht_lang'.s = ⟪1, s'⟫ ->
  sht_lang.s = ⟪1, s⟫ ->
  s' ⊆ s ->
  LGTM.wp [sht_prog, sht_lang] (fun _ h => ∀ ll ∈ {l | Sum.inl l ∈ s},  ∃ pp, Sum.inr pp ∈ s'' ∧ h ⟨1, Sum.inl ll ⟩= h ⟨0, Sum.inr pp⟩)
  ==> LGTM.wp [sht_prog, sht_lang'] (fun _ h => ∀ ll ∈ {l | Sum.inl l ∈ s'},  ∃ pp, Sum.inr pp ∈ s'' ∧ h ⟨1, Sum.inl ll ⟩= h ⟨0, Sum.inr pp⟩) := by
  move=> prog lang lang' subset
  unfold hhimpl
  intro hh
  have hh1 := hh ∪_⟪1, s'⟫ hh
  move=> pre
  have shtt : (List.insertIdx 0 { s := ⟪0, s''⟫, ht := sht_prog.ht } [sht_lang]) = [sht_prog, sht_lang] := by simp; rw [← prog]
  rw [← shtt] at pre
  rw [← yunfocus_lemma (shts:= [sht_lang]) (idx:= 0) (l:= 0) (s:= s'') (ht:= sht_prog.ht)
    (Q' := (fun _ _ h => ∀ ll ∈ {l | Sum.inl l ∈ s},  ∃ pp, Sum.inr pp ∈ s'' ∧ h ⟨1, Sum.inl ll ⟩= h ⟨0, Sum.inr pp⟩))
    (Q := (fun _ h => ∀ ll ∈ {l | Sum.inl l ∈ s},  ∃ pp, Sum.inr pp ∈ s'' ∧ h ⟨1, Sum.inl ll ⟩= h ⟨0, Sum.inr pp⟩))] at pre =>//
  rotate_left
  { simp; rw [lang']; apply disjoint_label_set.mpr; aesop }
  have shtt' : (List.insertIdx 0 { s := ⟪0, s''⟫, ht := sht_prog.ht } [sht_lang']) = [sht_prog, sht_lang'] := by simp; rw [← prog]
  rw [← shtt']
  rw [← yunfocus_lemma (shts:= [sht_lang']) (idx:= 0) (l:= 0) (s:= s'') (ht:= sht_prog.ht)
    (Q' := (fun _ _ h => ∀ ll ∈ {l | Sum.inl l ∈ s'},  ∃ pp, Sum.inr pp ∈ s'' ∧ h ⟨1, Sum.inl ll ⟩= h ⟨0, Sum.inr pp⟩))
    (Q := (fun _ h => ∀ ll ∈ {l | Sum.inl l ∈ s'},  ∃ pp, Sum.inr pp ∈ s'' ∧ h ⟨1, Sum.inl ll ⟩= h ⟨0, Sum.inr pp⟩))]=>//
  rotate_left
  { simp; rw [lang]; apply disjoint_label_set.mpr; aesop }
  revert pre
  apply hwp_conseq=> hv;
  rw [← yfocus_set_lemma_eq (shts:= [sht_lang]) (l:= 1) (s' := s \ s') (s := s)
    (Q := (fun _ h => ∀ ll ∈ {l | Sum.inl l ∈ s},  ∃ pp, Sum.inr pp ∈ s'' ∧ h ⟨1, Sum.inl ll ⟩= h ⟨0, Sum.inr pp⟩))]=>//
  unfold LGTM.wp
  simp
  -- rw [lang]
  have eq1 : ⟪1, s ∩ s'⟫ = ⟪1, s'⟫ := by aesop
  rw [eq1, lang]
  -- rw [hwp_ht_eq (ht₁ := (sht_lang'.ht ∪_⟪1, s'⟫fun x ↦ [lang| ()])) (ht₂ := sht_lang.ht)]
  -- · apply hwp_conseq=> hv1/=
  --   -- rw [hwp_ht_eq (ht₁ := (sht_lang.ht ∪_⟪1, s ∩ (s \ s')⟫fun x ↦ [lang| ()])) (ht₂ := sht_lang.ht)]
  --   sorry
  · sorry
  · sorry
  -- hwp heval heval_nonrel bighstarDef hhimpl hhexists
  -- intro hq la lb
  -- set hq' : (α ⊕ β)ˡ → val → heap → Prop := fun a v=> if a.lab = 0 ∧ a.val ∈ s'' ∨ a.lab = 1 ∧ a.val ∈ s' then hq a v else hq a v
  -- use hq
  -- constructor
  -- · intro laa
  --   specialize la laa
  --   move=> lpre
  --   cases lpre with
  --   | inl h =>
  --     simp [h]
  --     simp [h] at la
  --     -- unfold hq
  --     -- simp [h]
  --     exact la
  --   | inr h =>
  --     simp [h]
  --     have h' : laa.lab = 1 ∧ laa.val ∈ s := by
  --       rcases h with ⟨hl, hr ⟩
  --       constructor
  --       {exact hl}
  --       {apply subset; exact hr}
  --     simp [h'] at la
  --     have h'' : sht_lang.ht laa = sht_lang'.ht laa := by
  --       apply htrm_subset_eq=>//
  --     simp [h''] at la
  --     -- unfold hq'
  --     -- simp [h]
  --     exact la
  -- · intro hv2 hh2
  --   specialize lb hv2 hh2
  --   move=> pre2
  --   have lbp' : (∀ (a : (α ⊕ β)ˡ), if a.lab = 0 ∧ a.val ∈ s'' ∨ a.lab = 1 ∧ a.val ∈ s then hq a (hv2 a) (hh2 a) else hh2 a = hh a) := by
  --     intro a
  --     by_cases h: a.lab = 0 ∧ a.val ∈ s'' ∨ a.lab = 1 ∧ a.val ∈ s'
  --     · rcases h with ⟨h1, h2⟩|⟨h3, h4⟩
  --       · specialize pre2 a
  --         -- unfold hq' at pre2
  --         scase_if=>//
  --       · specialize pre2 a
  --         -- unfold hq' at pre2
  --         scase_if=>//
  --         simp
  --         move=> hh1 hh2
  --         specialize hh2 h3
  --         have h_in_s : a.val ∈ s := subset h4
  --         contradiction
  --     · rw [not_or] at h
  --       rcases h with ⟨h1,h2⟩
  --       scase_if
  --       all_goals move=> hp
  --       rcases hp with hhh1 | hh2
  --       · contradiction
  --       · rw [not_and] at h2
  --         rcases hh2 with ⟨hhh1,hhh2⟩
  --         specialize h2 hhh1
  --         have cond : a.lab = 0 ∧ a.val ∈ s'' ∨ a.lab = 1 ∧ a.val ∈ s := by
  --           right; exact ⟨hhh1, hhh2⟩
  --         specialize la a cond
  --         sorry

  --       · specialize pre2 a
  --         rw [not_or] at hp
  --         have hcond : ¬ (a.lab = 0 ∧ a.val ∈ s'' ∨ a.lab = 1 ∧ a.val ∈ s') := by
  --           rw [not_or]
  --           constructor=>//
  --         rw [if_neg hcond] at pre2
  --         exact pre2
  --   specialize lb lbp'
  --   intro ll
  --   move=> ll1
  --   apply subset at ll1
  --   specialize lb ll ll1
  --   exact lb

/- ********************************** GrmDisj Rule ************************************** -/

/- Another format of Grmdisj rule using product type-/
#check Finmap.lookup_union_left_of_not_in

lemma union_heap_eq (h h1 h2 : hheap α ) :
  h = h1 ∪ h2 ->
  (∀ (a : α), Finmap.Disjoint (h1 a) (h2 a)) ->
  h1 x = h1 y ->
  h2 x = h2 y ->
  h x = h y := by
  move=> un dj pre1 pre2
  rw [un]
  aesop

#check hhlocal

set_option maxHeartbeats 1600000 in
lemma weird_grmdisj_lemma_safe_clean (s' s : Set (α × β)) (sht_prog sht_lang : LGTM.SHT) :
  sht_prog.s = ⟪0, s'⟫ ->
  sht_lang.s = ⟪ 1, s⟫ ->
  Disjoint sht_prog.s sht_lang.s ->
  s1 ∩ s2 = ∅ -> s1 ∪ s2 = s ->
  s'1 ∩ s'2 = ∅ -> s'1 ∪ s'2 = s' ->
  H₁ ==> LGTM.wp [⟨⟪ 0, s'1⟫, sht_prog.ht ⟩, ⟨⟪ 1, s1⟫, sht_lang.ht ⟩ ]
   (fun _ h => (∀ ll ∈ s1, ∃ pp, pp ∈ s'1 ∧ h ⟨1, ll ⟩= h ⟨0, pp⟩) ∧ (hlocal (⟪1,s1⟫ ∪ ⟪0, s'1⟫) h) ) ->
  H₂ ==> LGTM.wp [⟨⟪ 0, s'2⟫, sht_prog.ht ⟩, ⟨⟪ 1, s2⟫, sht_lang.ht ⟩ ]
   (fun _ h => (∀ ll ∈ s2, ∃ pp,  pp ∈ s'2 ∧ h ⟨1, ll ⟩= h ⟨0, pp⟩) ∧ (hlocal (⟪1,s2⟫ ∪ ⟪0, s'2⟫) h)) ->
  H₁ ∗ H₂ ==> LGTM.wp [sht_prog, sht_lang]  (fun _ h => ∀ ll ∈ s, ∃ pp, pp ∈ s' ∧ h ⟨1, ll ⟩= h ⟨0, pp⟩) := by
  move=> prog lang subs sp1 sp2 sp3 sp4 up1 up2
  have subsht : LGTM.wp [sht_prog, sht_lang] (fun _ h => ∀ ll ∈ s, ∃ pp, pp ∈ s' ∧ h ⟨1, ll ⟩= h ⟨0, pp⟩) = LGTM.wp ([⟨⟪ 0, s'1⟫, sht_prog.ht ⟩, ⟨⟪ 1, s1⟫, sht_lang.ht ⟩ ] ++ [⟨⟪ 0, s'2⟫, sht_prog.ht ⟩, ⟨⟪ 1, s2⟫, sht_lang.ht ⟩]) (fun v h => ∀ ll ∈ s, ∃ pp, pp ∈ s' ∧ h ⟨1, ll ⟩= h ⟨0, pp⟩):= by
    unfold LGTM.wp
    simp
    rw [prog,lang]
    have sames : (⟪0, s'⟫ ∪ ⟪1, s⟫) = (⟪0, s'1⟫ ∪ (⟪1, s1⟫ ∪ (⟪0, s'2⟫ ∪ ⟪1, s2⟫))) := by
      unfold labSet
      simp
      aesop
    rw [← sames]
    apply hwp_ht_eq
    unfold Set.EqOn
    intro x
    move=> h
    simp;
    scase_if=>//==
    · move=> h1 h2
      scase_if=>/==
      move=> h3
      scase_if=>//
    · move=> h1
      scase_if=>// h2
      · simp
        rcases h2 with ⟨h21,h22⟩
        scase_if
        aesop
      · apply not_and.mp at h2
        scase_if
        · simp
          move=> h3
          specialize h1 h3
          aesop
        · simp
          move=> h3
          scase_if
          · aesop
          · simp; move => h4
            scase_if
            · simp; move=> h5; aesop
            · simp; move=> h6;
              scase_if
              simp; move=> h7; specialize h2 h7;
              aesop
  rw [subsht]
  set Qp1 : hval (α × β)ˡ → hhProp (α × β)ˡ:= fun _ => fun h ↦ (∀ ll ∈ s2, ∃ pp ∈ s'2, h ⟨1, ll⟩ = h ⟨0, pp⟩ )∧ (hlocal (⟪1,s2⟫ ∪ ⟪0, s'2⟫) h)
  set B : hhProp (α × β)ˡ:= fun  h => (∀ ll ∈ s1, ∃ pp, pp ∈ s'1 ∧ h ⟨1, ll ⟩= h ⟨0, pp⟩) ∧ (hlocal (⟪1,s1⟫ ∪ ⟪0, s'1⟫) h)
  set B' : hval (α × β)ˡ → hhProp (α × β)ˡ:= fun _ => B
  intro hv
  move=> pre
  apply weird_wp_conseq (Q1 := whqstar Qp1 B)
  {
    unfold whqstar B Qp1
    unfold hqimpl hhimpl hhstar hlocal
    intro hv0 hh
    dsimp
    move=> qpre
    rcases qpre with ⟨hv1,hv2, ⟨⟨hl1,hl2⟩ ,⟨hr1,hr2⟩,hh3,hh4⟩⟩
    move=> ll hll
    by_cases h_in_s2 : ll ∈ s2
    · rcases hl1 ll h_in_s2 with ⟨pp, ⟨hp,hp2⟩⟩
      have hl_not_in_s1 : ⟨1,ll⟩ ∉ ⟪1, s1⟫ ∪ ⟪0, s'1⟫ := by
        simp
        intro h_in_s1
        exact Set.not_mem_empty ll ((by rw [←sp1]; exact ⟨h_in_s1, h_in_s2⟩) : ll ∈ ∅)
      have hp_not_in_s1 : ⟨0,pp⟩ ∉ ⟪1, s1⟫ ∪ ⟪0, s'1⟫ := by
        simp
        intro p_in_s2
        exact Set.not_mem_empty pp ((by rw [←sp3]; exact ⟨p_in_s2, hp⟩) : pp ∈ ∅)
      have hr2l := hr2 ⟨1,ll⟩ hl_not_in_s1
      have hr2p := hr2 ⟨0,pp⟩ hp_not_in_s1
      rw [← hr2l] at hr2p
      use pp
      constructor
      { aesop}
      apply union_heap_eq (h := hh) (h1 := hv1) (h2 := hv2)=>//
    · have h_in_s1 : ll ∈ s1 := by
        rw [←sp2, Set.mem_union] at hll
        exact hll.resolve_right h_in_s2
      rcases hr1 ll h_in_s1 with ⟨pp, ⟨hp,hp2⟩⟩
      have hl_not_in_s1 : ⟨1,ll⟩ ∉ ⟪1, s2⟫ ∪ ⟪0, s'2⟫ := by simp; exact h_in_s2
      have hp_not_in_s1 : ⟨0,pp⟩ ∉ ⟪1, s2⟫ ∪ ⟪0, s'2⟫ := by
        simp
        intro p_in_s2
        exact Set.not_mem_empty pp ((by rw [←sp3]; exact ⟨hp, p_in_s2⟩) : pp ∈ ∅)
      have hr2l := hl2 ⟨1,ll⟩ hl_not_in_s1
      have hr2p := hl2 ⟨0,pp⟩ hp_not_in_s1
      rw [← hr2l] at hr2p
      use pp
      constructor
      { aesop}
      apply union_heap_eq (h := hh) (h1 := hv1) (h2 := hv2)=>//
  }
  apply well_formed_sequ_lemma (R := H₁ ∗ H₂) (H := fun x => B ∗ H₂)
  { simp; apply disjoint_label_set.mpr; simp }
  { simp; apply disjoint_label_set.mpr; simp }
  { simp
    constructor
    · constructor
      · apply disjoint_label_set.mpr; simp; apply Set.disjoint_iff_inter_eq_empty.mpr; exact sp3
      · apply disjoint_label_set.mpr; simp
    · constructor
      · apply disjoint_label_set.mpr; simp
      · apply disjoint_label_set.mpr; simp; apply Set.disjoint_iff_inter_eq_empty.mpr; exact sp1
  }
  { apply hhimpl_frame_l (hH₃ := H₂) at up1
    apply hhimpl_trans=>//
    apply LGTM.wp_frame}
  { intro hv
    apply hhimpl_frame_r (hH₃ := B) at up2
    apply hhimpl_trans=>//
    srw hhstar_comm
    apply LGTM.wp_frame
  }
  { exact pre}


theorem tmp1 :
  hhlocal shts.set H₁ ->
  H₁ ==> LGTM.wp shts Q ->
  H₁ ==> LGTM.wp shts (fun hv hh => hlocal shts.set hh ∧ Q hv hh) := by
  intro h1 h2 h hh ; specialize h2 _ hh ; specialize h1 _ hh
  unfold hlocal at h1
  unfold LGTM.wp hwp at *
  rcases h2 with ⟨hQ', h2a, h2b⟩
  unfold heval
  -- exists (fun a v h => if a ∈ shts.set then hQ' a v h ∧  else hQ' a v)
  exists hQ'
  constructor
  · assumption
  · intro hv ; specialize h2b hv
    unfold bighstarDef at *
    intro h_ hh_ ; specialize h2b h_ hh_
    rcases h2b with ⟨hv1, h2b⟩
    dsimp
    exists hv1 ; dsimp ; constructor <;> try assumption
    intro a hnotin ; specialize hh_ a ; simp [hnotin] at hh_ ; rw [hh_] ; apply h1 ; assumption

/- remove hlocal in the postcondition -/
/- Q = fun s1 s2 => ∀ ... -/
set_option maxHeartbeats 1600000 in
lemma weird_grmdisj_lemma_safe (s' s : Set (α × β))  (sht_prog sht_lang : LGTM.SHT) (H₁ H₂ : hhProp (α × β)ˡ):
  sht_prog.s = ⟪0, s'⟫ ->
  sht_lang.s = ⟪ 1, s⟫ ->
  Disjoint sht_prog.s sht_lang.s ->
  s1 ∩ s2 = ∅ -> s1 ∪ s2 = s ->
  s'1 ∩ s'2 = ∅ -> s'1 ∪ s'2 = s' ->
  hhlocal (⟪ 0, s'1⟫ ∪ ⟪ 1, s1⟫) H₁ ->
  H₁ ==> LGTM.wp [⟨⟪ 0, s'1⟫, sht_prog.ht ⟩, ⟨⟪ 1, s1⟫, sht_lang.ht ⟩ ]
   (fun _ h => (∀ ll ∈ s1, ∃ pp, pp ∈ s'1 ∧ h ⟨1, ll ⟩= h ⟨0, pp⟩) ) ->
  ∀ x : hval (α × β)ˡ,
  ( hhstar (fun h => (hlocal (⟪ 0, s'1⟫ ∪ ⟪ 1, s1⟫) h) ∧ (∀ ll ∈ s1, ∃ pp, pp ∈ s'1 ∧ h ⟨1, ll ⟩= h ⟨0, pp⟩) ) H₂) ==>
  LGTM.wp [⟨⟪ 0, s'2⟫, sht_prog.ht ⟩, ⟨⟪ 1, s2⟫, sht_lang.ht ⟩ ]
    (fun hv' ↦ (fun _ h => ∀ ll ∈ s, ∃ pp, pp ∈ s' ∧ h ⟨1, ll ⟩= h ⟨0, pp⟩) (x ∪_(⟪ 0, s'1⟫ ∪ ⟪ 1, s1⟫) hv') ) ->
  H₁ ∗ H₂ ==> LGTM.wp [sht_prog, sht_lang]
    (fun _ h => ∀ ll ∈ s, ∃ pp, pp ∈ s' ∧ h ⟨1, ll ⟩= h ⟨0, pp⟩) := by
  move=> prog lang subs sp1 sp2 sp3 sp4 hlo up1 hva up2
  apply tmp1 at up1 ; dsimp [LGTM.SHTs.set] at up1 ; simp only [Set.union_empty] at up1
  on_goal 2=> dsimp [LGTM.SHTs.set] ; simp only [Set.union_empty] ; assumption
  have subsht : LGTM.wp [sht_prog, sht_lang] (fun _ h => ∀ ll ∈ s, ∃ pp, pp ∈ s' ∧ h ⟨1, ll ⟩= h ⟨0, pp⟩) = LGTM.wp ([⟨⟪ 0, s'1⟫, sht_prog.ht ⟩, ⟨⟪ 1, s1⟫, sht_lang.ht ⟩ ] ++ [⟨⟪ 0, s'2⟫, sht_prog.ht ⟩, ⟨⟪ 1, s2⟫, sht_lang.ht ⟩]) (fun v h => ∀ ll ∈ s, ∃ pp, pp ∈ s' ∧ h ⟨1, ll ⟩= h ⟨0, pp⟩):= by
    unfold LGTM.wp
    simp
    rw [prog,lang]
    have sames : (⟪0, s'⟫ ∪ ⟪1, s⟫) = (⟪0, s'1⟫ ∪ (⟪1, s1⟫ ∪ (⟪0, s'2⟫ ∪ ⟪1, s2⟫))) := by
      unfold labSet
      simp
      aesop
    rw [← sames]
    apply hwp_ht_eq
    unfold Set.EqOn
    intro x
    move=> h
    simp;
    scase_if=>//==
    · move=> h1 h2
      scase_if=>/==
      move=> h3
      scase_if=>//
    · move=> h1
      scase_if=>// h2
      · simp
        rcases h2 with ⟨h21,h22⟩
        scase_if
        aesop
      · apply not_and.mp at h2
        scase_if
        · simp
          move=> h3
          specialize h1 h3
          aesop
        · move=> h3
          scase_if
          · aesop
          · simp; move => h4
            scase_if
            · simp; move=> h5; aesop
            · simp; move=> h6;
              scase_if
              simp; move=> h7; specialize h2 h7;
              aesop
  rw [subsht]
  intro hv
  move=> pre
  apply well_formed_sequ_lemma (R := H₁ ∗ H₂ ) (H := fun x => (hhstar (fun h => (hlocal (⟪ 0, s'1⟫ ∪ ⟪ 1, s1⟫) h) ∧ (∀ ll ∈ s1, ∃ pp, pp ∈ s'1 ∧ h ⟨1, ll ⟩= h ⟨0, pp⟩) ) H₂))
  { simp; apply disjoint_label_set.mpr; simp }
  { simp; apply disjoint_label_set.mpr; simp }
  { simp
    constructor
    · constructor
      · apply disjoint_label_set.mpr; simp; apply Set.disjoint_iff_inter_eq_empty.mpr; exact sp3
      · apply disjoint_label_set.mpr; simp
    · constructor
      · apply disjoint_label_set.mpr; simp
      · apply disjoint_label_set.mpr; simp; apply Set.disjoint_iff_inter_eq_empty.mpr; exact sp1
  }
  { apply hhimpl_frame_l (hH₃ := H₂ ) at up1
    apply hhimpl_trans=>//
    apply LGTM.wp_frame}
  { intro hv
    apply hhimpl_trans=>//
  }
  { exact pre}


lemma weird_index_label_change (i j i' j': ℕ) (st sl : Set α) (sht_prog sht_lang : LGTM.SHT) :
  sht_prog.s = ⟪ i, st⟫ ->
  sht_lang.s = ⟪ j, sl ⟫ ->
  i ≠ j -> i' ≠ j' ->
  [∗ in ⟪ i, st⟫ ∪ ⟪ j, sl⟫ | Hx] ==> LGTM.wp [sht_prog2, sht_lang]
    (fun _ h =>  ∀ ll ∈ sl, ∃ pp ∈ st, h ⟨i,ll⟩= h ⟨j, pp⟩ ) ->
  [∗ in ⟪ i', st⟫ ∪ ⟪ j', sl⟫ | Hx] ==> LGTM.wp [sht_prog2, sht_lang]
    (fun _ h =>  ∀ ll ∈ sl, ∃ pp ∈ st, h ⟨i',ll⟩= h ⟨j', pp⟩ ) := by
  move=> prog lang idx idx2
  unfold hhimpl LGTM.wp --hwp bighstar bighstarDef
  move=> hpre hh2 ha2
  have hh1 := fun a => if a ∈ ⟪i, st⟫ then hh2 ⟨i', a.val⟩ else if a ∈ ⟪j, sl⟫ then hh2 ⟨j', a.val⟩ else hEmpty a
  specialize hpre hh1
  -- apply htriple_ht_extend_eq
  have hh1pre : (∀ (a : αˡ), if a ∈ ⟪i, st⟫ ∪ ⟪j, sl⟫ then (fun x ↦ Hx) a (hh1 a) else hh1 a = hEmpty a) := by
    intro a

    sorry
  sorry


lemma weird_grmdisj_extend_aux (s' s : Set (α × β)) (sht_prog1 sht_prog2 sht_lang : LGTM.SHT) :
  sht_prog1.s = ⟪ 0, s⟫ ->
  sht_prog2.s = ⟪ 1, s⟫ ->
  sht_lang.s = ⟪ 2, sl ⟫ ->
  [∗ in ⟪ 0, s⟫ ∪ ⟪ 1, s⟫ ∪ ⟪ 2, sl⟫ | Hx] ==> LGTM.wp [sht_prog1, sht_prog2, sht_lang ]
   (fun _ h => (∀ ll ∈ sl, ∃ pp, pp ∈ s ∧ h ⟨2, ll ⟩= h ⟨1, pp⟩) ) ->
  [∗ in ⟪ 1, s⟫ ∪ ⟪ 2, sl⟫ | Hx] ==> LGTM.wp [sht_prog2, sht_lang]
    (fun _ h =>  ∀ ll ∈ sl, ∃ pp ∈ s, h ⟨2,ll⟩= h ⟨1, pp⟩ ) := by
  intro prog1 prog2 lang
  -- apply hyper_triple_sht_extend (s := ⟪ 1, s⟫ ∪ ⟪ 2, sl⟫) (shts := [sht_prog1 ]) (p := sht_prog2.ht ∪_⟪ 1, s⟫ sht_lang.ht ) (Qx := fun x (h : hheap (α × β)ˡ) => ∀ ll ∈ sl, ∃ pp ∈ s, h ⟨2, ll⟩ = h ⟨1, pp⟩)
  simp [LGTM.triple, LGTM.wp] at *
  move=> pre hh hpre
  sorry
  -- scase!: hh=> hQ /[dup] hev /==; unfold bighstarDef; simp [fun_insert] => ev imp
  -- apply heval_conseq=> //
  -- unfold bighstar bighstarDef hhimpl


/- to strong, not directly useful -/
lemma weird_grmdisj_extend_aux2 (s' s : Set (α × β)) (sht_prog sht_lang : LGTM.SHT) :
  sht_prog.s = ⟪0, s'⟫ ->
  sht_lang.s = ⟪ 1, s⟫ ->
  [∗ in ⟪ 0, s'⟫ ∪ ⟪ 1, s⟫ | Hx] ∗ H₀ ==> LGTM.wp [⟨⟪ 0, s'⟫, sht_prog.ht ⟩, sht_lang ]
   (fun _ h => (∀ ll ∈ s, ∃ pp, pp ∈ s' ∧ h ⟨1, ll ⟩= h ⟨0, pp⟩) ∧ (hlocal (⟪1,s⟫ ∪ ⟪0, s'⟫) h) ) ->
  ∃ s'', s'' ⊆ s' ∧
 [∗ in ⟪ 0, s''⟫ ∪ ⟪ 1, s⟫ | Hx] ∗ H₀ ==> LGTM.wp [⟨⟪0, s''⟫, sht_prog.ht⟩, sht_lang]
    (fun _ h =>  ∀ ll ∈ s, ∃ pp ∈ s'', h ⟨1,ll⟩= h ⟨0, pp⟩ ∧ (hlocal (⟪1,s⟫ ∪ ⟪0, s''⟫) h)) := by
  intro prog lang pre
  use s'
  constructor --<;> simp
  · simp
  · apply hhimpl_trans=>//
    apply weird_wp_conseq
    unfold hqimpl hhimpl
    intro hv hh up
    aesop

set_option maxHeartbeats 1600000 in
lemma weird_grmdisj_lemma_standard (s' s : Set (α × β)) (sht_prog sht_lang : LGTM.SHT) :
  sht_prog.s = ⟪0, s'⟫ ->
  sht_lang.s = ⟪ 1, s⟫ ->
  Disjoint sht_prog.s sht_lang.s ->
  s1 ∩ s2 = ∅ -> s1 ∪ s2 = s ->
  hhlocal (⟪ 0, s'⟫) H₁ ->
  hhlocal (⟪ 1, s1⟫) H₂ ->
  hhlocal (⟪ 1, s2⟫) H₃ ->
  H₁ ∗ H₂ ==> LGTM.wp [⟨⟪ 0, s'⟫, sht_prog.ht ⟩, ⟨⟪ 1, s1⟫, sht_lang.ht ⟩ ]
   (fun _ h => (∀ ll ∈ s1, ∃ pp, pp ∈ s' ∧ h ⟨1, ll ⟩= h ⟨0, pp⟩) ∧ (hlocal (⟪1,s1⟫ ∪ ⟪0, s'⟫) h) ) ->
  H₁ ∗ H₃ ==> LGTM.wp [⟨⟪ 0, s'⟫, sht_prog.ht ⟩, ⟨⟪ 1, s2⟫, sht_lang.ht ⟩ ]
   (fun _ h => (∀ ll ∈ s2, ∃ pp,  pp ∈ s' ∧ h ⟨1, ll ⟩= h ⟨0, pp⟩) ∧ (hlocal (⟪1,s2⟫ ∪ ⟪0, s'⟫) h)) ->
  H₁ ∗ H₂ ∗ H₃ ==> LGTM.wp [sht_prog, sht_lang]  (fun _ h => ∀ ll ∈ s, ∃ pp, pp ∈ s' ∧ h ⟨1, ll ⟩= h ⟨0, pp⟩) := by
  move=> prog lang subs sp1 sp2 hl1 hl2 hl3
  unfold hhimpl hlocal LGTM.wp hwp heval bighstarDef heval_nonrel
  dsimp
  move=> part1 part2
  intro h h123pre
  specialize part1 h
  specialize part2 h

  have subsht : LGTM.wp [sht_prog, sht_lang] (fun _ h => ∀ ll ∈ s, ∃ pp, pp ∈ s' ∧ h ⟨1, ll ⟩= h ⟨0, pp⟩) = LGTM.wp ([⟨⟪ 0, s'⟫, sht_prog.ht ⟩, ⟨⟪ 1, s1⟫, sht_lang.ht ⟩ ] ++ [⟨⟪ 0, s'⟫, sht_prog.ht ⟩, ⟨⟪ 1, s2⟫, sht_lang.ht ⟩]) (fun v h => ∀ ll ∈ s, ∃ pp, pp ∈ s' ∧ h ⟨1, ll ⟩= h ⟨0, pp⟩):= by
    unfold LGTM.wp
    simp
    rw [prog,lang]
    have sames : (⟪0, s'⟫ ∪ ⟪1, s⟫) = (⟪0, s'⟫ ∪ (⟪1, s1⟫ ∪ (⟪0, s'⟫ ∪ ⟪1, s2⟫))) := by
      unfold labSet
      simp
      aesop
    rw [← sames]
    apply hwp_ht_eq
    unfold Set.EqOn
    intro x
    move=> h
    simp;
    scase_if=>//==
    · move=> h1
      scase_if=>/==
      move=> h3
      scase_if=>//
      scase_if=>//
      { move=> h4
        rcases h4 with ⟨ h41, h42⟩
        simp [h41] at h3
        rw [← sp2] at h3
        have : x.val ∉ s1 := by
          subst sp2
          simp_all only [Prod.exists, Prod.forall, one_ne_zero, IsEmpty.forall_iff, Set.mem_union, true_or,
            not_true_eq_false]
        contradiction
      }
      scase_if=>//
      move=> h5 h6
      rcases h5 with ⟨ h41, h42⟩
      simp [h41] at h3
      rw [← sp2] at h3
      have : x.val ∉ s2 := by
        subst sp2
        simp_all only [Prod.exists, Prod.forall, one_ne_zero, IsEmpty.forall_iff, true_and, Set.mem_union, or_true,
          not_true_eq_false]
      contradiction
  stop
  rw [subsht]
  set Qp1 : hval (α × β)ˡ → hhProp (α × β)ˡ:= fun _ => fun h ↦ (∀ ll ∈ s2, ∃ pp ∈ s', h ⟨1, ll⟩ = h ⟨0, pp⟩ )∧ (hlocal (⟪1,s2⟫ ∪ ⟪0, s'⟫) h)
  set B : hhProp (α × β)ˡ:= fun  h => (∀ ll ∈ s1, ∃ pp, pp ∈ s' ∧ h ⟨1, ll ⟩= h ⟨0, pp⟩) ∧ (hlocal (⟪1,s1⟫ ∪ ⟪0, s'⟫) h)
  set B' : hval (α × β)ˡ → hhProp (α × β)ˡ:= fun _ => B
  intro hv
  move=> pre
  apply weird_wp_conseq (Q1 := whqstar Qp1 B)
  {
    unfold whqstar B Qp1
    unfold hqimpl hhimpl hhstar hlocal
    intro hv0 hh
    dsimp
    move=> qpre
    rcases qpre with ⟨hv1,hv2, ⟨⟨hl1,hl2⟩ ,⟨hr1,hr2⟩,hh3,hh4⟩⟩
    move=> ll hll
    by_cases h_in_s2 : ll ∈ s2
    · rcases hl1 ll h_in_s2 with ⟨pp, ⟨hp,hp2⟩⟩
      have hl_not_in_s1 : ⟨1,ll⟩ ∉ ⟪1, s1⟫ ∪ ⟪0, s'⟫ := by
        simp
        intro h_in_s1
        exact Set.not_mem_empty ll ((by rw [←sp1]; exact ⟨h_in_s1, h_in_s2⟩) : ll ∈ ∅)
      have hp_not_in_s1 : ⟨0,pp⟩ ∉ ⟪1, s1⟫ := by
        simp
        -- intro p_in_s2
        -- exact Set.not_mem_empty pp ((by rw [←sp3]; exact ⟨p_in_s2, hp⟩) : pp ∈ ∅)
      have hr2l := hr2 ⟨1,ll⟩ hl_not_in_s1
      have hr2p := hr2 ⟨0,pp⟩ hp_not_in_s1
      -- rw [← hr2l] at hr2p
      use pp
      constructor
      { aesop}
      apply union_heap_eq (h := hh) (h1 := hv1) (h2 := hv2)=>//
    · have h_in_s1 : ll ∈ s1 := by
        rw [←sp2, Set.mem_union] at hll
        exact hll.resolve_right h_in_s2
      rcases hr1 ll h_in_s1 with ⟨pp, ⟨hp,hp2⟩⟩
      have hl_not_in_s1 : ⟨1,ll⟩ ∉ ⟪1, s2⟫ ∪ ⟪0, s'⟫ := by simp; exact h_in_s2
      have hp_not_in_s1 : ⟨0,pp⟩ ∉ ⟪1, s2⟫ ∪ ⟪0, s'⟫ := by
        simp
        intro p_in_s2
        exact Set.not_mem_empty pp ((by rw [←sp3]; exact ⟨hp, p_in_s2⟩) : pp ∈ ∅)
      have hr2l := hl2 ⟨1,ll⟩ hl_not_in_s1
      have hr2p := hl2 ⟨0,pp⟩ hp_not_in_s1
      rw [← hr2l] at hr2p
      use pp
      constructor
      { aesop}
      apply union_heap_eq (h := hh) (h1 := hv1) (h2 := hv2)=>//
  }
  apply well_formed_sequ_lemma (R := H₁ ∗ H₂) (H := fun x => B ∗ H₂)
  { simp; apply disjoint_label_set.mpr; simp }
  { simp; apply disjoint_label_set.mpr; simp }
  { simp
    constructor
    · constructor
      · apply disjoint_label_set.mpr; simp; apply Set.disjoint_iff_inter_eq_empty.mpr; exact sp3
      · apply disjoint_label_set.mpr; simp
    · constructor
      · apply disjoint_label_set.mpr; simp
      · apply disjoint_label_set.mpr; simp; apply Set.disjoint_iff_inter_eq_empty.mpr; exact sp1
  }
  { apply hhimpl_frame_l (hH₃ := H₂) at up1
    apply hhimpl_trans=>//
    apply LGTM.wp_frame}
  { intro hv
    apply hhimpl_frame_r (hH₃ := B) at up2
    apply hhimpl_trans=>//
    srw hhstar_comm
    apply LGTM.wp_frame
  }
  { exact pre}
/-
lemma weird_grmdisj_premium_aux (s' s: Set (α × β)) (sht_prog sht_lang : LGTM.SHT):
  sht_prog.s = ⟪0, s'⟫ ->
  sht_lang.s = ⟪ 1, s⟫ ->
  Disjoint sht_prog.s sht_lang.s ->
  s1 ∩ s2 = ∅ -> s1 ∪ s2 = s ->
  s'1 ∩ s'2 = ∅ -> s'1 ∪ s'2 = s' ->
  H₂ ==> LGTM.wp [⟨⟪ 0, s'2⟫, sht_prog.ht ⟩, ⟨⟪ 1, s2⟫, sht_lang.ht ⟩ ]
    (fun _ h => (∀ ll ∈ s2, ∃ pp, pp ∈ s'2 ∧ h ⟨1, ll ⟩= h ⟨0, pp⟩) )
    -- (fun hv => (fun xin h => (xin =hv ∧ ∀ ll ∈ s2, ∃ pp, pp ∈ s'2 ∧ h ⟨1, ll ⟩= h ⟨0, pp⟩) ∨ True) (x ∪_(⟪ 0, s'1⟫ ∪ ⟪ 1, s1⟫) hv) )
  ->
  ∀ x : hval (α × β)ˡ,
  (hhstar (fun h => (∀ ll ∈ s1, ∃ pp, pp ∈ s'1 ∧ h ⟨1, ll ⟩= h ⟨0, pp⟩) ) H₂) ==>
  LGTM.wp [⟨⟪ 0, s'2⟫, sht_prog.ht ⟩, ⟨⟪ 1, s2⟫, sht_lang.ht ⟩ ]
    (fun hv' ↦ (fun _ h => ∀ ll ∈ s, ∃ pp, pp ∈ s' ∧ h ⟨1, ll ⟩= h ⟨0, pp⟩) (x ∪_(⟪ 0, s'1⟫ ∪ ⟪ 1, s1⟫) hv') ):= by
  move=> prog lang subs sp1 sp2 sp3 sp4 up1 hv
  apply hhimpl_frame_r (hH₃ := (fun h => (∀ ll ∈ s1, ∃ pp, pp ∈ s'1 ∧ h ⟨1, ll ⟩= h ⟨0, pp⟩) )) at up1
  apply hhimpl_trans=>//
  srw hhstar_comm
  have mid := LGTM.wp_frame (sht := [{ s := ⟪0, s'2⟫, ht := sht_prog.ht }, { s := ⟪1, s2⟫, ht := sht_lang.ht }])
    (Q := fun _ h => (∀ ll ∈ s2, ∃ pp, pp ∈ s'2 ∧ h ⟨1, ll ⟩= h ⟨0, pp⟩))
    -- (Q := fun (hv : hval (α × β)ˡ) => (fun xin h => (xin = hv ∧ ∀ ll ∈ s2, ∃ pp ∈ s'2, h ⟨1, ll⟩ = h ⟨0, pp⟩) ∨ True) (x ∪_(⟪0, s'1⟫ ∪ ⟪1, s1⟫) hv))
    (H := fun h => ∀ ll ∈ s1, ∃ pp ∈ s'1, h ⟨1, ll⟩ = h ⟨0, pp⟩)
  apply hhimpl_trans=>//
  apply weird_wp_conseq
  unfold hqimpl hhimpl
  dsimp
  intro hv1 hh1
  unfold HStar.hStar instHStarHhProp
  dsimp
  unfold hhstar
  intro pre2
  rcases pre2 with ⟨h1,h2,⟨ h31,h32,h33,h34⟩⟩
  unfold hdisjoint at h34
  sorry

set_option maxHeartbeats 1600000 in
lemma weird_grmdisj_lemma_premium (s' s : Set (α × β))  (sht_prog sht_lang : LGTM.SHT) :
  sht_prog.s = ⟪0, s'⟫ ->
  sht_lang.s = ⟪ 1, s⟫ ->
  Disjoint sht_prog.s sht_lang.s ->
  s1 ∩ s2 = ∅ -> s1 ∪ s2 = s ->
  s'1 ∩ s'2 = ∅ -> s'1 ∪ s'2 = s' ->
  H₁ ==> LGTM.wp [⟨⟪ 0, s'1⟫, sht_prog.ht ⟩, ⟨⟪ 1, s1⟫, sht_lang.ht ⟩ ]
   (fun _ h => (∀ ll ∈ s1, ∃ pp, pp ∈ s'1 ∧ h ⟨1, ll ⟩= h ⟨0, pp⟩) ) ->
  H₂ ==> LGTM.wp [⟨⟪ 0, s'2⟫, sht_prog.ht ⟩, ⟨⟪ 1, s2⟫, sht_lang.ht ⟩ ]
    (fun _ h => ∀ ll ∈ s2, ∃ pp, pp ∈ s'2 ∧ h ⟨1, ll ⟩= h ⟨0, pp⟩) ->
  H₁ ∗ H₂ ==> LGTM.wp [sht_prog, sht_lang]
    (fun _ h => ∀ ll ∈ s, ∃ pp, pp ∈ s' ∧ h ⟨1, ll ⟩= h ⟨0, pp⟩) := by
  move=> prog lang subs sp1 sp2 sp3 sp4 up1 up2
  apply weird_grmdisj_premium_aux (s := s) (s' := s') at up2 =>//
  apply weird_grmdisj_lemma_safe (s := s) (s' := s') (s1 := s1 ) (s2 := s2 ) (s'1 := s'1) (s'2 := s'2)=>//
-/
/- Old format of Grmdisj rule -/
/- separate the grammar into s' and s \ s'
 linking to Grmdisj rule in the note
-/
lemma weird_grmdisj_lemma_old (s' s : Set (α ⊕ β)) (sht_prog sht_lang : LGTM.SHT) :
  sht_prog.s = ⟪0, s''⟫ ->
  sht_lang.s = ⟪ 1, s⟫ ->
  s' ⊆ s -> Disjoint sht_prog.s sht_lang.s ->
  -- H ==> LGTM.wp [sht_prog] (fun _ h => ∀ a, a ∉ ⟪0, s \ s'⟫ ∧ h a = ∅) ->
  H₁ ==> LGTM.wp [sht_prog, ⟨⟪ 1, s \ s'⟫, sht_lang.ht ⟩ ]
   (fun _ h => ∀ ll ∈ {l | Sum.inl l ∈ s \ s'}, ∃ pp, pp ∈ {p | Sum.inr p ∈ s''} ∧ h ⟨1, Sum.inl ll ⟩= h ⟨0, Sum.inr pp⟩) ->
  H₂ ==> LGTM.wp [sht_prog, ⟨⟪ 1, s'⟫, sht_lang.ht ⟩ ]
   (fun _ h => ∀ ll ∈ {l | Sum.inl l ∈ s'}, ∃ pp, pp ∈ {p | Sum.inr p ∈ s''} ∧ h ⟨1, Sum.inl ll ⟩= h ⟨0, Sum.inr pp⟩) ->
  hhand H₁ H₂ ==> LGTM.wp [sht_prog, sht_lang]
   (fun v h => ∀ ll ∈ {l | Sum.inl l ∈ s}, ∃ pp, pp ∈ {p | Sum.inr p ∈ s''} ∧ h ⟨1, Sum.inl ll ⟩= h ⟨0, Sum.inr pp⟩) := by
  move=> prog lang subs disj up1 up2 hh pre
  srw (LGTM.wp_focus 0) at up1=>//
  on_goal 2=> simp_all; apply disjoint_label_set.mpr; aesop
  srw (LGTM.wp_focus 0) at up2=>//
  on_goal 2=> simp_all; apply disjoint_label_set.mpr; aesop
  srw (LGTM.wp_focus 0)=>//
  simp_all
  -- apply LGTM.wp_cons
  -- apply hhimpl_frame_l (hH₃ := H₂) at up1
  -- set Hpart1 : hval (α ⊕ β)ˡ → hhProp (α ⊕ β)ˡ := fun x h ↦
  --     ∀ (ll : α), ∃ pp, Sum.inl ll ∈ s \ s' ∧ Sum.inr pp ∈ s'' ∧ h ⟨1, Sum.inl ll⟩ = h ⟨0, Sum.inr pp⟩
  set Hpart1 : hval (α ⊕ β)ˡ → hhProp (α ⊕ β)ˡ := fun x ↦ hhand H₁ H₂
  -- set Hpart_up1 : hval (α ⊕ β)ˡ → hhProp (α ⊕ β)ˡ := fun x ↦ H₁
  -- have up1_set := well_formed_focus_lemma (idx := 0) (l := 0) (shts := [sht_prog, ⟨⟪ 1, s \ s'⟫, sht_lang.ht ⟩ ]) (s := s \ s') (s' := ∅) (H := Hpart_up1) (R := H ∗ H₁)
  -- set upq : hval (α ⊕ β)ˡ → hhProp (α ⊕ β)ˡ:= fun _ h => ∀ ll ∈ {l | Sum.inl l ∈ s \ s'}, ∃ pp, Sum.inr pp ∈ s'' ∧ h ⟨1, Sum.inl ll ⟩= h ⟨0, Sum.inr pp⟩
  -- specialize up1_set upq =>//
  stop
  apply well_formed_focus_lemma (idx := 1) (l := 1) (shts := [sht_prog, sht_lang]) (s' := s') (s := s) (R := H ∗ (H₁ ∗ H₂)) (H := Hpart1)=>//
  { simp_all; apply disjoint_label_set.mpr; aesop }
  { unfold Hpart1
    stop
    apply hhimpl_frame_l

   }
  { intro hv
    unfold Hpart1
    stop
    apply hhimpl_trans=>//
    have mid := LGTM.wp_frame (H := H) (sht := [sht_prog, { s := ⟪1, s \ s'⟫, ht := sht_lang.ht }]) (Q := (fun x h ↦
      ∀ (ll : α), ∃ pp, Sum.inl ll ∈ s \ s' ∧ Sum.inr pp ∈ s'' ∧ h ⟨1, Sum.inl ll⟩ = h ⟨0, Sum.inr pp⟩))
    apply hhimpl_trans=>//
    simp_all
    unfold hhimpl
    -- apply weird_wp_conseq (Q2 := Hpart1)
    -- unfold hqimpl hhimpl Hpart1
    -- intro hv1
    -- srw weird_heap_sub_right
    sorry
  }
  stop
  intro hv2
  unfold Hpart1
  apply hhimpl_trans=>//
  -- apply hhimpl_hhstar_trans_r=>//
  unfold LGTM.wp
  simp_all
  unfold hhimpl
  intro hh
  simp
  -- apply hwp_union
  sorry

#check hhimpl_trans_r
#check if_pos
#check hhimpl
#check ysubst_lemma_aux
#print ysubst_lemma
#print hheap

-- def IndexgetRight! {α β} [Inhabited β]: (α ⊕ β)ˡ → βˡ
--   | x => ⟨x.lab, (WeirdLogic.Sum.getRight! x.val) ⟩


/- ********************************** Lang and Payload Rule ************************************** -/

lemma weird_post_conseq (t : LGTM.SHTs (Labeled α)) (Q1 Q2 : hval (Labeled α) → hhProp (Labeled α)) :
  Q1 ===> Q2 →
  H ==> LGTM.wp t Q1 ->
  H ==> LGTM.wp t Q2 := by
  move=> qq up
  apply hhimpl_trans=>//
  apply weird_wp_conseq (Q1 := Q1) (Q2 := Q2)=>//


lemma weird_lang_lemma (s₁ s₂ : Set (trm × β)) (sht_prog sht_lang : LGTM.SHT) :
  sht_prog.s = ⟪0, s₁⟫ ->
  sht_lang.s = ⟪ 1, s₂⟫ ->
  Disjoint sht_prog.s sht_lang.s ->
  s₂ = {(tl,dp)} ->
  H ==> LGTM.wp [sht_prog, sht_lang] (fun _ h => ∃ pp ∈ s₁,h ⟨1, (tl,dp) ⟩ = h ⟨0, pp⟩) ->
  H ==> LGTM.wp [sht_prog, sht_lang] (fun _ h => ∀ ll ∈ s₂, ∃ pp ∈ s₁, h ⟨1, ll ⟩ = h ⟨0,pp⟩) := by
  move=> prog lang disj set_eq
  apply weird_post_conseq
  unfold hqimpl hhimpl
  intro hv hh
  simp_all


/- remove all quantifiers from the post-condition, prepare for prod rule -/
lemma weird_payload_lemma (s₁ s₂ : Set (α × β)) (sht_prog sht_lang : LGTM.SHT) :
  sht_prog.s = ⟪0, s₁⟫ ->
  sht_lang.s = ⟪ 1, s₂⟫ ->
  Disjoint sht_prog.s sht_lang.s ->
  pr ∈ s₁ ->
  H ==> LGTM.wp [sht_prog, sht_lang] (fun _ h => h ⟨1, pl ⟩= h ⟨0, pr⟩) ->
  H ==> LGTM.wp [sht_prog, sht_lang] (fun _ h => ∃ pp ∈ s₁, h ⟨1, pl ⟩ = h ⟨0, pp⟩):= by
  move=> prog lang disj set_in
  apply weird_post_conseq
  unfold hqimpl hhimpl
  intro hv hh
  move=> up
  use pr

/- as long as the payload is fixed, Prod or InfProd rule is applicable -/
lemma weird_payload_lemma2 (s₁ s₂ : Set (α × β)) (sht_prog sht_lang : LGTM.SHT) :
  sht_prog.s = ⟪0, s₁⟫ ->
  sht_lang.s = ⟪ 1, s₂⟫ ->
  Disjoint sht_prog.s sht_lang.s ->
  pr ∈ s₁ ->
  H ==> LGTM.wp [sht_prog, sht_lang] (fun _ h => ∀ ll ∈ s₂, h ⟨1, ll ⟩= h ⟨0, pr⟩) ->
  H ==> LGTM.wp [sht_prog, sht_lang] (fun _ h => ∀ ll ∈ s₂, ∃ pp ∈ s₁, h ⟨1, ll ⟩ = h ⟨0, pp⟩):= by
  move=> prog lang disj set_in
  apply weird_post_conseq
  unfold hqimpl hhimpl
  aesop

/- fix the payload index set; derivable from weaken lemma -/
lemma weird_payload_aux_lemma (s' s s'': Set α) (sht_prog sht_lang : LGTM.SHT):
  sht_prog.s = ⟪0, s⟫ ->
  sht_lang.s = ⟪1, s''⟫ ->
  s' ⊆ s -> Disjoint sht_prog.s sht_lang.s ->
  H₁ ==> LGTM.wp [⟨⟪0, s \ s'⟫, sht_prog.ht⟩] (fun _ => fun h ↦ ∀ a ∉ ⟪0, s \ s'⟫, h a = ∅ ) ->
  H₂ ==> LGTM.wp [⟨⟪0, s'⟫, sht_prog.ht⟩, sht_lang]
    (fun _ h =>  ∃ pp ∈ s', h ⟨1,ll⟩= h ⟨0, pp⟩ ) ->
  H₁ ∗ H₂ ==> LGTM.wp [sht_prog, sht_lang]
  (fun _ h =>  ∃ pp ∈ s, h ⟨1, ll ⟩= h ⟨0, pp⟩) := by
  move=> prog lang subs disj part1 part2
  intro h12
  move=> H12
  apply weird_wp_conseq (Q1 := fun _ h =>  ∃ pp ∈ s', h ⟨1,ll⟩= h ⟨0, pp⟩)=>//
  { intro x h w; aesop }
  set Qp1 : hval αˡ → hhProp αˡ:= fun _ => (fun h ↦ ∃ pp ∈ s', h ⟨1, ll⟩ = h ⟨0, pp⟩)
  set B : hhProp αˡ:= fun h ↦ ∀ a ∉ ⟪0, s \ s'⟫, h a = ∅
  set B' : hval αˡ → hhProp αˡ:= fun _ => B
  apply weird_wp_conseq (Q1 := whqstar Qp1 B)
  · unfold whqstar B Qp1
    intro x
    simp
    move=> hc hcon
    apply weird_heap_sub_right_fix_lang' (s := s) (Q := B)=>//
    · unfold hhlocal hlocal B
      intro h
      dsimp
      simp
    · unfold B
      simp_all
  apply well_formed_focus_lemma (idx := 0) (l := 0) (shts := [sht_prog, sht_lang]) (s' := s') (s := s) (H := B' ∗ H₂) (R := H₁ ∗ H₂) (Q := Qp1 ∗ B)=>//
  · simp_all; apply disjoint_label_set.mpr; aesop
  · have part11 := (hhimpl_frame_l (hH₃ := H₂) (hH₁ := H₁) (hH₂ := LGTM.wp [{ s := ⟪0, s \ s'⟫, ht := sht_prog.ht }] B'))
    specialize part11 part1
    simp
    apply hhimpl_trans (h₁ := H₁ ∗ H₂ ) ( h₂ := ((LGTM.wp [{ s := ⟪0, s \ s'⟫, ht := sht_prog.ht }] B') ∗ H₂)) (h₃ := LGTM.wp [{ s := ⟪0, s \ s'⟫, ht := sht_prog.ht }] (B' ∗ H₂))
    · exact part11
    · have form1 := LGTM.wp_frame (Q := B') (H := H₂) (sht := [{ s := ⟪0, s \ s'⟫, ht := sht_prog.ht }])
      convert form1
  intro x
  have part21 := (hhimpl_frame_l (hH₃ := B) (hH₁ := H₂) (hH₂ := LGTM.wp [{ s := ⟪0, s'⟫, ht := sht_prog.ht }, sht_lang] Qp1))
  specialize part21 part2
  simp
  unfold B'
  rw [hhstar_comm]
  apply hhimpl_trans (h₁ := H₂ ∗ B) ( h₂ := LGTM.wp [{ s := ⟪0, s'⟫, ht := sht_prog.ht }, sht_lang] Qp1 ∗ B) (h₃ := LGTM.wp [{ s := ⟪0, s ∩ s'⟫, ht := sht_prog.ht }, sht_lang] (Qp1 ∗ B))
  · exact part21
  · have form2 := LGTM.wp_frame ( Q := Qp1) (H := B) (sht := [{ s := ⟪0, s'⟫, ht := sht_prog.ht }, sht_lang])
    convert form2
    aesop

lemma weird_payload_aux_lemma2 (s' s s'' s2' sp: Set α) (sht_prog sht_lang : LGTM.SHT):
  sht_prog.s = ⟪0, s⟫ ->
  sht_lang.s = ⟪1, s''⟫ ->
  s' ⊆ s ->
  s ⊆ sp ->
  Disjoint sht_prog.s sht_lang.s ->
  H₁ ==> LGTM.wp [⟨⟪0, s \ s'⟫, sht_prog.ht⟩] (fun _ => fun h ↦ ∀ a ∉ ⟪0, s \ s'⟫, h a = ∅ ) ->
  H₂ ==> LGTM.wp [⟨⟪0, s'⟫, sht_prog.ht⟩, sht_lang]
    (fun _ h =>  ∀ ll ∈ s2', ∃ pp ∈ sp \ ( s \ s'), h ⟨1,ll⟩= h ⟨0, pp⟩ ) ->
  H₁ ∗ H₂ ==> LGTM.wp [sht_prog, sht_lang]
  (fun _ h => ∀ ll ∈ s2', ∃ pp ∈ sp, h ⟨1, ll ⟩= h ⟨0, pp⟩) := by
  move=> prog lang subs disj dj2 part1 part2
  intro h12
  move=> H12
  apply weird_wp_conseq (Q1 := fun _ h =>  ∀ ll ∈ s2', ∃ pp ∈ sp \ ( s \ s'), h ⟨1,ll⟩= h ⟨0, pp⟩)=>//
  { intro x h w ll hl; specialize w ll hl; aesop }
  set Qp1 : hval αˡ → hhProp αˡ:= fun _ => (fun h ↦ ∀ ll ∈ s2', ∃ pp ∈ sp \ ( s \ s'), h ⟨1, ll⟩ = h ⟨0, pp⟩)
  set B : hhProp αˡ:= fun h ↦ ∀ a ∉ ⟪0, s \ s'⟫, h a = ∅
  set B' : hval αˡ → hhProp αˡ:= fun _ => B
  apply weird_wp_conseq (Q1 := whqstar Qp1 B)
  · unfold whqstar Qp1
    intro x
    simp
    move=> hc hcon
    -- set tmp := ((pp: α )∈ sp ∧ (pp ∈ s → pp ∈ s')) with htmp
    apply weird_heap_sub_right' (s := s) (Q := B)=>//
    · unfold hhlocal hlocal B
      intro h
      dsimp
      simp
      intro ha a pre
      specialize ha a
      have hcond : a.lab = 0 → a.val ∈ s → a.val ∈ s' := by
        intro hl hs
        have ⟨hsp, hss'⟩ := pre hl hs
        exact hss' hs
      exact ha hcond
  apply well_formed_focus_lemma (idx := 0) (l := 0) (shts := [sht_prog, sht_lang]) (s' := s') (s := s) (H := B' ∗ H₂) (R := H₁ ∗ H₂) (Q := Qp1 ∗ B)=>//
  · simp_all; apply disjoint_label_set.mpr; aesop
  · have part11 := (hhimpl_frame_l (hH₃ := H₂) (hH₁ := H₁) (hH₂ := LGTM.wp [{ s := ⟪0, s \ s'⟫, ht := sht_prog.ht }] B'))
    specialize part11 part1
    simp
    apply hhimpl_trans (h₁ := H₁ ∗ H₂ ) ( h₂ := ((LGTM.wp [{ s := ⟪0, s \ s'⟫, ht := sht_prog.ht }] B') ∗ H₂)) (h₃ := LGTM.wp [{ s := ⟪0, s \ s'⟫, ht := sht_prog.ht }] (B' ∗ H₂))
    · exact part11
    · have form1 := LGTM.wp_frame (Q := B') (H := H₂) (sht := [{ s := ⟪0, s \ s'⟫, ht := sht_prog.ht }])
      convert form1
  intro x
  have part21 := (hhimpl_frame_l (hH₃ := B) (hH₁ := H₂) (hH₂ := LGTM.wp [{ s := ⟪0, s'⟫, ht := sht_prog.ht }, sht_lang] Qp1))
  specialize part21 part2
  simp
  unfold B'
  rw [hhstar_comm]
  apply hhimpl_trans (h₁ := H₂ ∗ B) ( h₂ := LGTM.wp [{ s := ⟪0, s'⟫, ht := sht_prog.ht }, sht_lang] Qp1 ∗ B) (h₃ := LGTM.wp [{ s := ⟪0, s ∩ s'⟫, ht := sht_prog.ht }, sht_lang] (Qp1 ∗ B))
  · exact part21
  · have form2 := LGTM.wp_frame ( Q := Qp1) (H := B) (sht := [{ s := ⟪0, s'⟫, ht := sht_prog.ht }, sht_lang])
    convert form2
    aesop

lemma weird_payload_index_lemma (s₁ s₂ : Set (α × β)) (sht_prog sht_lang : LGTM.SHT) :
  sht_prog.s = ⟪0, s₁⟫ ->
  sht_lang.s = ⟪ 1, s₂⟫ ->
  Disjoint sht_prog.s sht_lang.s ->
  pr ∈ s₁ ->
  H₁ ==> LGTM.wp [⟨⟪0,s₁ \ {pr}⟫, sht_prog.ht⟩] (fun _ => fun h=> ∀ a ∉ ⟪0, s₁ \ {pr}⟫ , h a = ∅) ->
  H₂ ==> LGTM.wp [⟨⟪0,{pr}⟫, sht_prog.ht⟩, sht_lang] (fun _ h =>  h ⟨1, pl ⟩= h ⟨0, pr⟩) ->
  H₁ ∗ H₂ ==> LGTM.wp [sht_prog, sht_lang] (fun _ h => ∃ pp ∈ s₁, h ⟨1, pl ⟩ = h ⟨0, pp⟩):= by
  move=> prog lang dsj ele pre1 pre2
  apply weird_payload_aux_lemma (s' := {pr}) (s := s₁)=>//

lemma weird_payload_index_lemma2 (s₁ s₂ s₃ s₄: Set (α × β)) (sht_prog sht_lang : LGTM.SHT) :
  sht_prog.s = ⟪0, s₁⟫ ->
  sht_lang.s = ⟪ 1, s₂⟫ ->
  Disjoint sht_prog.s sht_lang.s ->
  pr ∈ s₁ ->
  s₁ ⊆ s₃ ->
  H₁ ==> LGTM.wp [⟨⟪0,s₁ \ {pr}⟫, sht_prog.ht⟩] (fun _ => fun h=> ∀ a ∉ ⟪0, s₁ \ {pr}⟫ , h a = ∅) ->
  H₂ ==> LGTM.wp [⟨⟪0,{pr}⟫, sht_prog.ht⟩, sht_lang] (fun _ h =>  ∀ ll ∈ s₄, ∃ pp ∈ s₃ \ (s₁ \ {pr}), h ⟨1, ll ⟩= h ⟨0, pp⟩) ->
  H₁ ∗ H₂ ==> LGTM.wp [sht_prog, sht_lang] (fun _ h => ∀ ll ∈ s₄, ∃ pp ∈ s₃, h ⟨1, ll ⟩ = h ⟨0, pp⟩):= by
  move=> prog lang dsj ele sub pre1 pre2
  apply weird_payload_aux_lemma2 (s' := {pr}) (s := s₁)=>//

lemma weird_fix_lang (t : trm) (p : β) (arg_list : List trm):
  H ==> LGTM.wp [sht_prog, { s := ⟪idx, {(t, p)}⟫, ht := fun _ => t.trm_call arg_list }] Q =
  H ==> LGTM.wp [sht_prog, { s := ⟪idx, {(t, p)}⟫, ht := fun lang => lang.val.1.trm_call arg_list }] Q := by
  congr
  apply LGTM.wp_sht_eq
  simp_all

lemma weird_fix_payload1 (dt : trm) (pv : ℤ) (prog : trm) :
  H ==> LGTM.wp [{s := ⟪0, {(dt, pv)}⟫, ht := fun _ : (trm × ℤ)ˡ => prog.trm_call [ x , [lang| ⟨pv⟩]]}, sht_lang] Q =
  H ==> LGTM.wp [{s := ⟪0, {(dt, pv)}⟫, ht := fun p : (trm × ℤ)ˡ => prog.trm_call [ x , [lang| ⟨p.val.2⟩]]}, sht_lang] Q := by
  congr
  apply LGTM.wp_sht_eq
  simp_all

#check bighstar_hhstar_disj
#check bighstarDef_hhstar

open EmptyPCM
lemma hqstar_disjoint_lang_index_eq ( lang_index pay_index lang_index1 lang_index2 pay_index1 pay_index2: Set α):
  lang_index1 ∪ lang_index2 = lang_index ->
  pay_index1 ∪ pay_index2 = pay_index ->
  Disjoint lang_index1 lang_index2 ->
  Disjoint pay_index1 pay_index2 ->
  (hqstar
    (fun (hv': hval αˡ) (h : (hheap αˡ))=> ∀ ll ∈ lang_index1,  ∃ pp ∈ pay_index1, h ⟨1, ll⟩ = h ⟨0, pp⟩)
    (fun (h : (hheap αˡ)) => ∀ ll ∈ lang_index2, ∃ pp ∈ pay_index2, h ⟨1, ll⟩ = h ⟨0, pp⟩)) ===>
  (fun hv' h => ∀ ll ∈ lang_index, ∃ pp ∈ pay_index, h ⟨1, ll⟩ = h ⟨0, pp⟩)
    := by
  move=> un1 un2 disj1 disj2
  unfold hqstar HStar.hStar instHStarHhProp
  dsimp
  rw [hhstar_symbol_replace]
  rw [←hhprop_disjoint_hhadd_eq]
  on_goal 2=>
    unfold hhProp.disjoint
    intro h1 h2
    simp
    intro pre1 pre2
    intro a
    sorry
  intro hv hh
  intro pre
  obtain ⟨ hh1,hh2, h1, h2, h3, h4⟩ := pre
  simp [h3]
  intro ll hl
  sorry


/- ********************************** Sequence Rules ************************************** -/

/- deriables from focus rule and similar to the proof of weaken lemma? -/

lemma weird_seqleft_lemma (s₁ s₂ : Set α):
  True := by
  simp

/- ********************************** For Rules ************************************** -/
lemma htriple_htriple_prod (s1 s2 : Set α) (f : α -> Set α) (H : α -> hProp) (Q : α -> hProp) :
  Disjoint s1 s2 ->
  (∀ a ∈ (s1 ∪ s2), htriple (f a) ht [∗ i in (f a)| H i] (fun hv => [∗ i in (f a)| Q i])) ->
  htriple (s1 ∪ s2) ht [∗ i in (s1 ∪ s2)| H i] (fun hv => [∗ i in (s1 ∪ s2)| Q i]) := by
    move=> disj htr hh hH;
    stop
    apply heval_prod
    {
      sorry
      -- sby move=> a /[dup]?/htr; sapply; move: (hH a)
    }
    sby move=> a; move: (hH a)

#check heval_prod

lemma weird_infdisj_lemma (s1 s2 : Set (α × β)) (Idx : Set ℕ) (sht_prog sht_lang : LGTM.SHT) (f g : ℕ -> (α × β)):
  sht_prog.s = ⟪0, s1⟫ ->
  sht_lang.s = ⟪ 1, s2⟫ ->
  s1 = (⋃ i : ℕ , {f i}) ->
  s2 = (⋃ i : ℕ , {g i}) ->
  -- s2 = (⋃ i : ℕ , {(trm_repeat i inside_trm, depay)} : Set (α × β)) ->
  ∀ k ∈ Idx , ([∗i in ({⟨0,f k⟩,⟨1,g k⟩} : Set (α × β)ˡ) | Hx ] ==> LGTM.wp
    [⟨ {⟨0,f k⟩}, sht_prog.ht ⟩, ⟨{⟨1,g k⟩}, sht_lang.ht ⟩ ]
    (fun _ h => (∀ ll ∈ ({g k} : Set (α × β)), ∃ pp, pp ∈ ({f k} : Set (α × β)) ∧ h ⟨1, ll ⟩= h ⟨0, pp⟩) )) ->
  [∗i in ⟪0, s1⟫ ∪ ⟪1, s2⟫ | Hx ] ==> LGTM.wp
    [sht_prog, sht_lang ]
    (fun _ h => (∀ ll ∈ s2, ∃ pp, pp ∈ s1 ∧ h ⟨1, ll ⟩= h ⟨0, pp⟩) ) := by
  move=> prog lang hf hg n hn pre
  stop
  have tmp := htriple_htriple_prod
      (α := (α × β)ˡ) (s1 := ⟪0, s1⟫) (s2 := ⟪1, s2⟫)
      (f := fun i => {i})
      (H := fun i => Hx)
      -- (Q := fun i => fun h => ∀ ll ∈ s2, ∃ pp, pp ∈ s1 ∧ h i= h j)

  sorry

#check hmkstruct
#check hformula
