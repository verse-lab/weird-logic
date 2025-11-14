import WeirdLogic.Gram
import WeirdLogic.WTriple
import WeirdLogic.WUtil
import WeirdLogic.InfInfProd

import Lgtm.Common.Util

open Lean Lean.Expr Lean.Meta Qq
open Elab Command Term Meta Tactic
open Classical trm val prim

local macro "LabType" : term => `(ℕ)

/- ********************************** Rules ************************************** -/

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

/- Standard Weaken Rule:

          hlocal(P \ P1, H1) {H1} [C(P \ P1)] {⊤}
      {H2} [C(P1); L] { ∀ l ∈ L, ∃ p ∈ P1, h l = hp }
   ------------------------------------------------------
    {H1 ∗ H2} [C(P); L] { ∀ l ∈ L, ∃ p ∈ P, h l = hp }
-/

/- Prod version: s' is the part to keep (P' in weaken rule) -/
set_option maxHeartbeats 640000 in
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

set_option maxHeartbeats 640000 in
lemma weird_weaken_lemma (s' s s'': Set α) (sht_prog sht_lang : LGTM.SHT):
  sht_prog.s = ⟪0, s⟫ ->
  sht_lang.s = ⟪1, s''⟫ ->
  s' ⊆ s -> Disjoint sht_prog.s sht_lang.s ->
  hhlocal ⟪0, s \ s'⟫ H₁ ->
  H₁ ==> LGTM.wp [⟨⟪0, s \ s'⟫, sht_prog.ht⟩] (fun _ => ⊤) ->
  H₂ ==> LGTM.wp [⟨⟪0, s'⟫, sht_prog.ht⟩, sht_lang]
    (fun _ h => ∀ ll ∈ s'', ∃ pp ∈ s', h ⟨1,ll⟩= h ⟨0, pp⟩ ) ->
  H₁ ∗ H₂ ==> LGTM.wp [sht_prog, sht_lang]
  (fun _ h => ∀ ll ∈ s'', ∃ pp ∈ s, h ⟨1, ll ⟩= h ⟨0, pp⟩) := by
  intros ; apply weird_weaken_lemma' <;> try assumption
  rename_i hh tmp ; rw [← LGTM.triple.eq_1, LGTM.triple_hlocal_add_to_post] at hh
  apply LGTM.triple_conseq ; apply hhimpl_refl
  on_goal 2=> apply hh
  on_goal 2=> simp ; assumption
  intro hv hh hpre ; simp at hpre ; apply hpre.left

#check hwp_conseq
#check yfocus_set_lemma_eq
#check yunfocus_lemma


/- ********************************** GrmDisj Rule ************************************** -/

/- See the standard version at GramDisjStandard.lean.

  {H1 ∗ H2} [C(P);L1] {Q(P,L1)}, {H1 ∗ H3} [C(P);L2] {Q(P,L2)}
  ------------------------------------------------------
           {H1 ∗ H2 ∗ H3} [C(P); L] {Q(P,L)}

   The following is the combination of GramDisjStandard and Weaken rule.

  P = P1 ∪+ P2, L = L1 | L2
  {H1} [C(P1);L1] {Q(P1,L1)}, {H2} [C(P2);L2] {Q(P2,L2)}
  ------------------------------------------------------
           {H1 ∗ H2} [C(P); L] {Q(P,L)}
-/
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
        exact Set.notMem_empty ll ((by rw [←sp1]; exact ⟨h_in_s1, h_in_s2⟩) : ll ∈ ∅)
      have hp_not_in_s1 : ⟨0,pp⟩ ∉ ⟪1, s1⟫ ∪ ⟪0, s'1⟫ := by
        simp
        intro p_in_s2
        exact Set.notMem_empty pp ((by rw [←sp3]; exact ⟨p_in_s2, hp⟩) : pp ∈ ∅)
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
        exact Set.notMem_empty pp ((by rw [←sp3]; exact ⟨hp, p_in_s2⟩) : pp ∈ ∅)
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
  rw [← LGTM.triple.eq_1, LGTM.triple_hlocal_add_to_post] at up1
  on_goal 2=> dsimp [LGTM.SHTs.set] ; simp only [Set.union_empty] ; assumption
  dsimp [LGTM.triple, LGTM.SHTs.set] at up1 ; simp only [Set.union_empty] at up1
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


-- lemma weird_index_label_change (i j i' j': ℕ) (st sl : Set α) (sht_prog sht_lang : LGTM.SHT) :
--   sht_prog.s = ⟪ i, st⟫ ->
--   sht_lang.s = ⟪ j, sl ⟫ ->
--   i ≠ j -> i' ≠ j' ->
--   [∗ in ⟪ i, st⟫ ∪ ⟪ j, sl⟫ | Hx] ==> LGTM.wp [sht_prog2, sht_lang]
--     (fun _ h =>  ∀ ll ∈ sl, ∃ pp ∈ st, h ⟨i,ll⟩= h ⟨j, pp⟩ ) ->
--   [∗ in ⟪ i', st⟫ ∪ ⟪ j', sl⟫ | Hx] ==> LGTM.wp [sht_prog2, sht_lang]
--     (fun _ h =>  ∀ ll ∈ sl, ∃ pp ∈ st, h ⟨i',ll⟩= h ⟨j', pp⟩ ) := by
--   move=> prog lang idx idx2
--   unfold hhimpl LGTM.wp --hwp bighstar bighstarDef
--   move=> hpre hh2 ha2
--   have hh1 := fun a => if a ∈ ⟪i, st⟫ then hh2 ⟨i', a.val⟩ else if a ∈ ⟪j, sl⟫ then hh2 ⟨j', a.val⟩ else hEmpty a
--   specialize hpre hh1
--   -- apply htriple_ht_extend_eq
--   have hh1pre : (∀ (a : αˡ), if a ∈ ⟪i, st⟫ ∪ ⟪j, sl⟫ then (fun x ↦ Hx) a (hh1 a) else hh1 a = hEmpty a) := by
--     intro a


-- lemma weird_grmdisj_extend_aux (s' s : Set (α × β)) (sht_prog1 sht_prog2 sht_lang : LGTM.SHT) :
--   sht_prog1.s = ⟪ 0, s⟫ ->
--   sht_prog2.s = ⟪ 1, s⟫ ->
--   sht_lang.s = ⟪ 2, sl ⟫ ->
--   [∗ in ⟪ 0, s⟫ ∪ ⟪ 1, s⟫ ∪ ⟪ 2, sl⟫ | Hx] ==> LGTM.wp [sht_prog1, sht_prog2, sht_lang ]
--    (fun _ h => (∀ ll ∈ sl, ∃ pp, pp ∈ s ∧ h ⟨2, ll ⟩= h ⟨1, pp⟩) ) ->
--   [∗ in ⟪ 1, s⟫ ∪ ⟪ 2, sl⟫ | Hx] ==> LGTM.wp [sht_prog2, sht_lang]
--     (fun _ h =>  ∀ ll ∈ sl, ∃ pp ∈ s, h ⟨2,ll⟩= h ⟨1, pp⟩ ) := by
--   intro prog1 prog2 lang
--   -- apply hyper_triple_sht_extend (s := ⟪ 1, s⟫ ∪ ⟪ 2, sl⟫) (shts := [sht_prog1 ]) (p := sht_prog2.ht ∪_⟪ 1, s⟫ sht_lang.ht ) (Qx := fun x (h : hheap (α × β)ˡ) => ∀ ll ∈ sl, ∃ pp ∈ s, h ⟨2, ll⟩ = h ⟨1, pp⟩)
--   simp [LGTM.triple, LGTM.wp] at *
--   move=> pre hh hpre
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

#check hhimpl_trans_r
#check if_pos
#check hhimpl
#check ysubst_lemma_aux
#print ysubst_lemma
#print hheap


/- ********************************** Lang and Payload Rule ************************************** -/

/- Rules to fix the program or payload in the triple
   P = {p}, {H} [C(p); L] { ∀ l ∈ L, h l = h p}
   --------------------------------------------- Fix-Payload
   {H} [C(P); L] { ∀ l ∈ L, ∃ p ∈ P, h l = h p}

   L = {l}, {H} [C(P); l] { ∃ p ∈ P, h l = h p}
   --------------------------------------------- Fix-Lang
   {H} [C(P); L] { ∀ l ∈ L, ∃ p ∈ P, h l = h p}

-/
lemma weird_post_conseq (t : LGTM.SHTs (Labeled α)) (Q1 Q2 : hval (Labeled α) → hhProp (Labeled α)) :
  Q1 ===> Q2 →
  H ==> LGTM.wp t Q1 ->
  H ==> LGTM.wp t Q2 := by
  move=> qq up
  apply hhimpl_trans=>//
  apply weird_wp_conseq (Q1 := Q1) (Q2 := Q2)=>//

lemma weird_pre_conseq (t : LGTM.SHTs (Labeled α)) (Q : hval (Labeled α) → hhProp (Labeled α)) :
  H1 ==> H2 →
  H2 ==> LGTM.wp t Q ->
  H1 ==> LGTM.wp t Q := by
  move=> qq up
  apply hhimpl_trans=>//

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
set_option maxHeartbeats 3200000 in
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

set_option maxHeartbeats 3200000 in
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

set_option maxHeartbeats 3200000 in
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

set_option maxHeartbeats 3200000 in
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

lemma weird_fix_payload2 (dt : trm) (pv : ℤ) (prog : trm):
  H ==> LGTM.wp [{s := ⟪0, {(dt, pv)}⟫, ht := fun _ : (trm × ℤ)ˡ => prog.trm_call [x, y, [lang| ⟨pv⟩]]}, sht_lang] Q =
  H ==> LGTM.wp [{s := ⟪0, {(dt, pv)}⟫, ht := fun p : (trm × ℤ)ˡ => prog.trm_call [x, y, [lang| ⟨p.val.2⟩]]}, sht_lang] Q := by
  congr
  apply LGTM.wp_sht_eq
  simp_all

#check bighstar_hhstar_disj
#check bighstarDef_hhstar


/- ********************************** InfDisj Rules ************************************** -/

/- Infinitely disjoint rule
    f is the partition of P, g is the partition of L
      ∀ i ∈ Idx, {H(i)}[C(f i); g i] {Q(i)}
  ---------------------------------------------------
    { f_(i ∈ Idx) H(i)} [C(P); L] { f_(i ∈ Idx) Q (i)}

-/


lemma inject_labSet (s1 : Set α) (Idx : Set β)(f : β -> α) (k : ℕ):
  s1 = ⋃ i ∈ Idx, {f i} ->
  ⟪k,s1⟫ = ⋃ i ∈ Idx, ({⟨k,(f i)⟩ }: Set αˡ) := by
  move=> h
  rw [h]; unfold labSet
  simp
  ext x
  constructor <;> move=>hh; subst h; simp_all only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_singleton_iff, exists_prop]
  · obtain ⟨w, h⟩ := hh
    obtain ⟨left, right⟩ := h
    obtain ⟨w_1, h⟩ := left
    obtain ⟨left, right_1⟩ := h
    subst right_1 right
    simp_all only [Labeled.mk.injEq, true_and]
    apply Exists.intro
    · apply And.intro
      on_goal 2 => {rfl
      }
      · simp_all only
  · subst h
    simp_all only [Set.mem_iUnion, Set.mem_singleton_iff, exists_prop, Set.mem_setOf_eq]
    obtain ⟨w, h⟩ := hh
    obtain ⟨left, right⟩ := h
    subst right
    simp_all only [Labeled.mk.injEq, true_and, exists_eq_right]
    apply Exists.intro
    · apply And.intro
      on_goal 2 => {rfl
      }
      · simp_all only

set_option maxHeartbeats 3200000 in
lemma weird_infdisj_lemma (s1 s2 : Set (α × β)) (Idx : Set ℕ) (sht_prog sht_lang : LGTM.SHT) (f g : ℕ -> (α × β)):
  sht_prog.s = ⟪0, s1⟫ ->
  sht_lang.s = ⟪ 1, s2⟫ ->
  s1 = (⋃ i ∈ Idx , {f i}) ->
  s2 = (⋃ i ∈ Idx , {g i}) ->
  Function.Injective f ->
  Function.Injective g ->
  -- s2 = (⋃ i : ℕ , {(trm_repeat i inside_trm, depay)} : Set (α × β)) ->
  (∀ k ∈ Idx , ([∗i in ({⟨0,f k⟩,⟨1,g k⟩} : Set (α × β)ˡ) | Hx ] ==> LGTM.wp
    [⟨ {⟨0,f k⟩}, sht_prog.ht ⟩, ⟨{⟨1,g k⟩}, sht_lang.ht ⟩ ]
    (fun _ h => (∀ ll ∈ ({g k} : Set (α × β)), ∃ pp, pp ∈ ({f k} : Set (α × β)) ∧ h ⟨1, ll ⟩= h ⟨0, pp⟩) ))) ->
  [∗i in ⟪0, s1⟫ ∪ ⟪1, s2⟫ | Hx ] ==> LGTM.wp
    [sht_prog, sht_lang ]
    (fun _ h => (∀ ll ∈ s2, ∃ pp, pp ∈ s1 ∧ h ⟨1, ll ⟩= h ⟨0, pp⟩) ) := by
  move=> prog lang hf hg injf injg pre
  unfold LGTM.wp at pre ; simp [LGTM.SHTs.set] at pre
  have tmp := htriple_htriple_partition
      (α := (α × β)ˡ) (s := Idx)
      (pf := fun i => {⟨0, f i⟩, ⟨1, g i⟩ })
      (ht := fun _ => sht_prog.ht ∪_⟪0, s1⟫ sht_lang.ht ∪_⟪1, s2⟫ fun x => [lang| ()])
      (ht' := sht_prog.ht ∪_⟪0, s1⟫ sht_lang.ht ∪_⟪1, s2⟫ fun x => [lang| ()])
      (hh := fun i => Hx)
      (Q := fun i _ => fun h => (h ⟨1, g i⟩ )= (h ⟨0, f i⟩ )
          -- else  h ⟨1, g i⟩ = ∅ ∧ h ⟨0, f i⟩ = ∅
          )
  specialize tmp --( by simp ; clear *- ; aesop ) (by intros ; rfl)
    (by
      intro i hi j hj ijneq ; rw [Set.disjoint_iff_forall_ne] ; simp
      constructor <;> intro hh
      · apply injf at hh ; contradiction
      · apply injg at hh ; contradiction
    )
    (by simp ; clear *- ; aesop )
    (by intros ; rfl)
    (by
      intro k kin ; specialize pre k kin
      rewrite (occs := .pos [2]) [Set.pair_comm] at pre
      rw [hwp_ht_eq (ht₂ := (sht_prog.ht ∪_⟪0, s1⟫sht_lang.ht ∪_⟪1, s2⟫fun x ↦ [lang| ()]))] at pre
      on_goal 2 =>
        simp [Set.EqOn]
        constructor
        · have hfk : f k ∈ s1 := by rw [hf];simp; use k
          simp [hfk]
        · have hfk : g k ∈ s2 := by rw [hg];simp; use k;
          simp [hfk]
      assumption )
    (by intros ; rfl)
  unfold LGTM.wp
  simp [LGTM.SHTs.set, prog, lang]
  have eq : (⟪0, s1⟫ ∪ ⟪1, s2⟫) = (⋃ j ∈ Idx, {⟨0, f j⟩, ⟨1, g j⟩}) := by
    simp [inject_labSet _ _ _ _ hf, inject_labSet _ _ _ _ hg]
    simp only [← Set.iUnion_union_distrib] ; rfl
  rw [← eq] at tmp
  apply htriple_conseq ; apply tmp ; apply hhimpl_refl
  intro hv hh ; simp [hhforall, hf, hg] ; clear *- hh ; aesop
