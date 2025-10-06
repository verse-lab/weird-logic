import Lgtm.Unary.Lang
import Lgtm.Hyper.HProp
import Lgtm.Hyper.YSimp
import Lgtm.Hyper.YChange
import Lgtm.Hyper.WP
import Lgtm.Hyper.ProofMode
import Lgtm.Hyper.SepLog
import Lgtm.Common.LabType

import WeirdLogic.Gram
import WeirdLogic.WTriple
-- import WeirdLogic.Util

open Lean Lean.Expr Lean.Meta Qq
open Elab Command Term Meta Tactic
open Classical trm val prim

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

lemma weird_wp_conseq (t : LGTM.SHTs (Labeled α)) (Q1 Q2 : hval (Labeled α) → hhProp (Labeled α)) :
  Q1 ===> Q2 →
  LGTM.wp t Q1 ==> LGTM.wp t Q2 := by
  move=> ??
  srw []LGTM.wp => ?
  sby apply heval_conseq

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

-- #print yfocus_set_lemma
-- #check qstar
-- #check hhstar
-- #check hqstar
-- #check hwp

def whqstar {A} (q : A → @hhProp α) (h : @hhProp α) : A → @hhProp α :=
  fun x => hhstar (q x) h

/- not used yet -/
def weird_hstar (Q : @hval α-> @hhProp α) (H : @hhProp α) :
  (Q ∗ H) = whqstar Q H:= by
  aesop

lemma weird_hwp_conseq (ht : @htrm α) (Q Q' : @hval α -> @hhProp α) :
  Q ===> Q' -> hwp s ht Q hr -> hwp s ht Q' hr:= by
  sby move=> ??/=; apply heval_conseq

lemma weird_hwp_conseq' (ht : @htrm α) (Q Q' : @hval α -> @hhProp α) :
  Q ===> (∃ʰ hv, Q' $ · ∪_s hv) -> hwp s ht Q hv -> hwp s ht Q' hv:= by
  sby move=> ??/=; apply heval_conseq'


lemma hval_form_eq (hv : @hval αˡ) :
  hv = fun x => hv x := by
  simp

lemma hval_eq (hv' : @hval αˡ) (hv2 : @hval αˡ):
  hv2 = hv' ->
  hv' = (fun x ↦ if x.lab = l then (hv' ∪_⟪l, s'⟫hv2) x else hv' x) := by
  move => hx
  simp
  rw [hval_form_eq hv']
  funext x
  by_cases h1: x.lab = l
  · simp [h1]
    by_cases h2 : x.val ∈ s'
    · simp [h2]
    · simp [h2]; aesop;
  · simp [h1]

lemma hwp_heap_frame :
  hwp s ht Q = hwp s2 ht2 Q2 ->
  hwp s ht Q h = hwp s2 ht2 Q2 h := by
  move=>?
  aesop

lemma weird_hwp_union (s₁ s₂ : Set α) :
  Disjoint s₁ s₂ ->
  hwp (s₁ ∪ s₂) ht Q h = hwp s₁ ht (fun hv => hwp s₂ ht (fun hv' => Q (hv ∪_s₁ hv'))) h:= by
    move=> ?
    apply hwp_heap_frame
    apply hhimpl_antisymm=> ?<;> unfold hwp=> ?
    { sby apply heval_unfocus }
    sby apply heval_focus

def well_formed_focus_lemma (idx : ℕ) (l : LabType) (s' s : Set α) (shts : LGTM.SHTs (Labeled α)) (H Q: hval αˡ → hhProp αˡ) {pi : idx < shts.length} :
  shts[idx].s = ⟪l, s⟫ ->
  (shts.Pairwise (Disjoint ·.s ·.s)) ->
  (Disjoint (LGTM.SHTs.set (List.eraseIdx shts idx)) ⟪l, Set.univ⟫) ->
  R ==> LGTM.wp [⟨⟪l, s \ s'⟫, shts[idx].ht⟩] H ->
  (∀ x : hval αˡ, (H x) ==> LGTM.wp ((shts.eraseIdx (idx)).insertIdx idx ⟨⟪l, s ∩ s'⟫, shts[idx].ht⟩)
  fun hv' ↦ Q (fun_lab_insert l (hv' ∪_⟪l, s'⟫ x) hv')) ->
  R ==> LGTM.wp shts (fun hv ↦ Q hv) := by
  move=> shtsset disj1 disj2 up1
  intro up2
  have focuswp := yfocus_set_lemma_aux (s' := s') (Q := fun hv ↦ Q hv)
  specialize focuswp idx l s shts
  {exact pi}
  specialize focuswp shtsset disj1 disj2
  apply hhimpl_trans=>//
  apply hhimpl_trans_r=>//
  unfold LGTM.wp
  have same_s : (LGTM.SHTs.set [{ s := ⟪l, s \ s'⟫, ht := shts[idx].ht }]) = ⟪l, s \ s'⟫ := by simp
  rw [same_s]
  srw (hwp_ht_eq (s := ⟪l, s \ s'⟫ ) (ht₁ := shts[idx].ht ) (ht₂ := (shts[idx].ht ∪_⟪l, s \ s'⟫ (fun x ↦ [lang| ()]))))
  on_goal 2 =>
    unfold Set.EqOn
    intro xl
    simp
    move=>xh1 xh2 xh3
    split_ifs
    · rfl
    · simp_all
  apply hwp_conseq
  simp [LGTM.wp] at up2
  intro hx
  specialize up2 hx
  simp
  apply hhimpl_trans=>//

#check Finmap.Disjoint

-- lemma hwp_Q_eq' (Q Q' : @hval α-> @hhProp α) :
--   (∀ hv, Q hv = (∃ʰ hv, Q' $ · ∪_s hv) hv) -> hwp s ht Q = hwp s ht Q' := by
--   move=> pre; apply congr=> // !
--   move=> hv/=
--   specialize pre hv
--   srw (pre)
--   apply Eq.symm
--   -- unfold hhexists
--   ysimp [hv]=>//
--   · apply hhimpl_hhexists_l
--     intro hv'
--     sorry
--   · srw (fun_insert_ff); aesop

#check hhprop_disjoint_comm

lemma hhprop_antisymm (H₁ H₂ : @hhProp α ) :
    H₁ ==> H₂ ∧ H₂ ==> H₁ ->
    H₁ = H₂ := by
    move=> h
    rcases h with ⟨h1,h2⟩
    aesop

lemma hqimpl_trans {h₁ h₂ h₃ : hval α → hhProp α} : h₁ ===> h₂ -> h₂ ===> h₃ -> h₁ ===> h₃ :=
  fun h₁h₂ h₂h₃ hhv hh HH₁ => h₂h₃ hhv hh (h₁h₂ hhv hh HH₁)

-- lemma heval_conseq'' (Q Q' : @hval α-> @hhProp α):
--   heval s hh t Q1 →
--   (∃ʰ hv : @hval α, Q1 $ · ∪_s hv) ===> Q2 →
--   heval s hh t Q2 := by
--   scase! => ?? himp qimp ⟨//|⟩
--   constructor=> // hv
--   ychange himp=> ?; ychange qimp=> ?
--   stop
--   srw fun_insert_ss; ysimp

-- lemma hwp_conseq'' (ht : @htrm α) (Q Q' : @hval α-> @hhProp α) :
--   (∃ʰ hv, Q $ · ∪_s hv) ===> Q' -> hwp s ht Q ==> hwp s ht Q' := by
--   move=> a b c//==
--   apply heval_conseq''=>//

/- From yfocus_set_lemma_aux
 - Prove the focus lemma in both directions
-/
set_option maxHeartbeats 1600000 in
lemma yfocus_set_lemma_eq (idx : ℕ) (l : LabType) (s' s : Set α) (shts : LGTM.SHTs (Labeled α))
  {pi : idx < shts.length} :
  shts[idx].s = ⟪l, s⟫ ->
  -- (∀ h: hval αˡ , ∀ x ∉ s, h ⟨l,x⟩ = val_unit ) ->
  (shts.Pairwise (Disjoint ·.s ·.s)) ->
  (Disjoint (LGTM.SHTs.set (List.eraseIdx shts idx)) ⟪l, Set.univ⟫) ->
    (hwp ⟪l, s \ s'⟫ shts[idx].ht fun hv =>
    LGTM.wp ((shts.eraseIdx (idx)).insertIdx idx ⟨⟪l, s ∩ s'⟫,shts[idx].ht⟩) fun hv' =>
      Q $ fun_lab_insert l (hv' ∪_⟪l,s'⟫ hv) hv') = LGTM.wp shts Q := by
    stop -- to save time for testing
    move=> seq --uniset
    move =>/[dup]?/List.pairwise_iff_getElem dj' /[dup] dj₁ /Set.disjoint_left dj
    srw (LGTM.wp_focus idx) //' seq -(Set.diff_union_inter ⟪l,s⟫ ⟪l,s'⟫) /==
    srw hwp_union; apply hwp_Q_eq=> //'; rotate_left
    { simp [disjE, Set.disjoint_sdiff_inter] }
    move=> hv₁ /=; srw (LGTM.wp_focus idx)
    { srw  List.getElem_insertIdx_self //=; rotate_left
      { srw List.length_insertIdx if_pos List.length_eraseIdx if_pos //' }
      srw List.eraseIdx_insertIdx /=
      apply hwp_Q_eq=> hv₂ /=;
      apply hhprop_antisymm
      constructor
      on_goal 1 =>
        apply hwp_conseq'=> hv₃ /=;
        ysimp [fun_lab_insert l ((hv₂ ∪_⟪l, s ∩ s'⟫hv₃) ∪_⟪l, s'⟫hv₁) (hv₂ ∪_⟪l, s ∩ s'⟫hv₃)];
        apply congr_hhimpl; congr!; funext ⟨m,x⟩=> /==
        scase_if=> /== ?
        scase_if=> /==
        { scase_if=> //' }
        scase_if=> //';
        scase_if=> //' /dj //
      apply hwp_conseq'=> hv₃ /=;
      ysimp [fun_lab_insert l ((hv₂ ∪_⟪l, s ∩ s'⟫hv₃) ∪_⟪l, s'⟫hv₁) (hv₂ ∪_⟪l, s ∩ s'⟫hv₃)];
      intro hv
      apply congr_hhimpl; congr!; funext ⟨m,x⟩=> /==
      scase_if=> /== h
      scase_if=> /==
      { scase_if=> //'
        scase_if=> //
      }
      scase_if=> //';
      scase_if=> //';
      scase_if=> //
      -- required the added assumption, otherwise, False
      sorry
    }
    srw List.pairwise_iff_getElem=> > ?
    srw List.length_insertIdx if_pos at _hi <;> try omega
    on_goal 2=> srw List.length_eraseIdx if_pos //
    srw List.length_eraseIdx if_pos // at _hi
    srw List.length_insertIdx if_pos at _hj <;> try omega
    on_goal 2=> srw List.length_eraseIdx if_pos //
    srw List.length_eraseIdx if_pos at _hj <;> try omega
    srw ?(List.insertIdx_getElem _) //'
    { scase: [i < idx]=> ?
      { srw dif_neg //'; scase: [i = idx]=> ?
        { srw dif_neg //' (List.eraseIdx_getElem _) <;> try omega
          sdo 3 srw dif_neg <;> try omega
          srw (List.eraseIdx_getElem _) <;> try omega
          srw dif_neg <;> try omega
          apply dj'; omega }
        srw dif_pos //' /= dif_neg //' dif_neg //'
        srw (List.eraseIdx_getElem _) <;> try omega
        srw dif_neg <;> try omega
        srw disjoint_comm; apply Set.disjoint_of_subset _ _ dj₁=> x //'
        srw shts_set_eq_sum=> ? ; simp only [Nat.Ico_zero_eq_range, mem_union, Finset.mem_range]
        exists (j -1)=> ⟨|⟩
        { srw List.length_eraseIdx if_pos //' }
        srw getElem!_pos //'  (List.eraseIdx_getElem _) //'
        srw dif_neg //' }
      srw dif_pos //' (List.eraseIdx_getElem _) //' dif_pos //'
      scase: [j < idx]=> ?
      { srw dif_neg //'; scase: [j = idx]=> ?
        { srw dif_neg //' (List.eraseIdx_getElem _) //' dif_neg //'
          apply dj'=> //' }
        srw dif_pos //'=> /=; apply Set.disjoint_of_subset _ _ dj₁=> x //'
        srw shts_set_eq_sum=> ? ; simp only [Nat.Ico_zero_eq_range, mem_union, Finset.mem_range]
        exists (i)=> ⟨|⟩
        { srw List.length_eraseIdx if_pos=> //' }
        srw getElem!_pos //'  (List.eraseIdx_getElem _) //' }
      srw dif_pos //'(List.eraseIdx_getElem _) //' }
    all_goals srw List.length_eraseIdx if_pos=> //'

def well_formed_focus_eq_lemma (idx : ℕ) (l : LabType) (s' s : Set α) (shts : LGTM.SHTs (Labeled α)) (H Q: hval αˡ → hhProp αˡ) {pi : idx < shts.length} :
  shts[idx].s = ⟪l, s⟫ ->
  (shts.Pairwise (Disjoint ·.s ·.s)) ->
  (∀ h: hval αˡ , ∀ x ∉ s, h ⟨l,x⟩ = val_unit ) ->
  (Disjoint (LGTM.SHTs.set (List.eraseIdx shts idx)) ⟪l, Set.univ⟫) ->
  R ==> LGTM.wp shts (fun hv ↦ Q hv) =
  R ==> LGTM.wp [⟨⟪l, s \ s'⟫, shts[idx].ht⟩] H ∧
  (∀ x : hval αˡ, (H x) ==> LGTM.wp ((shts.eraseIdx (idx)).insertIdx idx ⟨⟪l, s ∩ s'⟫, shts[idx].ht⟩)
  fun hv' ↦ Q (fun_lab_insert l (hv' ∪_⟪l, s'⟫ x) hv')) := by
  move=> shtsset disj1 hemp disj2
  have focuswp := yfocus_set_lemma_eq (s' := s') (Q := fun hv ↦ Q hv)
  specialize focuswp idx l s shts
  {exact pi}
  -- specialize focuswp shtsset hemp disj1 disj2
  -- rw [← focuswp]
  -- unfold hhimpl
  sorry

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
  H₁ ==> LGTM.wp [⟨⟪0, s \ s'⟫, sht_prog.ht⟩] (fun _ => fun h ↦ ∀ a, a ∉ ⟪0, s \ s'⟫ ∧ h a = ∅ ) ->
  H₂ ==> LGTM.wp [⟨⟪0, s'⟫, sht_prog.ht⟩, sht_lang]
    (fun _ h => ∀ ll ∈ {l | Sum.inl l ∈ s''}, ∃ pp, Sum.inr pp ∈ s' ∧ h ⟨1, Sum.inl ll ⟩= h ⟨0, Sum.inr pp⟩) ->
  H₁ ∗ H₂ ==> LGTM.wp [sht_prog, sht_lang]
  (fun _ h => ∀ ll ∈ {l | Sum.inl l ∈ s''}, ∃ pp, Sum.inr pp ∈ s ∧ h ⟨1, Sum.inl ll ⟩= h ⟨0, Sum.inr pp⟩) := by
  move=> prog lang subs disj part1 part2
  intro h12
  move=> H12
  apply weird_weaken_mid_post_lemma=>//
  set Qp1 : hval (α ⊕ β)ˡ → hhProp (α ⊕ β)ˡ:= fun _ => (fun h ↦ ∀ ll ∈ {l | Sum.inl l ∈ s''}, ∃ pp, Sum.inr pp ∈ s' ∧ h ⟨1, Sum.inl ll⟩ = h ⟨0, Sum.inr pp⟩)
  set B : hhProp (α ⊕ β)ˡ:= fun h ↦ ∀ a, a ∉ ⟪0, s \ s'⟫ ∧ h a = ∅
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
  H₁ ==> LGTM.wp [⟨⟪0, s \ s'⟫, sht_prog.ht⟩] (fun _ => fun h ↦ ∀ a, a ∉ ⟪0, s \ s'⟫ ∧ h a = ∅ ) ->
  H₂ ==> LGTM.wp [⟨⟪0, s'⟫, sht_prog.ht⟩, sht_lang]
    (fun _ h => ∀ ll ∈ s'', ∃ pp ∈ s', h ⟨1,ll⟩= h ⟨0, pp⟩ ) ->
  H₁ ∗ H₂ ==> LGTM.wp [sht_prog, sht_lang]
  (fun _ h => ∀ ll ∈ s'', ∃ pp ∈ s, h ⟨1, ll ⟩= h ⟨0, pp⟩) := by
  move=> prog lang subs disj part1 part2
  intro h12
  move=> H12
  apply weird_weaken_mid_post_lemma'=>//
  set Qp1 : hval αˡ → hhProp αˡ:= fun _ => (fun h ↦ ∀ ll ∈ s'', ∃ pp ∈ s', h ⟨1, ll⟩ = h ⟨0, pp⟩)
  set B : hhProp αˡ:= fun h ↦ ∀ a, a ∉ ⟪0, s \ s'⟫ ∧ h a = ∅
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

lemma weird_grmdisj_lemma_aux' (s' s : Set (α × β)) (H₃ HH H₁ H₂ : hhProp (α × β)ˡ) (Q : hval (α × β)ˡ → hhProp (α × β)ˡ) (sht_prog sht_lang : LGTM.SHT) :
  sht_prog.s = ⟪0, s''⟫ ->
  sht_lang.s = ⟪ 1, s⟫ ->
  s' ⊆ s -> Disjoint sht_prog.s sht_lang.s ->
  HH ∗ H₁ ==> LGTM.wp [sht_prog] (fun hv1 => LGTM.wp [sht_lang1] fun hv2 => Q (hv2 ∪_⟪1, s \ s'⟫ hv1)) ->
  HH ∗ H₂ ==> (LGTM.wp [sht_prog] (fun hv1 => LGTM.wp [sht_lang2] fun hv2 => Q (hv2 ∪_⟪1, s'⟫ hv1))) ->
  HH ∗ H₁ ∗ H₂ ==> LGTM.wp [sht_prog] (fun hv1 => LGTM.wp [sht_lang1] fun hv2 => LGTM.wp [sht_lang2] fun hv3 => Q (hv3 ∪_⟪1, s'⟫ (hv2 ∪_⟪1, s \ s'⟫ hv1)) ) := by
  move=>prog lang subst disj h1 h2
  unfold LGTM.wp at h1 h2
  sorry


lemma weird_grmdisj_lemma' (s' s : Set (α × β)) (sht_prog sht_lang : LGTM.SHT) :
  sht_prog.s = ⟪0, s''⟫ ->
  sht_lang.s = ⟪ 1, s⟫ ->
  s' ⊆ s -> Disjoint sht_prog.s sht_lang.s ->
  -- H₃ = HH  (H₁ ∗ H₂) ->
  HH ∗ H₁ ==> LGTM.wp [sht_prog, ⟨⟪ 1, s \ s'⟫, sht_lang.ht ⟩ ] (fun _ h => ∀ ll ∈ s \ s', ∃ pp, pp ∈ s'' ∧ h ⟨1, ll ⟩= h ⟨0, pp⟩) ->
  HH ∗ H₂ ==> LGTM.wp [sht_prog, ⟨⟪ 1, s'⟫, sht_lang.ht ⟩ ] (fun _ h => ∀ ll ∈ s', ∃ pp,  pp ∈ s'' ∧ h ⟨1, ll ⟩= h ⟨0, pp⟩) ->
  HH ∗ H₁ ∗ H₂ ==> LGTM.wp [sht_prog, sht_lang]  (fun v h => ∀ ll ∈ s, ∃ pp, pp ∈ s'' ∧ h ⟨1, ll ⟩= h ⟨0, pp⟩) := by
  sorry

#check hhand

/- Another format of Grmdisj rule -/
lemma weird_grmdisj_lemma_aux (s' s : Set (α ⊕ β)) (sht_prog sht_lang1 sht_lang2 : LGTM.SHT) (Q : hval (α ⊕ β)ˡ → hhProp (α ⊕ β)ˡ) :
  sht_prog.s = ⟪0, s''⟫ ->
  sht_lang1.s = ⟪ 1, s \ s'⟫ ->
  sht_lang2.s = ⟪ 1, s'⟫ ->
  s' ⊆ s -> Disjoint sht_prog.s sht_lang1.s ->
  hhand (LGTM.wp [sht_prog] (fun hv1 => LGTM.wp [sht_lang1] fun hv2 => Q (hv2 ∪_⟪1, s \ s'⟫ hv1)) )
  (LGTM.wp [sht_prog] (fun hv1 => LGTM.wp [sht_lang2] fun hv2 => Q (hv2 ∪_⟪1, s'⟫ hv1))) ==>
  LGTM.wp [sht_prog] (fun hv1 => LGTM.wp [sht_lang1] fun hv2 => LGTM.wp [sht_lang2] fun hv3 => Q (hv3 ∪_⟪1, s'⟫ (hv2 ∪_⟪1, s \ s'⟫ hv1)) ) := by
  sorry

/- separate the grammar into s' and s \ s'
 linking to Grmdisj rule in the note
-/
lemma weird_grmdisj_lemma (s' s : Set (α ⊕ β)) (sht_prog sht_lang : LGTM.SHT) :
  sht_prog.s = ⟪0, s''⟫ ->
  sht_lang.s = ⟪ 1, s⟫ ->
  s' ⊆ s -> Disjoint sht_prog.s sht_lang.s ->
  -- H ==> LGTM.wp [sht_prog] (fun _ h => ∀ a, a ∉ ⟪0, s \ s'⟫ ∧ h a = ∅) ->
  H₁ ==> LGTM.wp [sht_prog, ⟨⟪ 1, s \ s'⟫, sht_lang.ht ⟩ ] (fun _ h => ∀ ll ∈ {l | Sum.inl l ∈ s \ s'}, ∃ pp, pp ∈ {p | Sum.inr p ∈ s''} ∧ h ⟨1, Sum.inl ll ⟩= h ⟨0, Sum.inr pp⟩) ->
  H₂ ==> LGTM.wp [sht_prog, ⟨⟪ 1, s'⟫, sht_lang.ht ⟩ ] (fun _ h => ∀ ll ∈ {l | Sum.inl l ∈ s'}, ∃ pp, pp ∈ {p | Sum.inr p ∈ s''} ∧ h ⟨1, Sum.inl ll ⟩= h ⟨0, Sum.inr pp⟩) ->
  hhand H₁ H₂ ==> LGTM.wp [sht_prog, sht_lang]  (fun v h => ∀ ll ∈ {l | Sum.inl l ∈ s}, ∃ pp, pp ∈ {p | Sum.inr p ∈ s''} ∧ h ⟨1, Sum.inl ll ⟩= h ⟨0, Sum.inr pp⟩) := by
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

/- ********************************** Lemmas for Index Type ************************************** -/

lemma weird_index_subst_left (l : ℕ) (a b c: βˡ ) (x x' : (α ⊕ β )ˡ)
  (f : βˡ → trm) (pay_index : Set β ) (prog : trm)
  (Q : hval (α ⊕ β)ˡ → hhProp (α ⊕ β)ˡ)
  (Q' : hval βˡ → hhProp βˡ):
  pay_index.Nonempty ->
  H' ==> LGTM.wp [{
    s := ⟪l, pay_index⟫,
    ht := fun b => prog.trm_call [f b]
  }] Q' ->
  H ==> LGTM.wp [{
    s := {x : (α ⊕ β )ˡ | ∃ a ∈ ⟪l, pay_index⟫, ⟨a.lab, Sum.inr (a.val)⟩ = x},
    ht := fun x': (α ⊕ β )ˡ ↦
      match Function.partialInv (fun c : βˡ ↦ ⟨c.lab, Sum.inr c.val⟩) x' with
      | some b => prog.trm_call [f b]
      | none => default
  }] Q := by
  move=> nonem up
  -- apply ysubst_lemma ( «σ» := WeirdLogic.Sum.getRight!) =>//
  -- · simp;sorry
  -- · simp_all; sorry
  -- · move=> *; simp_all; sorry
  -- · sorry
  -- simp;
  sorry


/- ********************************** Lang and Payload Rule ************************************** -/

lemma weird_post_conseq (t : LGTM.SHTs (Labeled α)) (Q1 Q2 : hval (Labeled α) → hhProp (Labeled α)) :
  Q1 ===> Q2 →
  H ==> LGTM.wp t Q1 ->
  H ==> LGTM.wp t Q2 := by
  move=> qq up
  apply hhimpl_trans=>//
  apply weird_wp_conseq (Q1 := Q1) (Q2 := Q2)=>//

lemma weird_lang_lemma (s₁ s₂ : Set (α ⊕ β)) (pl : α) (sht_prog sht_lang : LGTM.SHT) :
  sht_prog.s = ⟪0, s₁⟫ ->
  sht_lang.s = ⟪ 1, s₂⟫ ->
  Disjoint sht_prog.s sht_lang.s ->
  s₂ = {(Sum.inl pl)} ->
  H ==> LGTM.wp [sht_prog, sht_lang] (fun _ h => ∃ pp, Sum.inr pp ∈ s₁ ∧ h ⟨1, Sum.inl pl ⟩ = h ⟨0, Sum.inr pp⟩) ->
  H ==> LGTM.wp [sht_prog, sht_lang] (fun _ h => ∀ ll ∈ {l | Sum.inl l ∈ s₂}, ∃ pp, Sum.inr pp ∈ s₁ ∧  h ⟨1, Sum.inl ll ⟩ = h ⟨0, Sum.inr pp⟩) := by
  move=> prog lang disj set_eq
  apply weird_post_conseq
  unfold hqimpl hhimpl
  intro hv hh
  simp_all


lemma weird_payload_lemma (s₁ s₂ : Set (α ⊕ β)) (pr : β) (sht_prog sht_lang : LGTM.SHT) :
  sht_prog.s = ⟪0, s₁⟫ ->
  sht_lang.s = ⟪ 1, s₂⟫ ->
  Disjoint sht_prog.s sht_lang.s ->
  Sum.inr pr ∈ s₁ ->
  H ==> LGTM.wp [sht_prog, sht_lang] (fun _ h => h ⟨1, Sum.inl pl ⟩= h ⟨0, Sum.inr pr⟩) ->
  H ==> LGTM.wp [sht_prog, sht_lang] (fun _ h => ∃ pp, Sum.inr pp ∈ s₁ ∧ h ⟨1, Sum.inl pl ⟩ = h ⟨0, Sum.inr pp⟩):= by
  move=> prog lang disj set_in
  apply weird_post_conseq
  unfold hqimpl hhimpl
  intro hv hh
  move=> up
  simp_all
  use pr

lemma weird_lang_lemma' (s₁ s₂ : Set (trm × β)) (sht_prog sht_lang : LGTM.SHT) :
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


lemma weird_payload_lemma' (s₁ s₂ : Set (α × β)) (sht_prog sht_lang : LGTM.SHT) :
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

lemma weird_payload_lemma2' (s₁ s₂ : Set (α × β)) (sht_prog sht_lang : LGTM.SHT) :
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

lemma weird_payload_focus_lemma' (s₁ s₂ : Set (α × β)) (sht_prog sht_lang : LGTM.SHT) :
  sht_prog.s = ⟪0, s₁⟫ ->
  sht_lang.s = ⟪ 1, s₂⟫ ->
  Disjoint sht_prog.s sht_lang.s ->
  pr ∈ s₁ ->
  H ==> LGTM.wp [{s:= ⟪0,{pr}⟫, ht:= sht_lang.ht}, sht_lang] (fun _ h => ∀ ll ∈ s₂, h ⟨1, ll ⟩= h ⟨0, pr⟩) ->
  H ==> LGTM.wp [sht_prog, sht_lang] (fun _ h => ∀ ll ∈ s₂, ∃ pp ∈ s₁, h ⟨1, ll⟩ = h ⟨0, pp⟩):= by
  move=> prog lang disj set_in
  sorry

lemma weird_fix_lang (t : trm):
  H ==> LGTM.wp [sht_prog, { s := ⟪l, {(t, p)}⟫, ht := fun l => t }] Q =
  H ==> LGTM.wp [sht_prog, { s := ⟪l, {(t, p)}⟫, ht := fun lang => lang.val.1 }] Q := by
  congr
  apply LGTM.wp_sht_eq
  simp_all

lemma weird_seqleft_lemma (s₁ s₂ : Set (α ⊕ β)):
  True := by
  simp

#check hmkstruct
#check hformula
