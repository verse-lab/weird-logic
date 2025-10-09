import Lgtm.Unary.Lang
import Lgtm.Hyper.HProp
import Lgtm.Hyper.YSimp
import Lgtm.Hyper.YChange
import Lgtm.Hyper.WP
import Lgtm.Hyper.ProofMode
import Lgtm.Hyper.SepLog
import Lgtm.Common.LabType

open Lean Lean.Expr Lean.Meta Qq
open Elab Command Term Meta Tactic
open Classical trm val prim

local macro "LabType" : term => `(ℕ)

/- This file contains supplementary lemmas of LGTM especially for Weird Logic -/

lemma weird_wp_conseq (t : LGTM.SHTs (Labeled α)) (Q1 Q2 : hval (Labeled α) → hhProp (Labeled α)) :
  Q1 ===> Q2 →
  LGTM.wp t Q1 ==> LGTM.wp t Q2 := by
  move=> ??
  srw []LGTM.wp => ?
  sby apply heval_conseq

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

#check hwp_union

/- WpNEst lemma from LGTM. A generalized version of unfocus lemma (see fig 18) -/
def wp_nest_focus_lemma (shts1 shts2: LGTM.SHTs (Labeled α)) :
  Disjoint shts1.set shts2.set ->
  (List.Pairwise (Disjoint ·.s ·.s) shts1) ->
  (List.Pairwise (Disjoint ·.s ·.s) shts2) ->
  LGTM.wp (shts1 ++ shts2) Q = LGTM.wp shts1 (fun x => LGTM.wp shts2 (fun hv' => Q (x ∪_(shts1.set) hv'))) := by
  move=> sh dj1 dj2
  unfold LGTM.wp
  simp
  srw (hwp_union)=>//
  rw [← hwp_ht_eq (ht₁:= shts1.htrm) (ht₂:= (shts1.htrm ∪_shts1.set shts2.htrm))]
  on_goal 2=>
    unfold Set.EqOn
    intro xl
    simp
    move=>xh1
    split_ifs=>//
  apply hwp_Q_eq
  intro hv
  rw [← hwp_ht_eq (ht₁:= shts2.htrm) (ht₂:= (shts1.htrm ∪_shts1.set shts2.htrm))]
  unfold Set.EqOn
  intro xl xlh
  simp
  have xl2 : xl ∉ shts1.set := by exact Disjoint.not_mem_of_mem_left (id (Disjoint.symm sh)) xlh
  split_ifs=>//


/- SeqU lemma from LGTM. (see fig 18)-/
def well_formed_sequ_lemma (shts1 shts2 : LGTM.SHTs (Labeled α)) (H Q: hval αˡ → hhProp αˡ) :
  (shts1.Pairwise (Disjoint ·.s ·.s)) ->
  (shts2.Pairwise (Disjoint ·.s ·.s)) ->
  Disjoint shts1.set shts2.set ->
  R ==> LGTM.wp shts1 H ->
  (∀ x : hval αˡ, (H x) ==> LGTM.wp shts2
  fun hv' ↦ Q (x ∪_(shts1.set) hv') ) ->
  R ==> LGTM.wp (shts1++shts2) Q:= by
  move=> disj1 disj2 disj3 up1 up2
  apply hhimpl_trans=>//
  srw (wp_nest_focus_lemma)=>//
  apply weird_wp_conseq
  intro x
  specialize up2 x
  exact up2

lemma hhprop_antisymm (H₁ H₂ : @hhProp α ) :
    H₁ ==> H₂ ∧ H₂ ==> H₁ ->
    H₁ = H₂ := by
    move=> h
    rcases h with ⟨h1,h2⟩
    aesop

lemma hqimpl_trans {h₁ h₂ h₃ : hval α → hhProp α} : h₁ ===> h₂ -> h₂ ===> h₃ -> h₁ ===> h₃ :=
  fun h₁h₂ h₂h₃ hhv hh HH₁ => h₂h₃ hhv hh (h₁h₂ hhv hh HH₁)

set_option maxHeartbeats 1600000 in
lemma yfocus_set_lemma_eq (idx : ℕ) (l : LabType) (s' s : Set α) (shts : LGTM.SHTs (Labeled α))
  {pi : idx < shts.length} :
  shts[idx].s = ⟪l, s⟫ ->
  (shts.Pairwise (Disjoint ·.s ·.s)) ->
  (Disjoint (LGTM.SHTs.set (List.eraseIdx shts idx)) ⟪l, Set.univ⟫) ->
    (hwp ⟪l, s \ s'⟫ shts[idx].ht fun hv =>
    LGTM.wp ((shts.eraseIdx (idx)).insertIdx idx ⟨⟪l, s ∩ s'⟫,shts[idx].ht⟩) fun hv' =>
      Q (hv ∪_⟪l,s \ s'⟫ hv') ) = LGTM.wp shts Q := by
    -- stop -- to save time for testing
    move=> seq
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
        apply hwp_conseq=> hv₃ /=;
        ysimp
        apply congr_hhimpl; unfold fun_insert;
        apply congr_arg; funext ⟨m,x⟩=> /==
        scase_if=> /==
      apply hwp_conseq=> hv₃ /=;
      apply congr_hhimpl; unfold fun_insert;
      apply congr_arg; funext ⟨m,x⟩=> /==
      scase_if=> /==
      scase_if=> //== h1 h2
      scase_if=> //== h3
      scase_if=> //==
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

lemma congr_hhimpl_right ( H Q₁ Q₂ : hhProp α ) :
  Q₁ = Q₂ -> H ==> Q₁ = H ==> Q₂ := by
  move=> h
  subst h; rfl

/- need to know the H, unless cannot be proved -/
lemma nesthwp_wp (idx : ℕ)  (l : LabType) (s' s : Set α) (shts : LGTM.SHTs (Labeled α)) (H Q: hval αˡ → hhProp αˡ) {pi : idx < shts.length} :
  shts[idx].s = ⟪l, s⟫ ->
  H = (fun x => LGTM.wp ((shts.eraseIdx (idx)).insertIdx idx ⟨⟪l, s ∩ s'⟫, shts[idx].ht⟩) (fun hv' ↦ Q (x ∪_⟪l, s \ s'⟫ hv'))) ->
  (R ==> LGTM.wp [⟨⟪l, s \ s'⟫, shts[idx].ht⟩]
  (fun x : hval αˡ => LGTM.wp ((shts.eraseIdx (idx)).insertIdx idx ⟨⟪l, s ∩ s'⟫, shts[idx].ht⟩)
  fun hv' ↦ Q (x ∪_⟪l, s \ s'⟫ hv')) ) =
  (
    R ==> LGTM.wp [⟨⟪l, s \ s'⟫, shts[idx].ht⟩] H ∧
    ∀ x: hval αˡ, H x ==> LGTM.wp ((shts.eraseIdx (idx)).insertIdx idx ⟨⟪l, s ∩ s'⟫, shts[idx].ht⟩) (fun hv' ↦ Q (x ∪_⟪l, s \ s'⟫ hv'))
  ) := by
  move=> sh hh
  apply propext; apply Iff.intro
  · move=> up
    constructor
    · rw [hh]
      exact up
    · rw [hh]
      simp
  · move=> up
    rcases up with ⟨up1,up2⟩
    apply hhimpl_trans=>//
    apply weird_wp_conseq
    intro x
    specialize up2 x
    exact up2


def well_formed_focus_inverse_lemma (idx : ℕ) (l : LabType) (s' s : Set α) (shts : LGTM.SHTs (Labeled α)) (Q: hval αˡ → hhProp αˡ) {pi : idx < shts.length} :
  shts[idx].s = ⟪l, s⟫ ->
  (shts.Pairwise (Disjoint ·.s ·.s)) ->
  (Disjoint (LGTM.SHTs.set (List.eraseIdx shts idx)) ⟪l, Set.univ⟫) ->
  R ==> LGTM.wp shts (fun hv ↦ Q hv) ->
  (R ==> LGTM.wp [⟨⟪l, s \ s'⟫, shts[idx].ht⟩]
  (fun x : hval αˡ => LGTM.wp ((shts.eraseIdx (idx)).insertIdx idx ⟨⟪l, s ∩ s'⟫, shts[idx].ht⟩)
  fun hv' ↦ Q (x ∪_⟪l, s \ s'⟫ hv')) ) := by
  move=> shtsset disj1 disj2 up1
  let focuswp := yfocus_set_lemma_eq (s' := s') (Q := fun hv ↦ Q hv)
  specialize focuswp idx l s shts
  {exact pi}
  specialize focuswp shtsset disj1 disj2
  rw [← focuswp] at up1
  unfold LGTM.wp
  unfold LGTM.wp at up1
  simp_all
  srw (hwp_ht_eq (s := ⟪l, s \ s'⟫ ) (ht₁ := shts[idx].ht ) (ht₂ := (shts[idx].ht ∪_⟪l, s \ s'⟫ (fun x ↦ [lang| ()])))) at up1
  on_goal 2 =>
    unfold Set.EqOn
    intro xl
    simp
    move=>xh1 xh2 xh3
    split_ifs
    · rfl
    · simp_all
  exact up1
