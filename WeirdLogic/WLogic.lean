
import Lgtm.Unary.Lang
import Lgtm.Hyper.HProp
import Lgtm.Hyper.YSimp
import Lgtm.Hyper.YChange
import Lgtm.Hyper.WP
import Lgtm.Hyper.ProofMode
import Lgtm.Hyper.SepLog

import WeirdLogic.Gram

open Lean Lean.Expr Lean.Meta Qq
open Elab Command Term Meta Tactic
open Classical trm val prim

variable {α : Type} (s : Set α)

-- local notation "htrm" => htrm α
-- local notation "hval" => hval α
-- local notation "hhProp" => hhProp α

section WTriple

local macro "LabType" : term => `(ℕ)

def hgram (α : Type) := α -> trm

inductive payload_base : Type where
  | pld_bool : Bool → payload_base
  | pld_nat : ℕ → payload_base

inductive payload : Type where
  | pld_nil : payload
  | pld_cons : payload_base → payload → payload

def hwtrm (α : Type) := α -> trm /- α is payload later-/

local notation "hwtrm" => hwtrm α

def payload_to_list (p : payload) : List val :=
  match p with
  | payload.pld_nil => []
  | payload.pld_cons b p' =>
    match b with
    | payload_base.pld_bool b => [val.val_bool b] ++ payload_to_list p'
    | payload_base.pld_nat n => [val.val_int n] ++ payload_to_list p'

abbrev payload_map := Finmap ( λ _ : var ↦ val)

def lgtm_match (l : trm) (L : cfg) : Prop :=
  match_cfg l L

/- do substitube now, add choose in while later -/
def render_C (C : trm) (p : payload_map ) (v : List var): trm :=
  v.foldl ( λ C svar =>
    let sval := p.lookup svar |>.getD (val.val_int 0)
    subst svar (trm.trm_val sval) C
  ) C

#check Unary.isubst
def render_C' (C : trm) (p : List ℕ ) (v : List var): trm :=
  let ppairs := p.zip v
  ppairs.foldl (
    λ C svar =>
    subst svar.2 (trm.trm_val (val.val_int svar.1)) C
  ) C

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
    exact w ll'

#check heval_nonrel
#print bighstarDef
#check hhstar
#print hheap

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


#print yfocus_set_lemma
#print yfocus_set_lemma
#check hhProp α
#check qstar
#check hhstar
#check hqstar
#check hwp

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

  -- apply yfocus_set_lemma_aux (s' := s')=>//
  -- simp [hhimpl] at up1 up2
  -- specialize up1 hr prer
  -- have same_set := hwp_ht_eq (s := ⟪l, s \ s'⟫ ) (ht₁ := shts[idx].ht ) (ht₂ := (shts[idx].ht ∪_⟪l, s \ s'⟫ (fun x ↦ [lang| ()]))) (Q := H)
  -- have hteq : Set.EqOn shts[idx].ht (shts[idx].ht ∪_⟪l, s \ s'⟫fun x ↦ [lang| ()]) ⟪l, s \ s'⟫ := by
  --   unfold Set.EqOn
  --   intro xl
  --   simp
  --   move=>xh1 xh2 xh3
  --   split_ifs
  --   · rfl
  --   · simp_all
  -- specialize same_set hteq
  -- -- have up1' := by
  -- --   rw [← same_set] at up1
  -- --   exact up1
  -- -- unfold LGTM.wp
  -- -- revert hr
  -- -- apply LGTM.wp_focus
  -- apply weird_hwp_union (s₁ := ⟪l, s \ s'⟫) (s₂ := (LGTM.SHTs.set (List.insertIdx idx { s := ⟪l, s ∩ s'⟫, ht := shts[idx].ht } (List.eraseIdx shts idx))))
  -- apply weird_hwp_conseq'
  -- · intro hv2 hheap2 hpre2
  --   unfold LGTM.wp
  --   have up2' := up2 hv2 hheap2 hpre2
  --   unfold hhexists
  --   use hv2
  --   simp
  --   apply weird_hwp_conseq
  --   · intro B hheapB hpreB
  --     unfold fun_lab_insert
  --     -- unfold hhexists
  --     -- use B
  --     rw [← hval_eq B]
  --     exact hpreB
  --     unfold fun_insert
  --     simp
  --   · exact up2'
  -- · aesop

#check Finmap.Disjoint

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

/- s' is the part to keep (P' in weaken rule) -/
lemma weird_weaken_lemma  (s' s s'': Set (α ⊕ β)) (sht_prog sht_lang : LGTM.SHT):
  sht_prog.s = ⟪0, s⟫ ->
  sht_lang.s = ⟪1, s''⟫ ->
  s' ⊆ s -> Disjoint sht_prog.s sht_lang.s ->
  H₁ ==> LGTM.wp [⟨⟪0, s \ s'⟫, sht_prog.ht⟩] (fun _ => fun h ↦ ∀ a, a ∈ ⟪0, s \ s'⟫ ∧ h a ≠ ∅ ) ->
  H₂ ==> LGTM.wp [⟨⟪0, s'⟫, sht_prog.ht⟩, sht_lang] (fun _ h => ∀ ll ∈ {l | Sum.inl l ∈ s''}, ∃ pp, Sum.inr pp ∈ s' ∧ h ⟨1, Sum.inl ll ⟩= h ⟨0, Sum.inr pp⟩) ->
  H₁ ∗ H₂ ==> LGTM.wp [sht_prog, sht_lang]
  (fun _ h => ∀ ll ∈ {l | Sum.inl l ∈ s''}, ∃ pp, Sum.inr pp ∈ s ∧ h ⟨1, Sum.inl ll ⟩= h ⟨0, Sum.inr pp⟩) := by
  move=> prog lang subs disj part1 part2
  intro h12
  move=> H12
  apply weird_weaken_mid_post_lemma=>//
  set Qp1 : hval (α ⊕ β)ˡ → hhProp (α ⊕ β)ˡ:= fun _ => (fun h ↦ ∀ ll ∈ {l | Sum.inl l ∈ s''}, ∃ pp, Sum.inr pp ∈ s' ∧ h ⟨1, Sum.inl ll⟩ = h ⟨0, Sum.inr pp⟩)
  set B : hhProp (α ⊕ β)ˡ:= fun h ↦ ∀ a, a ∈ ⟪0, s \ s'⟫ ∧ h a ≠ ∅
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
  · simp_all; rw [@disjoint_label_set]; aesop
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

  /- if use yfocus_set_lemma, TOO HORRIBLE !!! -/
  -- apply yfocus_set_lemma_aux 0 1 s' s [sht_prog, sht_lang] (Q := whqstar Qp1 B) =>//
  -- { simp
  --   rw [lang]
  --   simp_all
  --   rw [@disjoint_label_set]
  --   aesop
  -- }
  -- {
  --   simp_all
  --   unfold whqstar LGTM.wp
  --   have part11 := (hhimpl_frame_l (hH₃ := H₂) (hH₁ := H₁) (hH₂ := LGTM.wp [{ s := ⟪1, s \ s'⟫, ht := sht_prog.ht }] fun x ↦ B))
  --   specialize part11 part1
  --   have part21 := (hhimpl_frame_r (hH₃ := B) (hH₁ := H₂) (hH₂ := LGTM.wp [{ s := ⟪1, s'⟫, ht := sht_prog.ht }, sht_lang] Qp1))
  --   specialize part21 part2
  --   simp [hhimpl, LGTM.wp] at part11 part21
  --   specialize part11 h12 H12
  --   simp_all
  --   apply hwp_frame at part11

  --   convert part11
  --   ·
  --   -- rcases part11 with ⟨part11h, ⟨ part11h2, ⟨part11wp1, ⟨part11wp21,part11wp22, part11wp23⟩ ⟩⟩⟩

  --   substs part11wp22
  --   apply hwp_frame
  --   -- specialize part11 p21
  --   -- simp [LGTM.wp] at p21
  --   -- simp_all

  --   let hQ' : (α ⊕ β)ˡ → val → hProp := hhstar H₂ B
  --   use hQ'
  --   constructor
  --   {
  --   }
  --   {
  --     intro hv
  --     dsimp
  --     move=> hhv hvbig
  --     simp_all
  --     unfold hhexists
  --   }
  -- }
  -- apply weird_weaken_mid_post_lemma=>//
  -- sby apply weird_weaken_mid_body_lemma


lemma weird_grmdisj_lemma (s' s : Set (α ⊕ β)) (sht_prog sht_lang : LGTM.SHT) :
  sht_prog.s = ⟪1, s''⟫ ->
  sht_lang.s = ⟪ 2, s⟫ ->
  s' ⊆ s →
  H ==> LGTM.wp [sht_prog, ⟨⟪ 2, s'⟫, sht_lang.ht ⟩ ] (fun _ h => ∀ ll, ∃ pp, Sum.inl ll ∈ s' ∧ h ⟨2, Sum.inl ll ⟩= h ⟨1, Sum.inr pp⟩) ->
  H ==> LGTM.wp [sht_prog, ⟨⟪ 2, s \ s'⟫, sht_lang.ht ⟩ ] (fun _ h => ∀ ll, ∃ pp, Sum.inl ll ∈ s \ s' ∧ h ⟨2, Sum.inl ll ⟩= h ⟨1, Sum.inr pp⟩) ->
  H ==> LGTM.wp [sht_prog, sht_lang]  (fun _ h => ∀ ll, ∃ pp, Sum.inl ll ∈ s ∧ h ⟨2, Sum.inl ll ⟩= h ⟨1, Sum.inr pp⟩) := by
  move=> prog lang subs set1 set2 hh
  intro H
  sorry

#check hhimpl_trans_r
#check if_pos

lemma weird_lang_lemma ( s : Set (α ⊕ β)) (shts : LGTM.SHTs (Labeled (α ⊕ β))) (h: shts.length = 2) (tl : α) {pi : idx < shts.length}
  [FindLabel l shts idx pi] :
  shts[idx].s = ⟪1, s⟫ ->
  idx = 0 ∧ shts[1].s = ⟪ 2, s'⟫ ->
  {⟨1, (Sum.inl tl)⟩} = shts[0].s ->
  LGTM.wp shts (fun _ h => ∃ pp, h ⟨1, Sum.inl tl ⟩= h ⟨1, Sum.inr pp⟩)
  ==> LGTM.wp shts (fun _ h => ∀ ll , ∃ pp, h ⟨2, Sum.inl ll ⟩= h ⟨1, Sum.inr pp⟩) := by
  sorry

lemma weird_payload_lemma ( s : Set (α ⊕ β)) (shts : LGTM.SHTs (Labeled (α ⊕ β))) (h: shts.length = 2) (tp : β) (tl : α) :
  ⟨2, (Sum.inr pp)⟩ ∈ shts.set ->
  LGTM.wp shts (fun _ h => h ⟨1, Sum.inl tl ⟩= h ⟨2, Sum.inr tp⟩)
  ==> LGTM.wp shts (fun _ h => ∃ pp, h ⟨1, Sum.inl tl ⟩= h ⟨1, Sum.inr pp⟩) := by
  sorry

lemma weird_seqleft_lemma ( s : Set (α ⊕ β)) (shts : LGTM.SHTs (Labeled (α ⊕ β))) (h: shts.length = 2):
  True := by
  simp

#check hmkstruct
#check hformula

end WTriple
