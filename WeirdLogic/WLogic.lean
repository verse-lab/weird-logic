
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

-- lemma weird_weaken_mid_body_lemma (s' s s'': Set (α ⊕ β)) (sht_prog sht_lang : LGTM.SHT):
--   sht_prog.s = ⟪1, s⟫ ->
--   sht_lang.s = ⟪ 2, s''⟫ ->
--   s' ⊆ s -> Disjoint sht_prog.s sht_lang.s ->
--   hhstar (LGTM.wp [⟨⟪1, s\ s'⟫, sht_prog.ht⟩] Q)
--   (LGTM.wp [⟨⟪1, s'⟫, sht_prog.ht⟩, sht_lang] (fun _ h => ∀ ll ∈ {l | Sum.inl l ∈ s''}, ∃ pp, Sum.inr pp ∈ s' ∧ h ⟨2, Sum.inl ll ⟩= h ⟨1, Sum.inr pp⟩))
--   ==> LGTM.wp [sht_prog, sht_lang] (fun _ h => ∀ ll ∈ {l | Sum.inl l ∈ s''}, ∃ pp, Sum.inr pp ∈ s' ∧ h ⟨2, Sum.inl ll ⟩= h ⟨1, Sum.inr pp⟩) := by
--   move=> ps ls subst disj
--   simp
--   unfold LGTM.wp hwp heval heval_nonrel
--   intro x; dsimp;
--   intro hs
--   rcases hs with ⟨hh, hh1, ⟨⟨hh2, ⟨hh21, hh22⟩⟩, ⟨ha, ⟨ha1, ha2⟩⟩, hb, hc ⟩⟩
--   have hQ' := ha ∪_⟪1, s'⟫ hh2
  -- use hQ'
  -- sorry
  -- constructor
  -- · intro a ha
  --   split_ifs with h
  --   · specialize pre1 a (by sorry)

  -- · intro hv
  --   have subset : (⟪1, s'⟫ ∪ sht_lang.s) ⊆ (sht_prog.s ∪ sht_lang.s) := by
  --     calc
  --       ⟪1, s'⟫ ∪ sht_lang.s = ⟪1, (s' : Set (α ⊕ β))⟫ ∪ sht_lang.s := rfl
  --     _ ⊆ ⟪1, s⟫ ∪ sht_lang.s := by
  --       apply Set.union_subset_union_left
  --       have subset2 : s' ⊆ s → ⟪1,s'⟫ ⊆ ⟪1,s⟫ := by sorry
  --       apply subset2
  --       exact subst
  --     _ = sht_prog.s ∪ sht_lang.s := by
  --       rw [← sht_prog.s = ⟪1, s⟫] at *
  --       rfl


  -- have Qq  := fun (pp : Labeled (α ⊕ β)) (ll : (α ⊕ β)) (h : hheap (Labeled (α ⊕ β))) => h ⟨1, ll⟩ = h ⟨2, pp.val⟩
  -- apply shts_weaken_aux (shts := [sht_prog, sht_lang]) (shts' := [⟨⟪1, s'⟫, sht_prog.ht⟩, sht_lang]) (L := {l | Sum.inl l ∈ s''})


#print yfocus_set_lemma
#print yfocus_set_lemma
#check hhProp α
#check qstar
#check hhstar
#check hqstar

def whqstar {A} (q : A → @hhProp α) (h : @hhProp α) : A → @hhProp α :=
  fun x => hhstar (q x) h

/- not used yet -/
def weird_hstar (Q : @hval α-> @hhProp α) (H : @hhProp α) :
  (Q ∗ H) = whqstar Q H:= by
  aesop

def well_formed_focus_lemma (idx : ℕ) (l : LabType) (s' s : Set α) (shts : LGTM.SHTs (Labeled α)) (x : hval αˡ) (H' : hval αˡ → hhProp αˡ) (H : hhProp αˡ) {pi : idx < shts.length} :
  shts[idx].s = ⟪l, s⟫ ->
  (shts.Pairwise (Disjoint ·.s ·.s)) ->
  (Disjoint (LGTM.SHTs.set (List.eraseIdx shts idx)) ⟪l, Set.univ⟫) ->
  H' = (fun x => H )->
  R ==> LGTM.wp [⟨⟪l, s \ s'⟫, shts[idx].ht⟩] H' ∧
  (H ==> LGTM.wp ((shts.eraseIdx (idx)).insertIdx idx ⟨⟪l, s ∩ s'⟫,shts[idx].ht⟩) Q) ->
  R ==> LGTM.wp shts Q := by
  unfold LGTM.wp
  move=> shtsset disj1 disj2 HH upper
  rcases upper with ⟨up1, up2⟩
  sorry

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
  set B' : hval (α ⊕ β)ˡ → hhProp (α ⊕ β)ˡ:= fun _ => fun h ↦ ∀ a, a ∈ ⟪0, s \ s'⟫ ∧ h a ≠ ∅
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
  apply well_formed_focus_lemma (idx := 0) (l := 0) (shts := [sht_prog, sht_lang]) (s' := s') (s := s) (H' := B' ∗ H₂) (H := H₂ ∗ B) (R := H₁ ∗ H₂) (Q := Qp1 ∗ B)=>//
  · simp_all; rw [@disjoint_label_set]; aesop
  · apply swap_hqstar=>//
  · constructor
    · have part11 := (hhimpl_frame_l (hH₃ := H₂) (hH₁ := H₁) (hH₂ := LGTM.wp [{ s := ⟪0, s \ s'⟫, ht := sht_prog.ht }] B'))
      specialize part11 part1
      simp
      apply hhimpl_trans (h₁ := H₁ ∗ H₂ ) ( h₂ := ((LGTM.wp [{ s := ⟪0, s \ s'⟫, ht := sht_prog.ht }] B') ∗ H₂)) (h₃ := LGTM.wp [{ s := ⟪0, s \ s'⟫, ht := sht_prog.ht }] (B' ∗ H₂))
      · exact part11
      · have form1 := LGTM.wp_frame (Q := B') (H := H₂) (sht := [{ s := ⟪0, s \ s'⟫, ht := sht_prog.ht }])
        convert form1
    · intro x
      have part21 := (hhimpl_frame_l (hH₃ := B) (hH₁ := H₂) (hH₂ := LGTM.wp [{ s := ⟪0, s'⟫, ht := sht_prog.ht }, sht_lang] Qp1))
      specialize part21 part2
      simp
      apply hhimpl_trans (h₁ := H₂ ∗ B) ( h₂ := LGTM.wp [{ s := ⟪0, s'⟫, ht := sht_prog.ht }, sht_lang] Qp1 ∗ B) (h₃ := LGTM.wp [{ s := ⟪0, s ∩ s'⟫, ht := sht_prog.ht }, sht_lang] (Qp1 ∗ B))
      · exact part21
      · have form2 := LGTM.wp_frame ( Q := Qp1) (H := B) (sht := [{ s := ⟪0, s'⟫, ht := sht_prog.ht }, sht_lang])
        convert form2
        aesop

  /- if use yfocus_set_lemma -/
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
  --   · sorry
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
  --     sorry
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
