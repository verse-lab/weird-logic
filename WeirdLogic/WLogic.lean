
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


/- s' is the part to keep (P' in weaken rule) -/
lemma weird_weaken_lemma  (s' s : Set (α ⊕ β)) (shts : LGTM.SHTs (Labeled (α ⊕ β))) (h: shts.length = 2) {pi : idx < shts.length}
  [FindLabel l shts idx pi] :
  shts[idx].s = ⟪1, s⟫ ->
  idx = 0 ∧ shts[1].s = ⟪ 2, s''⟫ ->
  (shts.Pairwise (Disjoint ·.s ·.s)) ->
  LGTM.wp ((shts.eraseIdx idx).insertIdx idx ⟨⟪1, s ∩ s'⟫,shts[idx].ht⟩) (fun _ h => ∀ ll , ∃ pp, Sum.inr pp ∈ s' ∧ h ⟨1, Sum.inl ll ⟩= h ⟨2, Sum.inr pp⟩)
  ==> LGTM.wp shts (fun _ h => ∀ ll , ∃ pp, Sum.inr pp ∈ s ∧ h ⟨1, Sum.inl ll ⟩= h ⟨2, Sum.inr pp⟩) := by
  move=> label h1 h2;
  move=> *;
  apply hhimpl_trans_r=>//
  apply yfocus_set_lemma_aux=> //;
  move =>*;
  {sorry}
  sorry

lemma weird_grmdisj_lemma (s' s : Set (α ⊕ β)) (shts : LGTM.SHTs (Labeled (α ⊕ β))) (h: shts.length = 2) {pi : idx < shts.length}
  [FindLabel l shts idx pi] :
  shts[idx].s = ⟪2, s⟫ ->
  idx = 1 ∧ shts[0].s = ⟪ 1, s''⟫ ->
  (shts.Pairwise (Disjoint ·.s ·.s)) ->
  H ==> LGTM.wp ((shts.eraseIdx idx).insertIdx idx ⟨⟪ l, s'⟫, shts[idx].ht⟩ ) (fun _ h => ∀ ll, ∃ pp, Sum.inl ll ∈ s' ∧ h ⟨1, Sum.inl ll ⟩= h ⟨2, Sum.inr pp⟩) ->
  H ==> LGTM.wp ((shts.eraseIdx idx).insertIdx idx ⟨⟪ l, s \ s'⟫, shts[idx].ht⟩) (fun _ h => ∀ ll, ∃ pp, Sum.inl ll ∈ s \ s' ∧ h ⟨1, Sum.inl ll ⟩= h ⟨2, Sum.inr pp⟩) ->
  H ==> LGTM.wp shts Q := by
  move=> *; apply hhimpl_trans_r; apply yfocus_set_lemma_aux=> //;
  simp [Disjoint]; move => *; sorry
  sorry

#check hhimpl_trans_r
#check if_pos

lemma weird_lang_lemma ( s : Set (α ⊕ β)) (shts : LGTM.SHTs (Labeled (α ⊕ β))) (h: shts.length = 2) (tl : α) {pi : idx < shts.length}
  [FindLabel l shts idx pi] :
  shts[idx].s = ⟪1, s⟫ ->
  idx = 0 ∧ shts[1].s = ⟪ 2, s'⟫ ->
  {⟨1, (Sum.inl tl)⟩} = shts[0].s ->
  LGTM.wp shts (fun _ h => ∃ pp, h ⟨1, Sum.inl tl ⟩= h ⟨2, Sum.inr pp⟩)
  ==> LGTM.wp shts (fun _ h => ∀ ll , ∃ pp, h ⟨1, Sum.inl ll ⟩= h ⟨2, Sum.inr pp⟩) := by
  sorry

lemma weird_payload_lemma ( s : Set (α ⊕ β)) (shts : LGTM.SHTs (Labeled (α ⊕ β))) (h: shts.length = 2) (tp : β) (tl : α) :
  ⟨2, (Sum.inr pp)⟩ ∈ shts.set ->
  LGTM.wp shts (fun _ h => h ⟨1, Sum.inl tl ⟩= h ⟨2, Sum.inr tp⟩)
  ==> LGTM.wp shts (fun _ h => ∃ pp, h ⟨1, Sum.inl tl ⟩= h ⟨2, Sum.inr pp⟩) := by
  sorry

lemma weird_seqleft_lemma ( s : Set (α ⊕ β)) (shts : LGTM.SHTs (Labeled (α ⊕ β))) (h: shts.length = 2):
  True := by
  simp



end WTriple
