
import Lgtm.Unary.Lang
import Lgtm.Hyper.HProp
import Lgtm.Hyper.YSimp
import Lgtm.Hyper.YChange
import Lgtm.Hyper.SepLog
import Lgtm.Hyper.WP
import Lgtm.Hyper.ProofMode

import WeirdLogic.Gram

open Lean Lean.Expr Lean.Meta Qq
open Lean Elab Command Term Meta Tactic


section WTriple

local macro "LabType" : term => `(ℕ)
variable {α : Type} (s : Set α)

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

/- Following is test examples -/
def S2 : T := [lang| x := x + 1]
def S1 : N := "S1"

def prod1 : production :=
  Finmap.singleton S1 [symbol.terminal S2]

def L : cfg :=
  { nonterminals := {S1},
    prods := prod1,
    start := symbol.nonterminal S1 }

#check lgtm_match [lang| x := x + 1] L

/- Rules -/
-- lemma wtriple_grmdisj (α : Type) (t : hwtrm) (Q : hval → hhProp) :
--   Disjoint t t' →
--   LGTM.wp t Q ==> LGTM.wp t' Q:= by sorry

#check LGTM.wp
#check FindLabel
#check yfocus_set_lemma

/- s' is the part want to keep -/
lemma weird_weaken_lemma (l : LabType) (s' s : Set α) (shts : LGTM.SHTs (Labeled α)) {pi : idx < shts.length}
  [FindLabel l shts idx pi] :
  shts[idx].s = ⟪l, s⟫ ->
  shts.length = 2 ∧ l=1 ->
  (shts.Pairwise (Disjoint ·.s ·.s)) ->
  H ==> LGTM.wp ((shts.eraseIdx idx).insertIdx idx ⟨⟪l, s ∩ s'⟫,shts[idx].ht⟩) Q ->
  H ==> LGTM.wp shts Q := by
  move=> *; apply hhimpl_trans_r;
  dsimp=> //
  dsimp [LGTM.wp]
  sorry

lemma weird_grmdisj_lemma (l : LabType) (s' s : Set α) (shts : LGTM.SHTs (Labeled α)) {pi : idx < shts.length}
  [FindLabel l shts idx pi] :
  shts[idx].s = ⟪l, s⟫ ->
  shts.length = 2 ∧ l=2 ->
  (shts.Pairwise (Disjoint ·.s ·.s)) ->
  H ==> LGTM.wp ((shts.eraseIdx idx).insertIdx idx ⟨⟪ l, s'⟫, shts[idx].ht⟩ ) Q ->
  H ==> LGTM.wp ((shts.eraseIdx idx).insertIdx idx ⟨⟪ l, s \ s'⟫, shts[idx].ht⟩) Q ->
  H ==> LGTM.wp shts Q := by
  move=> *; apply hhimpl_trans_r; apply yfocus_set_lemma_aux=> //;
  simp [Disjoint]; move => *; sorry
  sorry

-- lemma weird_lang_lemma ( s : Set α) (shts : LGTM.SHTs (Labeled α)):
--   shts.length =2 ->
--   shts[1].s = ⟪l, s⟫ ->

-- lemma weird_payload_lemma ( s : Set α) (shts : LGTM.SHTs (Labeled α)):
--   shts.length =2 ->

-- lemma weird_if_true_lemma (shts : LGTM.SHTs (Labeled α)):
--   shts.length = 2 ->
--   shts.


end WTriple
