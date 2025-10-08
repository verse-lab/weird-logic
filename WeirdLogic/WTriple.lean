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

namespace WeirdLogic

variable {α : Type} (s : Set α)

-- local notation "htrm" => htrm α
-- local notation "hval" => hval α
-- local notation "hhProp" => hhProp α

local macro "LabType" : term => `(ℕ)

def hgram (α : Type) := α -> trm

/- ==================== Payload ==================== -/

abbrev payload := ℤ

inductive payload_base : Type where
  | pld_bool : Bool → payload_base
  | pld_nat : ℕ → payload_base

inductive payload' : Type where
  | pld_nil : payload'
  | pld_cons : payload_base → payload' → payload'

abbrev index' := trm ⊕ payload'
abbrev index_set := @Set.univ (trm ⊕ payload')ˡ

example : payload' :=
  payload'.pld_cons (payload_base.pld_nat 3) (payload'.pld_cons (payload_base.pld_bool true) payload'.pld_nil)



-- def hwtrm (α : Type) := α -> trm /- α is payload later-/

-- local notation "hwtrm" => hwtrm α

-- def payload_to_list (p : payload) : List val :=
--   match p with
--   | payload.pld_nil => []
--   | payload.pld_cons b p' =>
--     match b with
--     | payload_base.pld_bool b => [val.val_bool b] ++ payload_to_list p'
--     | payload_base.pld_nat n => [val.val_int n] ++ payload_to_list p'

abbrev payload_map := Finmap ( λ _ : var ↦ val)

/- ==================== Payload and Language Mapping Functions ==================== -/

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

namespace WeirdLogic
