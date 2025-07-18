
import Lgtm.Unary.Lang
import Lgtm.Hyper.HProp
import Lgtm.Hyper.YSimp
import Lgtm.Hyper.YChange
import Lgtm.Hyper.SepLog

import WeirdLogic.Gram

open Lean Lean.Expr Lean.Meta Qq
open Lean Elab Command Term Meta Tactic

section WTriple

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

def check_payload (α : Syntax) (v : List var): Bool :=
  match α with
  | `(Bool) =>
    match v with
    | s::_ => true
    | _ => false
  | `(ℕ) =>
    match v with
    | s::_ => true
    | _ => false
  | `(Bool × $β) =>
    match v with
    | s::xs => check_payload β xs
    | _ => false
  | `(ℕ × $β) =>
    match v with
    | s::xs => check_payload β xs
    | _ => false
  | _ => false

/- do substitube now, add choose in while later -/
def render_C (C : trm) (p : payload_map ) (v : List var): trm :=
  v.foldl ( λ C svar =>
    let sval := p.lookup svar |>.getD (val.val_int 0)
    subst svar (trm.trm_val sval) C
  ) C

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

end WTriple
