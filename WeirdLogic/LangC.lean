import Mathlib

open Classical
open Lean -- Meta Elab

set_option autoImplicit false
set_option tactic.hygienic false

inductive BinOp : Type where
| add : BinOp -- +
| mul : BinOp -- ×
| lt  : BinOp -- <
| eq  : BinOp -- ==
| band : BinOp -- ∧
| bor  : BinOp -- ∨

inductive CExpr : Type where
  | str  : String → CExpr
  | i  : ℕ → CExpr
  | null : CExpr
  | ptr  : ℕ → CExpr -- *e
  | addr : String → CExpr -- &l^v
  | bin  : BinOp → CExpr → CExpr → CExpr

open BinOp CExpr

-- abbrev Val := ℕ -- simper version
abbrev State := String → ℕ
abbrev Heap := State

def empty : State := fun _ => 0

def State.update (name : String) (val : ℕ) (s : State) : State :=
  fun name' ↦ if name' = name then val else s name'

macro s:term "[" name:term "↦" val:term "]" : term =>
  `(State.update $name $val $s)

def eval_cexpr (st : State)(e : CExpr) : Option Nat :=
 match e with
 | str v => none
 | i idx => idx
 | null => none
 | ptr p => p
 | addr address => none
 | bin binop e₁ e₂ => none -- TODO


inductive Stmt : Type where
  | skip       : Stmt
  | assign     : String → (State → ℕ) → Stmt
  | seq        : Stmt → Stmt → Stmt
  | output     : CExpr → Stmt
  | ifThenElse : (State → Prop) → Stmt → Stmt → Stmt
  | whileDo    : (State → Prop) → Stmt → Stmt
infixr:90 "; " => Stmt.seq

open Stmt
