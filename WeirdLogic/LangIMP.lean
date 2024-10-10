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

inductive IMPExpr : Type where
  | str  : String → IMPExpr
  | b  : Bool → IMPExpr
  | n  : ℕ → IMPExpr
  | bin  : BinOp → IMPExpr → IMPExpr → IMPExpr

open BinOp IMPExpr

inductive Val : Type where
  | bool  : Bool → Val
  | nat : ℕ → Val

-- abbrev Val := ℕ -- simper version
abbrev State := String → Val
abbrev Heap := State

def empty : State := fun _ => Val.nat 0

def State.update (name : String) (val : Val) (s : State) : State :=
  fun name' ↦ if name' = name then val else s name'

macro s:term "[" name:term "↦" val:term "]" : term =>
  `(State.update $name $val $s)

def bool_to_nat (b : Bool) : ℕ :=
  match b with
  | true => 1
  | false => 0

def nat_to_bool (n : ℕ ) : Bool :=
 match n with
 | 0 => false
 | _ => true

def eval_to_nat (st : State)(e : IMPExpr) : Nat :=
 match e with
 | str v => let val := st v
        match val with
        | Val.bool valb=> bool_to_nat valb
        | Val.nat valn => valn
 | b s => bool_to_nat s
 | n s => s
 | bin binop e₁ e₂ => match binop with
      | add => eval_to_nat st e₁ + eval_to_nat st e₂
      | mul => eval_to_nat st e₁ * eval_to_nat st e₂
      | lt => let ev1 := eval_to_nat st e₁
              let ev2 := eval_to_nat st e₂
              let ev := decide (ev1 < ev2)
              bool_to_nat ev
      | eq => let ev := eval_to_nat st e₁ == eval_to_nat st e₂
              bool_to_nat ev
      | band => let ev1 := eval_to_nat st e₁
                let ev2 := eval_to_nat st e₂
              match ev1, ev2 with
                | 0, _ => 0
                | _, 0 => 0
                | _, _ => 1
      | bor => let ev1 := eval_to_nat st e₁
               let ev2 := eval_to_nat st e₂
              match ev1, ev2 with
                | 0, 0 => 0
                | _, _ => 1

def eval_to_bool (st : State) (e : IMPExpr) : Bool :=
 match e with
 | str v => let val := st v
        match val with
        | Val.bool valb=> valb
        | Val.nat valn => nat_to_bool valn
 | b s => s
 | n s => nat_to_bool s
 | bin binop e₁ e₂ => match binop with
      | add => let ev := eval_to_nat st e₁ + eval_to_nat st e₂
               nat_to_bool ev
      | mul => let ev := eval_to_nat st e₁ * eval_to_nat st e₂
               nat_to_bool ev
      | lt => decide (eval_to_nat st e₁ < eval_to_nat st e₂)
      | eq => eval_to_nat st e₁ == eval_to_nat st e₂
      | band => decide (eval_to_bool st e₁ ∧ eval_to_bool st e₂)
      | bor => decide (eval_to_bool st e₁ ∨ eval_to_bool st e₂)

def eval_to_val (st : State) (e : IMPExpr) : Val :=
 match e with
 | str v => st v
 | b s => Val.bool s
 | n s => Val.nat s
 | bin binop e₁ e₂ => match binop with
      | add => let ev := eval_to_nat st e₁ + eval_to_nat st e₂
               Val.nat ev
      | mul => let ev := eval_to_nat st e₁ * eval_to_nat st e₂
               Val.nat ev
      | lt => Val.bool (decide (eval_to_nat st e₁ < eval_to_nat st e₂))
      | eq => Val.bool (eval_to_nat st e₁ == eval_to_nat st e₂)
      | band => Val.bool (decide (eval_to_bool st e₁ ∧ eval_to_bool st e₂))
      | bor => Val.bool (decide (eval_to_bool st e₁ ∨ eval_to_bool st e₂))

namespace Imp

declare_syntax_cat imp

syntax num : imp
syntax str : imp
syntax:60 imp:60 "+" imp:61 : imp
syntax:60 imp:60 "-" imp:61 : imp
syntax:70 imp:70 "*" imp:71 : imp
syntax:50 imp:50 "=" imp:50 : imp
syntax:50 imp:50 "<" imp:50 : imp
syntax:30 imp:30 "&&" imp:31 : imp
syntax:30 imp:30 "||" imp:31 : imp
-- syntax:50 imp:50 "!=" imp:50 : imp
-- syntax:40 "!" imp:40 : imp

syntax "true" : imp
syntax "false" : imp
syntax "(" imp ")" : imp
syntax "<{" imp "}>" : term
syntax ident : imp
syntax "<[" term "]>" : imp
syntax "true" : term
syntax "false" : term

macro_rules
  | `(term|true) => `(Bool.true)
  | `(term|false) => `(Bool.false)
  | `(term|<{$x}>) => `(imp|$x)
  | `(imp|$n:num) => `(IMPExpr.n $n)
  | `(imp|$s:str) => `(IMPExpr.str $s)
  | `(imp|$x + $y) => `(IMPExpr.bin BinOp.add <{$x}> <{$y}>)
  | `(imp|$x * $y) => `(IMPExpr.bin BinOp.mul <{$x}> <{$y}>)
  | `(imp|true) => `(IMPExpr.b.true)
  | `(imp|false) => `(IMPExpr.b.true)
  | `(imp|$x = $y) => `(IMPExpr.bin BinOp.eq <{$x}> <{$y}>)
  | `(imp|$x < $y) => `(IMPExpr.bin BinOp.lt <{$x}> <{$y}>)
  | `(imp|$x && $y) => `(IMPExpr.bin BinOp.and <{$x}> <{$y}>)
  | `(imp|$x || $y) => `(IMPExpr.bin BinOp.or <{$x}> <{$y}>)
  | `(imp|($x)) => `(<{$x}>)
  | `(imp|$x:ident) => `(IMPExpr.str $(Lean.quote (toString x.getId)))
  | `(imp|<[$t:term]>) => pure t
  -- | `(imp|$x != $y) => `(b_neq <{$x}> <{$y}>)
  -- | `(imp|$x - $y) => `(a_minus <{$x}> <{$y}>)
  -- | `(imp|!$x) => `(b_not <{$x}>)

abbrev w := "w"
abbrev x := "x"
abbrev y := "y"
abbrev z := "z"

example : eval_to_val (State.update x (Val.nat 5) empty)
    <{3 + x * 2}>
    -- (IMPExpr.bin add (n 3) (IMPExpr.bin mul (str x) (n 2)))
    = Val.nat 13 := by
  apply sorry

inductive Stmt : Type where
  | skip       : Stmt
  | assign     : String → (State → Val) → Stmt
  | seq        : Stmt → Stmt → Stmt
  | output     : IMPExpr → Stmt
  | ifThenElse : (State → Prop) → Stmt → Stmt → Stmt
  | whileDo    : (State → Prop) → Stmt → Stmt
infixr:90 "; " => Stmt.seq

open Stmt

-- syntax "skip" : imp
-- syntax:21 "output" imp:21: imp
-- syntax:21 imp:20 ":=" imp:21 : imp
-- syntax:20 imp:20 ";" imp:21 : imp
-- syntax:21 "if" imp:20 "then" imp:20 "else" imp:20 "end" : imp
-- syntax:21 "while" imp:20 "do" imp:20 "end" : imp

-- macro_rules
--   | `(imp|skip) => `(Stmt.skip)
--   | `(imp|output $e:imp) => `(Stmt.output <{$e}>)
--   | `(imp|$x:str := $y) => `(Stmt.assign $x <{$y}>)
--   | `(imp|$c1 ; $c2) => `(Stmt.seq <{$c1}> <{$c2}>)
--   | `(imp|if $b then $c1 else $c2 end) => `(Stmt.ifThenElse <{$b}> <{$c1}> <{$c2}>)
--   | `(imp|while $b do $c end) => `(Stmt.whileDo <{$b}> <{$c}>)

-- def skipstmt : Stmt := <{ skip }>
-- def outputstmt : Stmt := <{ output x }>

def val_to_bool (v : Val) : Bool :=
  match v with
  | Val.bool bb => bb
  | Val.nat bb => nat_to_bool bb

def val_to_nat (v : Val) : ℕ :=
  match v with
  | Val.nat bb => bb
  | Val.bool bb=> bool_to_nat bb

def sillyLoop : Stmt :=
  Stmt.whileDo (fun s ↦ val_to_nat (s "x") > val_to_nat (s "y"))
    (Stmt.skip;
     Stmt.assign "x" (fun s ↦ Val.nat (val_to_nat (s "x") - 1)))

-- def factorial: Stmt :=
--   <{ z := 0 empty;
--      y := 1 empty;
--      while z < x do
--        y := y * z s;
--        z := (z + 1)
--      end }>

-- inductive Trace : Type where
-- | empty : Trace          -- empty trace
-- | cons  : Val → Trace    -- trace is a sequence of output values


inductive Context : Type where
| hole : Context
| seqFront : Context → Stmt → Context
| seqBack : Stmt → Context → Context
| ifThenElseTrue : (State → Prop) → Context → Stmt → Context
| ifThenElseFalse : (State → Prop) → Stmt → Context → Context
| whileDo    : (State → Prop) → Stmt → Context

inductive BigStep : Stmt × State → State → Prop where
  | skip (s) :
    BigStep (Stmt.skip, s) s
  | assign (x a s) :
    BigStep (Stmt.assign x a, s) (s[x ↦ a s])
  | seq (S T s t u) (hS : BigStep (S, s) t)
      (hT : BigStep (T, t) u) :
    BigStep (S; T, s) u
  | if_true (B S T s t) (hcond : B s)
      (hbody : BigStep (S, s) t) :
    BigStep (Stmt.ifThenElse B S T, s) t
  | if_false (B S T s t) (hcond : ¬ B s)
      (hbody : BigStep (T, s) t) :
    BigStep (Stmt.ifThenElse B S T, s) t
  | while_true (B S s t u) (hcond : B s)
      (hbody : BigStep (S, s) t)
      (hrest : BigStep (Stmt.whileDo B S, t) u) :
    BigStep (Stmt.whileDo B S, s) u
  | while_false (B S s) (hcond : ¬ B s) :
    BigStep (Stmt.whileDo B S, s) s

infix:110 " ⟹ " => BigStep

def PartialHoare (P : State → Prop) (S : Stmt)
    (Q : State → Prop) : Prop :=
  ∀ (s:State) (t:State), P s → (S, s) ⟹ t → Q t

macro "{*" P:term " *} " "(" S:term ")" " {* " Q:term " *}" : term =>
  `(PartialHoare $P $S $Q)

theorem skip_intro {P} :
       {* P *} (Stmt.skip) {* P *} :=
       by sorry

namespace PartialHoare
