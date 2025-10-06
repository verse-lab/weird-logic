import Mathlib.Data.Finmap
import Mathlib.Data.Real.Basic
import Mathlib.Computability.ContextFreeGrammar

import Lgtm.Unary.Lang
import Lgtm.Common.Util
import Lgtm.Common.Heap

import Lean

open Lean Elab Tactic Meta

-- import WeirdLogic.Util
-- import WeirdLogic.Heap

-- open Classical
open trm var

/- =========================== Vulnerable Program Language ==================== -/
inductive wtrm : Type where
  | wtrm_basic : trm -> wtrm
  | wtrm_choose : var -> wtrm

syntax "⟦" term "⟧" : lang
macro_rules
  | `([lang| ⟦$t⟧]) => `($t)
/- =========================== Context-Free Grammar =========================== -/

abbrev T := trm
abbrev N := var

inductive symbol : Type where
  | terminal : T → symbol
  | nonterminal : N → symbol
  | eps : symbol
  | seq : symbol → symbol → symbol

abbrev production := Finmap ( λ _ : N ↦ List symbol)

structure cfg where
  nonterminals : Finset N
  -- terminals : Finset T
  prods : production
  start : symbol

partial def expand_cfg (g : cfg) (depth : ℕ ) (s : symbol) : List trm :=
  if decide (depth <= 0) then []
  else
    match s with
    | symbol.terminal t => [t]
    | symbol.nonterminal n =>
      -- if decide (n ∈ g.nonterminals) then
        match g.prods.lookup n with
        | some p =>
          p.flatMap fun re => expand_cfg g (depth - 1) re
        | none => []
      -- else []
    | symbol.eps => []
    | symbol.seq s1 s2 =>
      (expand_cfg g (depth-1) s1).flatMap fun x => (expand_cfg g (depth-1) s2).map (fun y => trm_seq x y)
-- termination_by depth

def check_cfg (g : cfg) (depth : ℕ ) (prog : trm) : Prop :=
  ∃ p ∈ (expand_cfg g depth g.start), eval_like p prog

set_option maxRecDepth 2000
set_option maxHeartbeats 2500000
partial def match_cfg (p : trm) (g : cfg) : Prop :=
  match g.start with
  | symbol.terminal t => p = t
  | symbol.nonterminal n =>
    match g.prods.lookup n with
    | some r =>
      ∃ re ∈ r, match_cfg p { g with start := re }
    | none => False
  | symbol.seq s1 s2 =>
    match p with
    | trm_seq x y =>
      let g1 := { g with start := s1 }
      let g2 := { g with start := s2 }
      match_cfg x g1 ∧ match_cfg y g2
    | _ => False
  | symbol.eps => True

/- =========================== Context-Free Grammar from Mathlib=========================== -/
def expand_trm (t : trm) : List (Symbol T N) :=
  match t with
  | trm_seq t1 t2 => (expand_trm t1) ++ (expand_trm t2)
  | _ => [Symbol.terminal t]

def squeeze_trm (tlist : List trm) : trm :=
  match tlist with
  | x1::x2::xs => trm_seq x1 (squeeze_trm (x2::xs))
  | [x] => x
  | [] => trm.trm_val 0


def trm_to_symbol_list (tlist : List trm) : List (Symbol T N) :=
  match tlist with
  | [] => []
  | x::xs => [Symbol.terminal x] ++ trm_to_symbol_list xs

def symbol_to_trm_list (slist : List (Symbol T N)) : List trm :=
  match slist with
  | [] => []
  | (Symbol.terminal x)::xs => [x] ++ symbol_to_trm_list xs
  | (Symbol.nonterminal _)::xs => symbol_to_trm_list xs

/- =========================== Macros ============================== -/
/- **TODO** Too many bugs, solve later -/
declare_syntax_cat gram
declare_syntax_cat sym
declare_syntax_cat prod

syntax ident : sym
syntax term : sym
syntax var : sym
syntax "ε" : sym
syntax sym " ; " sym : sym
-- syntax gram " ::= " term : gram
-- syntax gram " or " gram : gram
syntax gram " ; " gram : gram
-- syntax "(" gram ")" : gram
-- syntax "(" nonterminals ")" : gram
syntax "[sym| " sym "]" : term
syntax "[prod| " sym "::=" sym* "]" : term

local notation "%" x => (Lean.quote (toString (Lean.Syntax.getId x)))

-- macro_rules
--   | `([sym| $x:var]) => `(symbol.nonterminal $(%x))
--   | `([sym| $t:term]) => `(symbol.terminal trm_var $t)
--   | `([sym| ε]) => `(symbol.eps)
--   | `([sym| $g1:sym ; $g2:sym]) => `(symbol.seq [sym| $g1] [sym| $g2])
--   | `([prod| $l:sym ::= $rr:sym*]) => do
--       let rr <- rr.mapM fun re =>
--         match re with
--         | `([sym| $re:var]) => `(symbol.nonterminal $(%re))
--         | `([sym| $re:term]) => `(symbol.terminal trm_var $re)
--         | _ => Lean.Macro.throwError
--           "Invalid syntax in production: {re}, expected a variable or term"
--       `( production { l:=[sym| $l], r:= rr})

  -- | `([sym| $l $a $p $s]) => `({ nonterminals := $l
  --                                 terminals := $a
  --                                 prods := $p
  --                                 start := $s })
  -- | `([gram| $t:term]) => `(Gram.terminal trm_var $t)
  -- | `([gram| $x ::= $g2:gram]) => `(Gram.ref (Gram.nonterminal $(%x)) [gram| $g2])
  -- | `([gram| $x ::= $t:term]) => `(Gram.ref (Gram.nonterminal $(%x)) (Gram.terminal trm_var $t))
  -- | `([gram| $g1:gram or $g2:gram]) => `(Gram.choice [gram| $g1] [gram| $g2])
  -- | `([gram| $g1 ; $g2]) => `(Gram.seq [gram| $g1] [gram| $g2])
  -- | `([gram| ε]) => `(Gram.eps)
  -- | `([gram| ($g:gram)]) => `([gram| $g])

-- macro "gram_def" n:ident ":=" g:gram : command => do
--   `(def $n:ident : Gram := [gram| $g])
