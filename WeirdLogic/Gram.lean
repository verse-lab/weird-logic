import Mathlib.Data.Finmap
import Mathlib.Data.Real.Basic

import Lgtm.Unary.Lang
import Lgtm.Common.Util
import Lgtm.Common.Heap

import Lean

open Lean Elab Tactic Meta

-- import WeirdLogic.Util
-- import WeirdLogic.Heap

-- open Classical

/- =========================== Context-Free Grammar =========================== -/
open trm var

abbrev T := trm
abbrev N := var

inductive symbol : Type where
  | terminal : T → symbol
  | nonterminal : N → symbol
  | eps : symbol
  | seq : symbol → symbol → symbol


-- def eval_symbol : symbol → trm
--   | symbol.terminal t => t
--   | symbol.nonterminal n => trm_var n -- not true
--   -- | symbol.eps => none
--   | symbol.seq s1 s2 => trm_seq (eval_symbol s1) (eval_symbol s2)

abbrev production := Finmap ( λ _ : N ↦ List symbol)

-- structure production where
--   l : symbol
--   r : List symbol

structure ctx_grammar where
  nonterminals : Finset N
  -- terminals : Finset T
  prods : production
  start : symbol

partial def expandSymbol (g : ctx_grammar) (depth : ℕ ) (s : symbol) : List trm :=
  if decide (depth <= 0) then []
  else
    match s with
    | symbol.terminal t => [t]
    | symbol.nonterminal n =>
      -- if decide (n ∈ g.nonterminals) then
        match g.prods.lookup n with
        | some p =>
          p.flatMap fun re => expandSymbol g (depth - 1) re
        | none => []
      -- else []
    | symbol.eps => []
    | symbol.seq s1 s2 =>
      (expandSymbol g (depth-1) s1).flatMap fun x => (expandSymbol g (depth-1) s2).map (fun y => trm_seq x y)
-- termination_by depth

def check_cfg (g : ctx_grammar) (depth : ℕ ) (prog : trm) : Prop :=
  ∃ p ∈ (expandSymbol g depth g.start), eval_like p prog


/- **TODO** Macros. Too many bugs, solve later -/
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
