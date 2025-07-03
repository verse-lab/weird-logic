import Mathlib.Data.Finmap
import Mathlib.Data.Real.Basic

import Lgtm.Unary.Lang

-- import WeirdLogic.Util
-- import WeirdLogic.Heap


open Classical

/- =========================== Context-Free Grammar =========================== -/
open trm var

abbrev T := trm
abbrev N := var

inductive symbol : Type where
  | terminal : T → symbol
  | nonterminal : N → symbol
  | eps : symbol
  -- | choice : List symbol → symbol
  | seq : symbol → symbol → symbol

structure production where
  l : symbol
  r : List symbol

structure ctx_grammar where
  nonterminals : Set N
  terminals : Set T
  prods : List production
  start : N

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

/- **TODO** Macros. Too many bugs, solve later -/
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
