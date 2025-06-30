import Mathlib.Data.Finmap
import Mathlib.Data.Real.Basic

import WeirdLogic.Util
import WeirdLogic.Heap
import WeirdLogic.Lang


open Classical

namespace WeirdLogic

/- =========================== Attack Grammar =========================== -/

inductive Gram : Type
  | nonterminal : String → Gram
  | terminal : trm → Gram
  | seq : Gram → Gram → Gram
  | choice : Gram → Gram → Gram
  | ref : Gram → Gram → Gram
  | eps : Gram

-- L → S1
def L : Gram :=
  Gram.nonterminal "S1"

-- S1 → (x = x + 1 ; S1) | ε
def S1 : Gram :=
  Gram.choice
    (Gram.seq
      (Gram.terminal (trm.trm_ref "x" (trm.trm_app (trm.trm_app prim.val_add (trm.trm_var "x")) (trm.trm_val 1)) (trm.trm_val 0) ))
      (Gram.nonterminal "S1")
    )
    Gram.eps

-- macro "gram_def" n:ident ":=" g:gram : command => do
--   `(def $n:ident : val := [gram| $g])

declare_syntax_cat gram

syntax str : gram
syntax gram " + " gram : gram
syntax "ε" : gram
syntax "[gram| " gram "]" : gram


-- macro_rules
--   | `([gram| ε]) => `(Gram.eps)
--   | `([gram| $g1 + $g2]) =>  `( choice [gram| $g1] [gram| $g2])
--   | `([gram| $g1 → $g2]) =>  `( eq [gram| $g1] [gram| $g2])



end WeirdLogic
