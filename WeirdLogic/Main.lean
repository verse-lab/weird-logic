import Lgtm.Hyper.ProofMode
import Lgtm.Hyper.ArraysFun
import Lgtm.Unary.Lang

import WeirdLogic.Gram

open Unary prim val trm

namespace WeirdLogic

/- Using macro lang_def to define a language
macro "lang_def" n:ident ":=" l:lang : command => do
  `(def $n:ident : trm := [lang| $l])

lang_def C :=
  fun ⸨x:Val⸩ ⸨a:Val⸩ =>
    /- need to define choose a-/
    if a = true then
      x := x + 1
    else
      x := x +2
-/

/- Example Program -/

def lang_c := [lang|
  fun ⸨x:Val⸩ ⸨a:Val⸩ =>
    /- need to define choose a-/
    if a = true then
      x := x + 1
    else
      x := x +2]


/- Exampel Grammar L1 -/
/-  L ::= S1
    S1 ::= S2 ; S1 | ε
    S2 ::= x := x + 1 -/

def S2 : T := [lang| x := x + 1]
def S1 : N := "S1"
def L : N := "L"

def prod1 : production :=
  {
    l := symbol.nonterminal S1,
    r := [symbol.seq (symbol.terminal S2) (symbol.nonterminal S1), symbol.eps] }

def prod2 : production :=
  {
    l := symbol.nonterminal L,
    r := [symbol.nonterminal S1] }

def L1 : ctx_grammar :=
  { nonterminals := {S1, L},
    terminals := {S2}
    prods := [prod1],
    start := L }

end WeirdLogic
