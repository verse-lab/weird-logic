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

#print lang_c


/- Exampel Grammar L1 -/
/-  L ::= S1
    S1 ::= S2 ; S1 | ε
    S2 ::= x := x + 1 -/

def S2 : T := [lang| x := x + 1]
def S3 : T := [lang| x := x + 2]
def S1 : N := "S1"
def S4 : N := "S4"
def L : N := "L"

def prod1 : production :=
  (Finmap.singleton S1 [symbol.seq (symbol.terminal S2) (symbol.nonterminal S1), symbol.eps]).insert
  L [symbol.nonterminal S1]

def prod2 : production :=
  (Finmap.singleton S1 [(symbol.terminal S2), symbol.seq (symbol.terminal S2) (symbol.terminal S1)]).insert
  L [symbol.nonterminal S1]

def prod3 : production :=
  ((Finmap.singleton S1 [symbol.seq (symbol.terminal S2) (symbol.terminal S1), symbol.seq (symbol.terminal S4) (symbol.terminal S2)]
  ).insert
  L [symbol.nonterminal S1]
  ).insert S4 [(symbol.terminal S2),(symbol.terminal S2)]

def L1 : ctx_grammar :=
  { nonterminals := {S1, L, S4},
    -- terminals := {S2, S3},
    prods := prod1,
    start := symbol.nonterminal L }

#reduce expandSymbol L1 10 L1.start
#eval (expandSymbol L1 10 L1.start).length

end WeirdLogic
