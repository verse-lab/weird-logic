import Lgtm.Hyper.ProofMode
import Lgtm.Hyper.ArraysFun
import Lgtm.Unary.Lang

import Lgtm.Experiments.HyperCommon

import WeirdLogic.Gram
import WeirdLogic.WLogic
import WeirdLogic.Util

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

/- Exampel 1 -/
def lang_c1 := [lang|
  fun ⸨x:Val⸩ ⸨a:Val⸩ =>
    /- need to define choose a-/
    if a > 0 then
      x := x + 1
    else
      x := x +2
]
#print lang_c1

/-  L ::= S1
    S1 ::= S2 | S3
    S2 ::= x := x + 1
    S3 ::= x := x + 2 -/

def S2 : T := [lang| x := x + 1]
def S3 : T := [lang| x := x + 2]
def S1 : N := "S1"

def prod1 : production :=
  Finmap.singleton S1 [(symbol.terminal S2), (symbol.terminal S3)]

def L1 : cfg :=
  { nonterminals := {S1},
    prods := prod1,
    start := symbol.nonterminal S1 }

#check lgtm_match [lang| x := x + 1] L1

def svar_list : List var := ["a"]

abbrev c1_index := trm ⊕ List ℕ
def lang_index : Set (trm ⊕ List ℕ ):=
  {l:trm ⊕ List ℕ |
    match l with
    | Sum.inl t => lgtm_match t L1
    | Sum.inr _ => False}

#check lang_index

def pay_index : Set (trm ⊕ List ℕ) :=
  {p:trm ⊕ List ℕ |
  match p with
    | Sum.inl _ => False
    | Sum.inr _ => True
  }

def lang_c1_set := [lang|
  fun ⸨x:Val⸩ ⸨i:Val⸩ =>
    i
]

variable (N: ℕ)

def lang_render (p : trm ⊕ List ℕ) (l : trm) (svar : List var): trm :=
  render_C' l (Sum.getRight! p) svar

def origin_render (l : trm ⊕ List ℕ ) : trm :=
  Sum.getLeft! l

-- def origin_render ()
def origin_c1_set := [lang|
  fun ⸨p:Val⸩ =>
    p
]

#check lang_c1_set

lemma example1_spec (f : ℤ -> val):
  { ⊤ }
  [1| l in lang_index  => ⟦origin_render l.val ⟧]
  [1| p in pay_index => ⟦lang_render p.val lang_c1 svar_list⟧]
  { v,
    fun h => ∀ l ∈ lang_index, ∃ p ∈ pay_index , h ⟨1, l⟩ = h ⟨1, p⟩
  } := by
  unfold lang_render origin_render render_C' Sum.getLeft!
  intros h hh
  simp_all
  move=> >
  simp
  sorry


/- Example 2 -/
def lang_c2 := [lang|
  fun ⸨x:Val⸩ ⸨a:Val⸩ =>
    for i in [1:a] {
      x := x + 1
    }
]
/-  L ::= S1
    S1 ::= S2 | S2;S1
    S2 ::= x := x + 1 -/

def prod2 : production :=
  Finmap.singleton S1 [(symbol.terminal S2), symbol.seq (symbol.terminal S2) (symbol.nonterminal S1)]

def L2 : cfg :=
  { nonterminals := {S1},
    prods := prod2,
    start := symbol.nonterminal S1 }

def lang_index2 : Set (trm ⊕ List ℕ ):=
  {l:trm ⊕ List ℕ |
    match l with
    | Sum.inl t => lgtm_match t L2
    | Sum.inr _ => False}

lemma example2_spec (f : ℤ -> val):
  {
    arr⟨⋆⟩(xptr , i in 1 =>f i)
  }
  [1| l in lang_index2  => ⟦origin_render l.val⟧]
  [1| p in pay_index => ⟦lang_render (p.val ) lang_c2 svar_list⟧]
  { v,
    fun h => ∀ l ∈ lang_index2, ∃ p ∈ pay_index , h ⟨1, l⟩ = h ⟨1, p⟩
    -- arr⟨⋆⟩(xptr , i in 1 => f i)
  } := by
  unfold lang_render
  unfold render_C'
  sorry

/- Exampel 3 -/
def lang_c3 := [lang|
  fun ⸨x:Val⸩ ⸨a:Val⸩ =>
    while a
    { x := x + 1 }
]
#print lang_c2


-- def prod2 : production :=
--   (Finmap.singleton S1 [(symbol.terminal S2), symbol.seq (symbol.terminal S2) (symbol.terminal S1)]).insert
--   L [symbol.nonterminal S1]


end WeirdLogic
