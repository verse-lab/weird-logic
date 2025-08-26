import Mathlib.Computability.ContextFreeGrammar

import Lgtm.Hyper.ProofMode
import Lgtm.Hyper.ArraysFun
import Lgtm.Unary.Lang

import Lgtm.Experiments.HyperCommon

import WeirdLogic.Gram
import WeirdLogic.WLogic
import WeirdLogic.Util

open Unary prim val trm
open ContextFreeGrammar

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

/- Exampel 1: single if-else branch -/
def lang_c1 := [lang|
  fun ⸨a:Val⸩ =>
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

def pvar_list : List var := ["a"]
-- abbr payload

abbrev payload := ℕ

def pay_index : Set (trm ⊕ payload) :=
  {p:trm ⊕ payload |
  match p with
    | Sum.inl _ => False
    | Sum.inr _ => True
  }
#check pay_index

def lang_index : Set (trm ⊕ payload ):=
  {l:trm ⊕ payload |
    match l with
    | Sum.inl t => lgtm_match t L1
    | Sum.inr _ => False}

#check lang_index

variable (N: ℕ)

-- def payload_render (p : trm ⊕ List ℕ) (l : trm) (svar : List var): trm :=
--   render_C l (Sum.getRight! p) svar

def lang_render (l : trm ⊕ payload ) : trm :=
  Sum.getLeft! l

-- def origin_render ()
def origin_c1_set := [lang|
  fun ⸨p:Val⸩ =>
    p
]
#check bighstar

#check LGTM.triple

-- [1| p in pay_index => ⟦payload_render p.val lang_c1 pvar_list⟧]

lemma example1_spec (H : hProp ):
  { [∗ in ⟪1,pay_index⟫ ∪ ⟪2,lang_index⟫ | H ] }
  [1| p in pay_index => lang_c1(⟨ val_int (Sum.getRight! p.val)⟩ )]
  [2| l in lang_index  => ⟦lang_render l.val ⟧]
  { v,
    (fun h => ∀ l ∈ lang_index, ∃ p ∈ pay_index , h ⟨1, p⟩ = h ⟨2, l⟩ )
  } := by
  unfold lang_render Sum.getRight! Sum.getLeft!
  intros h hh
  move=> >
  simp [lang_c1]
  sorry


/- Example 2: single for loop -/
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

def lang_index2 : Set (trm ⊕ payload):=
  {l:trm ⊕ payload |
    match l with
    | Sum.inl t => lgtm_match t L2
    | Sum.inr _ => False}

lemma example2_spec (f : ℤ -> val):
  {
    [∗ in ⟪1,pay_index⟫ ∪ ⟪2,lang_index⟫ | H ] ∗ arr⟨⋆⟩(xptr , i in 1 =>f i)
  }
  [1| p in pay_index => lang_c2(⟨ val_int (Sum.getRight! p.val)⟩)]
  [2| l in lang_index2  => ⟦lang_render l.val⟧]
  { v,
    fun h => ∀ l ∈ lang_index2, ∃ p ∈ pay_index , h ⟨1, l⟩ = h ⟨2, p⟩
    -- arr⟨⋆⟩(xptr , i in 1 => f i)
  } := by
  unfold lang_render Sum.getLeft!
  simp
  intros h hh
  move=> >
  simp [lang_c2]
  sorry

/- Exampel 3: two variables in the payload -/
def lang_c3 := [lang|
  fun ⸨a:Val⸩ ⸨b:Val⸩ =>
    if a > 0 then
      x := x + 1
    else
      x := x + 2;
    if b > 0 then
      x := x + 3
    else
      x := x + 4
]
#print lang_c3

/- ============ Example 4: new cfg & if-else ============ -/
-- Example 4
def trm1 : trm := [lang| x := x + 1]
def trm2 : trm := [lang| x := x + 2]
def trm3 : trm := [lang| x := x + 3]
def r1 : ContextFreeRule trm String :=
  {
    input := "S1",
    output := [Symbol.terminal trm1, Symbol.nonterminal "S2"],
  }
def r2 : ContextFreeRule trm String :=
  {
    input := "S1",
    output := [Symbol.terminal trm2, Symbol.nonterminal "S2"],
  }
def r3 : ContextFreeRule trm String :=
  {
    input := "S2",
    output := [Symbol.terminal trm3],
  }
def cfg4 : ContextFreeGrammar trm :=
  {
    NT := String,
    initial := "S1",
    rules := Finset.mk {r1, r2, r3} (by unfold r1 r2 r3 trm1 trm2; simp)
  }

def l4 : Language trm := cfg4.language

#check cfg4.Derives [Symbol.terminal trm1] [Symbol.terminal trm1, Symbol.terminal trm3]
#check Derives.trans

example : cfg4.Generates [Symbol.terminal trm2, Symbol.terminal trm3]:= by
  unfold ContextFreeGrammar.Generates
  let tm := [Symbol.terminal trm2, Symbol.nonterminal "S2"]
  apply ContextFreeGrammar.Derives.trans (v := tm)
  . unfold ContextFreeGrammar.Derives
    unfold ContextFreeGrammar.Produces
    constructor
    { rfl}
    {
      use r2
      constructor
      { exact Finset.mem_mk.mpr (by simp)}
      { unfold tm; apply ContextFreeRule.rewrites_of_exists_parts (p := ∅ ) }
    }
  . unfold ContextFreeGrammar.Derives
    unfold ContextFreeGrammar.Produces
    constructor
    { rfl}
    {
      use r3
      constructor
      { exact Finset.mem_mk.mpr (by simp)}
      { unfold tm; apply ContextFreeRule.rewrites_of_exists_parts (p := [Symbol.terminal trm2] ) }
    }

def lang_c4 := [lang|
  fun ⸨a:Val⸩ ⸨b:Val⸩ =>
    if a > 0 then
      x := x + 1
    else
      x := x + 2;
    x := x + 3
]
#print lang_c4

def pay_index4 : Set (trm ⊕ payload) :=
  {p:trm ⊕ payload |
  match p with
    | Sum.inl _ => False
    | Sum.inr _ => True
  }
def lang_index4 : Set (trm ⊕ payload ):=
  {l:trm ⊕ payload |
    match l with
    | Sum.inl t => cfg4.Generates (expand_trm t)
    | Sum.inr _ => False}


lemma example4_spec (f : ℤ -> val):
  {
    [∗ in ⟪1,pay_index4⟫ ∪ ⟪2,lang_index4⟫ | H ] ∗ arr⟨⋆⟩(xptr , i in 1 =>f i)
  }
  [1| p in pay_index4 => lang_c4(⟨ val_int (Sum.getRight! p.val)⟩)]
  [2| l in lang_index4  => ⟦lang_render l.val⟧]
  { v,
    fun h => ∀ l ∈ lang_index4, ∃ p ∈ pay_index4 , h ⟨1, l⟩ = h ⟨2, p⟩
    -- arr⟨⋆⟩(xptr , i in 1 => f i)
  } := by
  unfold lang_render Sum.getLeft!
  sorry



end WeirdLogic
