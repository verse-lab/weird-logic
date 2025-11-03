import Mathlib.Computability.ContextFreeGrammar

import Lgtm.Hyper.ProofMode
import Lgtm.Hyper.ArraysFun
import Lgtm.Unary.Lang
import Lgtm.Experiments.HyperCommon

import WeirdLogic.Gram
import WeirdLogic.WLogic
import WeirdLogic.WTriple
import WeirdLogic.WUtil
import WeirdLogic.Hete

open Unary prim val trm
open ContextFreeGrammar

namespace WeirdLogic

/- L -> (S1; S2)
  S1 -> S3; S1
        | ε
  S2 -> trm 1
  S3 -> trm 2 | trm 3
 -/
/- context free + while rule -/
def trm1 : trm := [lang| x := -x]
def trm2 : trm := [lang| x := x + 1]
def trm3 : trm := [lang| x := x * 2]
def r1 : ContextFreeRule trm String :=
  {
    input := "L",
    output := [Symbol.nonterminal "S1", Symbol.nonterminal "S2"],
  }

def r2 : ContextFreeRule trm String :=
  {
    input := "S1",
    output := [Symbol.nonterminal "S3", Symbol.nonterminal "S1"],
  }

def r3 : ContextFreeRule trm String :=
  {
    input := "S1",
    output := [],
  }

def r4 : ContextFreeRule trm String :=
  {
    input := "S2",
    output := [Symbol.terminal trm1],
  }

def r5 : ContextFreeRule trm String :=
  {
    input := "S3",
    output := [Symbol.terminal trm2],
  }

def r6 : ContextFreeRule trm String :=
  {
    input := "S3",
    output := [Symbol.terminal trm3],
  }

def cfg1 : ContextFreeGrammar trm :=
  {
    NT := String,
    initial := "S1",
    rules := Finset.mk {r1, r2, r3, r4, r5, r6} (by unfold r1 r2 r3 r4 r5 r6 trm1 trm2 trm3; simp)
  }

def l1 : Language trm := cfg1.language

-- def prog_c1 (pa pb : List ℤ) : val :=
-- [trm|
--   let i := 0
--   let b := ⟨pa[i]⟩
--   ...
-- ]
-- fun f : trm -> ℤ
--

lang_def prog_c1 :=
  fun ⸨x: Val⸩ ⸨pa:Loc⸩ ⸨pb:Loc⸩ =>
    let i := 0 in
    let b := pb[i] in
    while pb[i] {
      let a := pa[i] in
        if a > 0 then
          x := x + 1
        else
          x := x*2;
      i := i+1
    };
    x := -x

abbrev multi_payload := List ℤ

def pay_index : Set (trm × multi_payload × multi_payload) :=
  {
    ([lang|()],(p,p)) | p ∈ @Set.univ multi_payload
  }
def lang_set : Set trm :=
  {l | cfg1.Generates (expand_trm l) ∧ l ∈ @Set.univ trm}

def lang_index : Set (trm × multi_payload × multi_payload ):=
  { (l, ([0],[0])) | l ∈ lang_set}

variable (pa_len : ℕ) (pb_len : ℕ) (xptr : loc)
variable (paptr : trm × multi_payload × multi_payload -> loc)
 (pbptr : trm × multi_payload × multi_payload -> loc)

lemma example4_spec' (f : ℤ -> val) (x : loc) (g q : ℤ -> val):
  {
    arr⟨⋆⟩(xptr , i in 1 =>f i)
    -- check the syntax of x->_
    -- ∗
    -- bighstar ⟪0,pay_index⟫ (fun i => harray i.val.2.1 (paptr i.val) ∗ harray i.val.2.2 (pbptr i.val))
  }
  [0| p in pay_index => prog_c1(⟨f 0⟩,⸨pa:Loc⸩, ⸨pb:Loc⸩)]
  [1| l in lang_index => ⟦l.val.1⟧]
  { v,
    fun h => ∀ l ∈ lang_index, ∃ p ∈ pay_index , (fun ll pp => h ⟨1, ll⟩ = h ⟨0, pp⟩) l p
  }
  := by
  sorry

/- Previously, constraints for payloads in the heap are in the post-condition
    -- ∧ arr⟨{⟨0,p⟩}⟩(pa , i in pa_len => p.2.1[i]!) h
    -- ∧ arr⟨{⟨0,p⟩}⟩(pb , i in pb_len => p.2.2[i]!) h
  And pre-condition is default
  -- arr⟨⋆⟩(pa , i in pa_len =>g i) ∗
  -- arr⟨⋆⟩(pb , i in pb_len =>q i)
-/
