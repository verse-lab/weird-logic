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

/- L -> S1
  S1 -> trm1; S1; trm1
        | trm2; S1; trm2
        | ε
  L = {w;wᴿ : w ∈ {trm1,trm2}*}
  context free + seq rule
  similar to balanced parentheses problem
-/
def trm1 : trm := [lang| let xx := !xl in let temp0 := xx + 1 in xl := temp0]
def trm2 : trm := [lang| let yy := !yl in let temp1 := yy - 1 in yl := temp1]
def r1 : ContextFreeRule trm String :=
  {
    input := "L",
    output := [Symbol.nonterminal "S1"],
  }

def r2 : ContextFreeRule trm String :=
  {
    input := "S1",
    output := [Symbol.terminal trm1, Symbol.nonterminal "S1", Symbol.terminal trm1],
  }

def r3 : ContextFreeRule trm String :=
  {
    input := "S1",
    output := [Symbol.terminal trm2, Symbol.nonterminal "S1", Symbol.terminal trm2],
  }

def r4 : ContextFreeRule trm String :=
  {
    input := "S1",
    output := [],
  }

def cfg1 : ContextFreeGrammar trm :=
  {
    NT := String,
    initial := "S1",
    rules := Finset.mk {r1, r2, r3, r4} (by unfold r1 r2 r3 r4 trm1 trm2; simp)
  }

def l1 : Language trm := cfg1.language


lang_def prog_c1 :=
  fun ⸨x:Loc⸩ ⸨y:Loc⸩ ⸨a: Val⸩ ⸨b: Loc⸩ =>
    for i in [0: a] {
      let j := b[i] in
      if j > 10 then
      let tmp1 := xx + 1 in
      x := tmp1
      else
      let tmp2 := yy - 1 in
      y := tmp2
    };
    for i in [0: a] {
      let j := b[i] in
      if j > 10 then
      let tmp2 := yy - 1 in
      y := tmp2
      else
      let tmp1 := xx + 1 in
      x := tmp1
    }

def pay_index : Set (trm × payload × payload) :=
  {
    (default_trm,(p,p)) | p ∈ @Set.univ payload
  }
def lang_set : Set trm :=
  {l | cfg1.Generates (expand_trm l) ∧ l ∈ @Set.univ trm}

def lang_index : Set (trm × payload × payload ):=
  { (l, (default_payload,default_payload)) | l ∈ lang_set}


lemma example4_spec' (xv : ℤ):
  {
    [∗ in ⟪0,pay_index⟫ ∪ ⟪1,lang_index⟫ | xl ~~> xv]
    -- ∗ ....
  }
  [0| p in pay_index => prog_c1(⸨xl : Loc⸩, ⟨p.val.2.1⟩, ⟨p.val.2.2⟩) ]
  [1| l in lang_index => l.val.fst(⸨xl: Loc⸩, ⸨yl : Loc⸩)]
  { v,
    fun h => ∀ ll ∈ lang_index, ∃ pp ∈ pay_index , h ⟨1, ll⟩ = h ⟨0, pp⟩
  }
  := by
  unfold LGTM.triple
  sorry

/- Previously, constraints for payloads in the heap are in the post-condition
    -- ∧ arr⟨{⟨0,p⟩}⟩(pa , i in pa_len => p.2.1[i]!) h
    -- ∧ arr⟨{⟨0,p⟩}⟩(pb , i in pb_len => p.2.2[i]!) h
  And pre-condition is default
  -- arr⟨⋆⟩(pa , i in pa_len =>g i) ∗
  -- arr⟨⋆⟩(pb , i in pb_len =>q i)
-/
