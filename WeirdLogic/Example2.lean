import Mathlib.Computability.ContextFreeGrammar

import Lgtm.Hyper.ProofMode
import Lgtm.Hyper.ArraysFun
import Lgtm.Unary.Lang
import Lgtm.Experiments.HyperCommon

import WeirdLogic.Gram
import WeirdLogic.WLogic
import WeirdLogic.WTriple
import WeirdLogic.Util
import WeirdLogic.Hete

open Unary prim val trm
open ContextFreeGrammar

namespace WeirdLogic

/- L -> (S1; S2)
  S1 -> trm2; S1
        | ε
  S2 -> trm 1
 -/
def trm1 : trm := [lang| x := -x]
def trm2 : trm := [lang| x := x + 1]
def r1 : ContextFreeRule trm String :=
  {
    input := "L",
    output := [Symbol.nonterminal "S1", Symbol.nonterminal "S2"],
  }

def r2 : ContextFreeRule trm String :=
  {
    input := "S1",
    output := [Symbol.terminal trm2, Symbol.nonterminal "S1"],
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


def cfg1 : ContextFreeGrammar trm :=
  {
    NT := String,
    initial := "S1",
    rules := Finset.mk {r1, r2, r3, r4} (by unfold r1 r2 r3 r4 trm1 trm2; simp)
  }

def l1 : Language trm := cfg1.language

-- lang_def prog_c1 :=
--   fun ⸨x: Val⸩ ⸨pa:Val⸩ =>
--     while pa > 0 {
--         x := x + 1;
--         pa := pa-1
--     };
--     x := -x

lang_def prog_c1 :=
  fun ⸨x: Val⸩ ⸨pa:Val⸩ =>
    for i in [0:pa] {
        x := x + 1
    }

abbrev default_payload : payload:= 0
abbrev default_trm : trm := [lang|()]

def pay_index : Set (trm × payload) :=
  {
    ([lang|()],p) | p ∈ @Set.univ payload
  }

def cfg_expand : Set ( List (Symbol T N)) :=
  {
    c | cfg1.Generates c
  }

def lang_list_index : Set (List trm) :=
  {l | (trm_to_symbol_list l) ∈ cfg_expand }

def lang_index_only : Set trm :=
  {squeeze_trm t | t ∈ lang_list_index}

def lang_set : Set trm :=
  {l | cfg1.Generates (expand_trm l) ∧ l ∈ @Set.univ trm}

def lang_index : Set (trm × payload ):=
  { (l, (0)) | l ∈ lang_index_only}

variable (pa_len : ℕ) (pb_len : ℕ) (xptr : loc)
variable (paptr : trm × payload -> loc) (pbptr : trm × payload -> loc)

lemma example4_spec' (f : ℤ -> val) (g q : ℤ -> val):
  {
    arr⟨⋆⟩(xptr , i in 1 =>f i)
  }
  [0| p in pay_index => prog_c1(⟨f 0⟩,⟨p.val.2⟩) ]
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
