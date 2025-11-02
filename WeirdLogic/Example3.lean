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

/- L -> (S1)
  S1 -> trm1; S1; trm2
        | ε
 -/
 /- context free + langseq rule -/
def trm1 : trm := [lang| let xx := !xl in let temp0 := xx + 1 in xl := temp0]
def trm2 : trm := [lang| let yy := !yl in let temp1 := yy + 1 in yl := temp1]
def r1 : ContextFreeRule trm String :=
  {
    input := "L",
    output := [Symbol.nonterminal "S1"]
  }

def r2 : ContextFreeRule trm String :=
  {
    input := "S1",
    output := [Symbol.terminal trm1, Symbol.nonterminal "S1", Symbol.terminal trm2],
  }

def r3 : ContextFreeRule trm String :=
  {
    input := "S1",
    output := [],
  }


def cfg1 : ContextFreeGrammar trm :=
  {
    NT := String,
    initial := "S1",
    rules := Finset.mk {r1, r2, r3} (by unfold r1 r2 r3 trm1 trm2; simp)
  }

def l1 : Language trm := cfg1.language

def cfg_expand : Set ( List (Symbol T N)) :=
  {
    c | cfg1.Generates c
  }

lang_def prog_c1 :=
  fun ⸨xl: Val⸩ ⸨yl: Val⸩ ⸨pa:Val⸩ =>
    for k in [0:pa] {
      let xx := !xl in
      let temp0 := xx + 1 in
      xl := temp0
    };
    for k in [0:pa] {
      let yy := !yl in
      let temp1 := yy + 1 in
      yl := temp1
    }

abbrev default_payload : payload:= 0
abbrev default_trm : trm := [lang|()]

abbrev Lang := List trm

def lang_list_index : Set (List trm) :=
  {l | (trm_to_symbol_list l) ∈ cfg_expand }

def cfgexp_grammar : ℕ → trm → trm → trm
  | 0, _, _ => trm_val val_unit
  | 1, t1, t2 => trm_seq t1 t2
  | (n+1), t1, t2 => trm_seq t1 (trm_seq (cfgexp_grammar n t1 t2) t2)

def lang_squeeze_list: Set trm :=
  {cfgexp_grammar i trm1 trm2 | i : ℕ }

def lang_fun_list : Set trm :=
  {[lang| fun ⸨xl: Loc⸩ ⸨yl : Loc⸩ => {tt}] | tt ∈ lang_squeeze_list }

def pay_index : Set (trm × payload) :=
  {
    (default_trm,p) | p ∈ @Set.univ payload
  }

def lang_index : Set (trm × payload ):=
  { (l,default_payload) | l ∈ lang_fun_list }

variable (pa_len : ℕ) (pb_len : ℕ) (xptr : loc)
variable (paptr : trm × payload -> loc) (pbptr : trm × payload -> loc)

lemma example3_spec (xv yv : ℤ) :
  {
    [∗ in ⟪0,pay_index⟫ ∪ ⟪1,lang_index⟫ | xl ~~> xv] ∗
    [∗ in ⟪0,pay_index⟫ ∪ ⟪1,lang_index⟫ | yl ~~> yv]
  }
  [0| p in pay_index => prog_c1(⸨xl : Loc⸩, ⸨yl : Loc⸩, ⟨p.val.2⟩) ]
  [1| l in lang_index => l.val.fst(⸨xl: Loc⸩, ⸨yl : Loc⸩)]
  { v,
    fun h => ∀ l ∈ lang_index, ∃ p ∈ pay_index , h ⟨1, ll⟩ = h ⟨0, pp⟩
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
