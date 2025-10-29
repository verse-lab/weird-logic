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

/- L -> S1
  S1 -> trm1; S1
        | ε
 -/
/- regular + for rule -/
/- for a language instance in type trm, the outermost type must be trm_funs -/

def trm_tmp : trm := [lang| fun ⸨xl: Loc⸩ => () ]
def trm1 : trm := [lang| let xx := !xl in xl := xx + 1]
def r1 : ContextFreeRule trm String :=
  {
    input := "L",
    output := [Symbol.nonterminal "S1"],
  }

def r2 : ContextFreeRule trm String :=
  {
    input := "S1",
    output := [Symbol.terminal trm1, Symbol.nonterminal "S1"],
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
    rules := Finset.mk {r1, r2, r3} (by unfold r1 r2 r3 trm1; simp)
  }

def l1 : Language trm := cfg1.language

def cfg_expand : Set ( List (Symbol T N)) :=
  {
    c | cfg1.Generates c
  }

-- lang_def prog_c1 :=
--   fun ⸨xl: Loc⸩ ⸨pa: Val⸩ =>
--     for k in [0 : pa] {
--       let tmp := !xl in
--       xl := tmp + 1
--     };
--     ()

lang_def prog_c1 :=
  fun ⸨xl: Loc⸩ ⸨pa: Val⸩ =>
    let tmp := !xl in
    for k in [0 : pa] {
      tmp := tmp + 1
    };
    xl := tmp

def pay_index' := @Set.univ payload
abbrev Lang := List trm

def lang_expand_list : Set Lang :=
  {l | (trm_to_symbol_list l) ∈ cfg_expand }

-- def lang_squeeze_list: Set trm :=
--   {squeeze_trm t | t ∈ lang_expand_list}



def regexp_grammar : ℕ → trm → trm
  | 0, _ => trm_val val_unit
  | 1, t => t
  | (n+1), t => trm_seq t (regexp_grammar n t)

def lang_squeeze_list: Set trm :=
  {regexp_grammar i trm1 | i : ℕ }

def lang_fun_list : Set trm :=
  {[lang| fun ⸨xl: Loc⸩ => {tt}] | tt ∈ lang_squeeze_list }

abbrev default_payload : payload:= 0
abbrev default_trm : trm := [lang|()]

def pay_index : Set (trm × payload) :=
  {
    (default_trm,p) | p ∈ @Set.univ payload
  }

def lang_index : Set (trm × payload ):=
  { (l,default_payload) | l ∈ lang_fun_list }


lemma example2_single_iter :
  ∀ n : ℕ,
  sn = [lang| fun ⸨xl: Loc⸩ => {regexp_grammar n trm1}] →
  {
    xl ~⟨i in {⟨0,(default_trm, (Int.ofNat n))⟩} ∪ {⟨1,(sn,default_payload)⟩}⟩~> xv
  }
  [0| p in {(default_trm, (Int.ofNat n))} => prog_c1(⸨xl: Loc⸩, ⟨p.val.2⟩)]
  [1| l in {(sn,default_payload)} => l.val.fst(⸨xl: Loc⸩)]
  { v,
    fun h => ∀ l ∈ ({(sn,default_payload)} : Set (trm × payload)), ∃ p ∈ ({(default_trm, (Int.ofNat n))} : Set (trm × payload)) , h ⟨1, l⟩= h ⟨0, p⟩
  }
  := by
  intro n
  induction n with
  | zero =>
    intro hsn
    unfold LGTM.triple default_payload hhsingle
    dsimp
    apply weird_lang_lemma=>//
    { simp; apply disjoint_label_set.mpr; simp}
    apply weird_payload_lemma=>//
    { simp; apply disjoint_label_set.mpr; simp}
    rw [← weird_fix_lang (p := default_payload)]
    rw [← weird_fix_payload1 (pv := 0)]
    -- dsimp [LGTM.wp, LGTM.SHTs.htrm]
    have sneq : regexp_grammar 0 trm1 = [lang| ()] := by
      unfold regexp_grammar; simp
    rw [sneq] at hsn; clear sneq
    yin 1: apply ywp_lemma_funs (tfunc := fun _ => sn) (ts := fun (l : (trm × payload)ˡ) => [xl])
    intro _ ; rfl ; intro _ ; rw [hsn]; intro _; rfl ; intros ; simp; simp [get_vars, type_match]
    simp  [Unary.func_call_ctx_prepare]
    all_goals
      try simp [isubstE, Unary.reduce_call_isubst]; --(try simp [Unary.isubst, Unary.isubst.go])--; (srw ?Unary.guard_pos; all_goals try rfl)
      try simp [wpgen]
      try simp [AList.lookup, List.mkAlist, List.eraseP, List.dlookup]
    ywp; yval
    have uneq : ({⟨0, (default_trm, 0)⟩} : Set (trm × payload)ˡ) ∪ {⟨1, (sn, 0)⟩} = {⟨0, (default_trm, 0)⟩, ⟨1, (sn, 0)⟩} := by
      exact rfl
    rw [← uneq]; clear uneq
    rw [←bighstar_hhstar_disj]
    on_goal 2=> simp

    yin 0: ywp; ylet
    -- { unfold hhsingle; simp [labSet]}
    -- yfor+ with
    --   (Q := fun i _ => (LGTM.wp [] fun x (h: hheap (trm × payload)ˡ) => h ⟨1, (sn, 0)⟩ = h ⟨0, (default_trm, 0)⟩))
    --   -- (H₀ := (xl ~⟨x in ⟪0, {(default_trm, 0)}⟫⟩~> xv) ∗ [∗i in {⟨1, (sn, 0)⟩}| xl ~~> xv])
    --   (Inv := fun _ => emp)
    -- apply ywp_lemma_funs (tfunc := fun _ => prog_c1) (ts := fun (p : (trm × payload)ˡ) => [xl, [lang| 0]])
    -- intro _ ; rfl ; intro _ ; rfl ; intros ; rfl ; intros ; simp [get_vars, type_match]
    -- simp  [Unary.func_call_ctx_prepare]
    -- all_goals
    --   try simp [isubstE, Unary.reduce_call_isubst]; --(try simp [Unary.isubst, Unary.isubst.go])--; (srw ?Unary.guard_pos; all_goals try rfl)
    --   try simp [wpgen]
    --   try simp [AList.lookup, List.mkAlist, List.eraseP, List.dlookup]
    -- rw [hwp_ht_eq (ht₂ := (fun a ↦
    --   [lang|
    --     () ]))]
    -- on_goal 2=> simp only [Set.EqOn, fun_insert, Set.union_empty] ; rintro ⟨l, ⟨a , b⟩⟩ bb ; congr ; simp

    apply htriple_conseq_frame (H₂ := [∗i in {⟨1, (sn, 0)⟩}| xl ~~> xv]); apply htriple_get (v := fun _ => xv) ;
    { unfold hhsingle; simp [labSet]}
    simp [subst, subst.go]
    -- yfor+ with
    --   (Q := fun i _ => (LGTM.wp [] fun x (h: hheap (trm × payload)ˡ) => h ⟨1, (sn, 0)⟩ = h ⟨0, (default_trm, 0)⟩))
    --   (H₀ := (xl ~⟨x in ⟪0, {(default_trm, 0)}⟫⟩~> xv))
    -- yfor
    sorry
  | succ k hk => sorry

set_option maxRecDepth 2000 in
set_option maxHeartbeats 6400000 in
lemma example2_spec (xv : ℤ):
  {
    xl ~⟨i in {⟨0,p⟩ | p ∈ pay_index} ∪ {⟨1,l⟩ | l ∈ lang_index}⟩~> xv
  }
  [0| p in pay_index => prog_c1(⸨xl: Loc⸩, ⟨p.val.2⟩)]
  [1| l in lang_index => l.val.fst(⸨xl: Loc⸩)]
  { v,
    fun h => ∀ l ∈ lang_index, ∃ p ∈ pay_index , h ⟨1, l⟩= h ⟨0, p⟩
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
