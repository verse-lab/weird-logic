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
def trm1 : trm := [lang| let xx := !xl in let temp0 := xx + 1 in xl := temp0]
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
    for k in [0 : pa] {
      let xx := !xl in
      let temp0 := xx + 1 in
      xl := temp0
    }

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

lemma regexp_grammar_isubst (n : ℕ) (t : trm) :
  isubst Ev El (regexp_grammar n t) = regexp_grammar n (isubst Ev El t) := by
  fun_induction regexp_grammar n t
  all_goals simp [regexp_grammar, isubst]
  assumption

lemma eval_for_val (v : val) : eval s v Q ↔ Q v s := by
  constructor
  · intro h ; cases h ; assumption
  · intro h ; constructor ; assumption

lemma empty_for_loop (a : Int) :
  eval s (trm_for i a a t) Q ↔ Q val_unit s := by
  constructor
  · intro h ; cases h ; rename_i h ; simp at h ; rw [eval_for_val] at h ; assumption
  · intro h ; constructor ; simp ; rw [eval_for_val] ; assumption

lemma equiv_1 (a : Int)
  (h : ∀ (v : val), subst i v t = t)
  -- (hQ : (∀ v1 v2, Q v1 = Q v2) ∨ (∀ v h, Q v h → v = val_unit))
  -- (hQt : ∀ Q', eval s t Q' →
  --   ((∀ v1 v2, Q' v1 = Q' v2) ∨ (∀ v h, Q' v h → v = val_unit)))
  (hQ : (∀ v1 v2, Q v1 = Q v2))
  :
  eval s (regexp_grammar n t) Q ↔ eval s (trm_for i a ((a + n : Int)) t) Q := by
  fun_induction regexp_grammar n t generalizing s a
  next t =>
    simp [regexp_grammar] ; rw [empty_for_loop, eval_for_val]
  next t =>
    simp [regexp_grammar]
    constructor
    · intro hh ; constructor ; simp ; rw [h]
      constructor ; assumption
      intros ; rw [empty_for_loop, hQ] ; assumption
    · intro hh ; cases hh ; rename_i hh
      simp at hh ; rw [h] at hh
      cases hh ; rename_i Q1 hmid h2
      simp only [empty_for_loop] at h2
      apply eval_conseq' ; assumption
      intros ; rw [hQ _ val_unit] ; solve_by_elim
  next n t not0 ih =>
    have tmp : a + 1 + ↑n = a + (↑n + 1) := by ac_rfl
    simp [regexp_grammar]
    constructor
    · intro hh ; constructor ; simp ; rw [h]
      cases hh ; rename_i Q1 hmid h2
      constructor ; assumption
      intro v1 s2 h2_ ; specialize h2 _ _ h2_
      specialize @ih s2 (a + 1) h ; rw [tmp] at ih
      rw [← ih] ; assumption
    · intro hh ; cases hh ; rename_i hh
      simp at hh ; rw [h] at hh
      cases hh ; rename_i Q1 hmid h2
      constructor ; assumption
      intro v1 s2 h2_ ; specialize h2 _ _ h2_
      specialize @ih s2 (a + 1) h ; rw [tmp] at ih
      rw [ih] ; assumption

lemma simple_loop_pre (xl : loc) (xv : ℤ) (n : Nat) :
  let nn : val := val_int n
  triple
    [lang|
      for k in [0 : nn] {
        let xx := !xl in
        let temp0 := xx + 1 in
        xl := temp0
      }]
    (xl ~~> xv) (fun _ => xl ~~> ((xv + n) : ℤ)) := by
  xfor (fun a => xl ~~> ((xv + a) : ℤ))
  intro i h1 h2 ; xwp ; xlet
  on_goal 2=> xsimp ; xsimp
  xapp ; xwp ; xlet ; xstep ; xapp ; xsimp

lemma xwp_lemma_funs' (xs : List trm) (ts : List trm) :
  t = trm_call tfunc ts ->
  tfunc = trm_funs xs t1 ->
  func_call_shape_condition xs (get_vars xs) ts ->
  func_call_ctx_prepare (List.zip xs ts) = some (Ev, El) ->
  himpl H (wp (isubst Ev.toAList El.toAList t1) Q) →
  triple t H Q := by
  move=> -> -> ?? h
  srw -wp_equiv ; apply himpl_trans ; apply h
  apply wp_eval_like
  apply eval_like_trm_apps_funs_pre <;> try assumption

lemma example2_single_iter (xv : ℤ) :
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
  intro n hsn
  unfold hhsingle-- ; rw [← bighstar_hhstar_disj] ; dsimp
  unfold LGTM.triple LGTM.wp labSet
  open Classical in simp +unfoldPartialApp [fun_insert]
  have tmp := htriple_prod (α := (trm × payload)ˡ) (s := {⟨1, (sn, default_payload)⟩, ⟨0, (default_trm, ↑n)⟩})
    (ht := open Classical in (fun a =>
      if a = ⟨0, (default_trm, ↑n)⟩ then prog_c1.trm_call [xl, [lang| ⟨a.val.2⟩]]
      else if a = ⟨1, (sn, default_payload)⟩ then a.val.1.trm_call [xl] else [lang| ()]))
    (H := fun _ => xl ~~> xv)
    (Q := fun _ _ => xl ~~> ((xv + n) : ℤ))
  specialize tmp (by
    clear tmp
    simp
    constructor
    · rw [hsn] ; (apply xwp_lemma_funs'; rfl; rfl; { simp [get_vars, type_match] }; { rfl })
      rw [regexp_grammar_isubst, trm1] ; simp [isubst, isubst.go]
      intro h hh ; apply (equiv_1 (i := "k") 0 _ _).mpr
      on_goal 2=> intro v ; rfl
      on_goal 2=> intros ; rfl
      simp ; revert h hh
      apply simple_loop_pre
    · xwp ; xapp_pre    -- ?
      apply simple_loop_pre
  )
  apply hhimpl_trans ; apply tmp
  clear tmp
  apply hwp_conseq
  ysimp
  unfold bighstar bighstarDef ; open Classical in simp
  intro h hh
  have h1 := hh ⟨1, (trm_funs [trm_varl "xl"] (regexp_grammar n trm1), 0)⟩ ; simp at h1
  have h2 := hh ⟨0, (default_trm, ↑n)⟩ ; simp at h2
  unfold hsingle at h1 h2 ; rw [h1, h2]

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
