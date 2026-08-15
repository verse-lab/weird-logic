import Mathlib.Computability.ContextFreeGrammar

import Lgtm.Hyper.ProofMode
import Lgtm.Hyper.ArraysFun
import Lgtm.Unary.Lang
import Lgtm.Experiments.HyperCommon

import WeirdLogic.Gram
import WeirdLogic.WLogic
import WeirdLogic.WTriple
import WeirdLogic.WUtil
import WeirdLogic.WUnary

open Unary prim val trm
open ContextFreeGrammar

namespace WeirdLogic.ExampleFor

/- L -> (S1)
  S1 -> trm1; S1; trm2
        | ε

  L = {trm1ⁿ;trm2ⁿ : n ≥ 0}
  context free + infdisj rule -/
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
  fun ⸨xl: Loc⸩ ⸨yl: Loc⸩ ⸨pa:Val⸩ =>
    for k in [0:pa] {
      let xx := !xl in
      let temp0 := xx + 1 in
      xl := temp0
    };
    for j in [0:pa] {
      let yy := !yl in
      let temp1 := yy + 1 in
      yl := temp1
    }

abbrev Lang := List trm

def lang_list_index : Set (List trm) :=
  {l | (trm_to_symbol_list l) ∈ cfg_expand }

def regexp_grammar : ℕ → trm → trm
  | 0, _ => trm_val val_unit
  | 1, t => t
  | (n+1), t => trm_seq t (regexp_grammar n t)

def cfgexp_grammar : ℕ → trm → trm → trm
  | 0, _, _ => trm_val val_unit
  | n, t1, t2 => trm_seq (regexp_grammar n t1) (regexp_grammar n t2)
  -- | 1, t1, t2 => trm_seq t1 t2
  -- | (n+1), t1, t2 => trm_seq t1 (trm_seq (cfgexp_grammar n t1 t2) t2)

def lang_squeeze_list: Set trm :=
  {cfgexp_grammar i trm1 trm2 | i : ℕ }

def lang_fun_list : Set trm :=
  {[lang| fun ⸨xl: Loc⸩ ⸨yl : Loc⸩ => {tt}] | tt ∈ lang_squeeze_list }

def pay_index : Set (trm × payload) :=
  {
    (default_trm,p) | p ∈ { pp : ℤ | pp ≥ 0 }
  }

def lang_index : Set (trm × payload ):=
  { (l,default_payload) | l ∈ lang_fun_list }

variable (pa_len : ℕ) (pb_len : ℕ) (xptr : loc)
variable (paptr : trm × payload -> loc) (pbptr : trm × payload -> loc)

lemma regexp_grammar_isubst (n : ℕ) (t : trm) :
  isubst Ev El (regexp_grammar n t) = regexp_grammar n (isubst Ev El t) := by
  fun_induction regexp_grammar n t
  all_goals simp [regexp_grammar, isubst]
  assumption

lemma cfgexp_grammar_isubst (n : ℕ) (t1 t2 : trm) :
  isubst Ev El (cfgexp_grammar n t1 t2) = cfgexp_grammar n (isubst Ev El t1) (isubst Ev El t2):= by
  unfold cfgexp_grammar
  cases n
  case zero => simp [isubst]
  case succ n =>
    simp [isubst]
    constructor <;> apply regexp_grammar_isubst
  -- proofs if use old format
  -- fun_induction cfgexp_grammar n t1 t2
  -- all_goals simp [cfgexp_grammar, isubst]
  -- assumption


lemma equiv_1 (a : Int)
  (h : ∀ (v : val), subst i v t = t)
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

lemma simple_loop_pre2 (xl : loc) (xv : ℤ) (yv : ℤ) (n : Nat) :
  let nn : val := val_int n
  triple
    [lang|
      for k in [0 : nn] {
        let xx := !xl in
        let temp0 := xx + 1 in
        xl := temp0
      }]
    (xl ~~> xv ∗ yl ~~>yv)
    (fun _ => xl ~~> ((xv + n) : ℤ) ∗ yl ~~> yv) := by
  apply triple_frame
  apply simple_loop_pre

lemma simple_loop_pre3 (xl : loc) (xv : ℤ) (yv : ℤ) (n : Nat) :
  let nn : val := val_int n
  triple
    [lang|
      for k in [0 : nn] {
        let yy := !yl in
        let temp1 := yy + 1 in
        yl := temp1
      }]
    (xl ~~> ((xv + n) : ℤ)∗ yl ~~>yv)
    (fun _ => yl ~~> ((yv + n) : ℤ)∗ xl ~~> ((xv + n) : ℤ)) := by
  rw [hstar_comm]
  apply triple_frame
  xfor (fun a => yl ~~> ((yv + a) : ℤ))
  intro i h1 h2 ; xwp ; xlet
  on_goal 2=> xsimp ; xsimp
  xapp ; xwp ; xlet ; xstep ; xapp ; xsimp

lemma example3_single_iter (xv : ℤ) (yv : ℤ):
  ∀ n : ℕ,
  sn = [lang| fun ⸨xl: Loc⸩ ⸨yl : Loc⸩=> {cfgexp_grammar n trm1 trm2}] →
  [∗ in {⟨0, (default_trm, Int.ofNat n)⟩} ∪ {⟨1, (sn, default_payload)⟩}| xl ~~> xv ∗ yl ~~> yv] ==>
  LGTM.wp
    [{ s := ⟪0, {(default_trm, Int.ofNat n)}⟫, ht := fun p ↦ prog_c1.trm_call [xl, yl, [lang| ⟨p.val.2⟩]] },
     { s := ⟪1, {(sn, default_payload)}⟫, ht := fun l ↦ l.val.1.trm_call [xl, yl] }]
    fun _ =>
      -- h => ∀ l ∈ ({(sn, default_payload)} : Set (trm × payload)), ∃ p ∈ ({(default_trm, n)} : Set (trm × payload)), h ⟨1, l⟩ = h ⟨0, p⟩
      [∗ in {⟨0, (default_trm, n)⟩} ∪ {⟨1, (sn, default_payload)⟩}| xl ~~> (xv + n) ∗ yl ~~> (yv + n)]
  := by
  intro n hsn
  unfold LGTM.wp labSet
  open Classical in simp +unfoldPartialApp [fun_insert]
  have tmp := htriple_prod (α := (trm × payload)ˡ) (s := {⟨1, (sn, default_payload)⟩, ⟨0, (default_trm, ↑n)⟩})
    (ht := open Classical in (fun a =>
      if a = ⟨0, (default_trm, ↑n)⟩ then prog_c1.trm_call [xl, yl, [lang| ⟨a.val.2⟩]]
      else if a = ⟨1, (sn, default_payload)⟩ then a.val.1.trm_call [xl, yl] else [lang| ()]))
    (H := fun _ => xl ~~> xv ∗ yl ~~> yv)
    (Q := fun _ _ => xl ~~> ((xv + n) : ℤ) ∗ yl ~~> ((yv + n) : ℤ) )
  specialize tmp (by
    clear tmp
    simp
    constructor
    · rw [hsn] ;
      (apply xwp_lemma_funs'; rfl; rfl; { simp [get_vars, type_match];}; { rfl })
      rw [cfgexp_grammar_isubst, trm1, trm2] ; simp [isubst, isubst.go]
      intro h hh ;
      unfold cfgexp_grammar
      cases n
      case zero =>
        simp;
        revert h hh
        apply empty_pre (H := xl ~~> xv ∗ yl ~~> yv)
      case succ n =>
        simp
        xwp; xseq_xlet_if_needed;
        intro h hh ; apply (equiv_1 (i := "k") 0 _ _).mpr
        on_goal 2=> intro v ; rfl
        on_goal 2=> intros ; rfl
        on_goal 2=> exact hh
        simp ;
        -- revert h hh
        have tpre := simple_loop_pre2 (xv := xv) (yl := yl) (xl := xl) (yv := yv) (n := n+1) h hh
        apply eval_conseq=>//
        intro v; simp
        intro h hh ; apply (equiv_1 (i := "k") 0 _ _).mpr
        on_goal 2=> intro v ; rfl
        on_goal 2=> intros ; rfl
        clear tpre
        -- revert h hh
        have tpre := simple_loop_pre3 (xv := xv) (yl := yl) (xl := xl) (yv := yv) (n := n+1) h hh
        apply eval_conseq (Q1 := fun x ↦ yl ~~> val_int (yv + ↑(n + 1)) ∗ xl ~~> val_int (xv + ↑(n + 1)))=>//
        intro v; simp
        rw [hstar_comm]; simp
    · xwp; xseq_xlet_if_needed;
      xfor (fun a => xl ~~> ((xv + a) : ℤ))
      exact Nat.cast_nonneg n;
      intro i h1 h2 ; xwp ; xlet;
      · xapp ; xwp ; xlet ; xstep ; xapp ; xsimp
      · intro h; simp
        xfor (fun a => yl ~~> ((yv + a) : ℤ))
        · exact Nat.cast_nonneg n;
        intro i h1 h2 ; xwp ; xlet;
        · xapp ; xwp ; xlet ; xstep ; xapp ; xsimp
        · xsimp ; xsimp;
  )
  assumption


def regexp_grammar_injective ( i j : ℕ) ( t : trm):
  t ≠ [lang| ()] ->
  regexp_grammar i t =  regexp_grammar j t ->
  i = j := by
  intro ht h
  unfold regexp_grammar at h
  induction i generalizing j with
  | zero =>
    induction j with
    | zero => rfl
    | succ jn hjn =>
        cases jn
        case zero => simp_all
        case succ jj => simp_all
  | succ ik hik=>
    induction j with
    | zero =>
        cases ik
        case zero => simp_all
        case succ jj => simp_all
    | succ jn hjn =>
        simp
        cases ik
        case zero =>
          cases jn
          case zero => simp_all
          case succ jnn =>
            simp only [Nat.zero_add, Nat.add_zero] at h
            have tnq := trm_seq_neq t (regexp_grammar (jnn + 1) t)
            contradiction
        case succ ikk =>
          cases jn
          case zero =>
            simp only [Nat.zero_add, Nat.add_zero] at h
            have tnq := trm_seq_neq t (regexp_grammar (ikk + 1) t)
            simp_all
          case succ jnn =>
            simp_all
            unfold regexp_grammar at h
            specialize hik (jnn+1) h
            simp_all

def cfgexp_grammar_injective ( i j : ℕ) ( t1 t2 : trm):
  t1 ≠ [lang| ()] -> t2 ≠ [lang| ()] ->
  cfgexp_grammar i t1 t2 =  cfgexp_grammar j t1 t2 ->
  i = j := by
  intro ht1 ht2 h
  cases i
  case zero =>
    cases j
    case zero => simp
    case succ j1=>
      unfold cfgexp_grammar at h
      simp_all
  case succ i1 =>
    cases j
    case zero => unfold cfgexp_grammar at h; simp_all
    case succ j1 =>
      unfold cfgexp_grammar at h; simp [*] at h
      rcases h with ⟨h1,h2⟩
      apply regexp_grammar_injective at h1
      repeat assumption

set_option maxRecDepth 2000 in
set_option maxHeartbeats 6400000 in
lemma forwm_spec (xv yv : ℤ) :
  {
    [∗ in ⟪0,pay_index⟫ ∪ ⟪1,lang_index⟫ | xl ~~> xv ∗ yl ~~> yv]
  }
  [0| p in pay_index => prog_c1(⸨xl : Loc⸩, ⸨yl : Loc⸩, ⟨p.val.2⟩) ]
  [1| l in lang_index => l.val.fst(⸨xl: Loc⸩, ⸨yl : Loc⸩)]
  { v,
    [∗ n in ⟪0,pay_index⟫ ∪ ⟪1,lang_index⟫
      |
      hforall fun j =>
      hforall fun (_ :
      n ∈ (({⟨0, (default_trm, j)⟩} ∪
      {⟨1, ([lang| fun ⸨xl: Loc⸩ ⸨yl : Loc⸩=> {cfgexp_grammar j trm1 trm2}], default_payload)⟩}) : Set (trm × payload)ˡ)) =>
      (xl ~~> (xv + Int.ofNat j) ∗ yl ~~> (yv + Int.ofNat j))
    ]
  }
  := by
  unfold LGTM.triple
  set Hx := xl ~~> xv ∗ yl ~~> yv with hhx
  dsimp
  unfold LGTM.wp ; simp
  have eq : (⟪0, pay_index⟫ ∪ ⟪1, lang_index⟫) =
    ⋃ (i : Nat), ({⟨0, (default_trm, Int.ofNat i)⟩} ∪
      {⟨1, ([lang| fun ⸨xl: Loc⸩ ⸨yl : Loc⸩=> {cfgexp_grammar i trm1 trm2}], default_payload)⟩}) := by
    simp only [Set.iUnion_union_distrib] ; congr! 1
    · ext a ; rcases a with ⟨al, aval⟩ ; simp [pay_index]-- ; aesop
      constructor
      · rintro ⟨_, ⟨p, hp1, _⟩⟩ <;> subst_eqs ; simp ; exists Int.toNat p ; simp [hp1]
      · rintro ⟨_, ⟨p, hp1, _⟩⟩ <;> subst_eqs ; simp
    · ext a ; rcases a with ⟨al, aval⟩ ; simp [lang_index, lang_fun_list, lang_squeeze_list] ; aesop
  rw [← Set.biUnion_univ] at eq
  rw [eq]
  apply htriple_htriple_bighstar_partition
    (Q := fun i _ =>
      hforall fun j =>
      hforall fun (_ :
      i ∈ (({⟨0, (default_trm, j)⟩} ∪
      {⟨1, ([lang| fun ⸨xl: Loc⸩ ⸨yl : Loc⸩=> {cfgexp_grammar j trm1 trm2}], default_payload)⟩}) : Set (trm × payload)ˡ)) =>
      (xl ~~> (xv + Int.ofNat j) ∗ yl ~~> (yv + Int.ofNat j)))
  on_goal 1=> {
    intro i _ j _ h
    simp_all ; constructor
    on_goal 2=> aesop
    intro h1
    dsimp [trm_funs] at h1; simp_all
    apply cfgexp_grammar_injective (t1 := trm1) (t2 := trm2) at h1
    aesop
    unfold trm1; simp
    unfold trm2; simp
  }
  on_goal 2=> intros ; rfl
  { intro k _ ; dsimp only
    have tmp := example3_single_iter (sn := trm_funs [trm_varl "xl", trm_varl "yl"] (cfgexp_grammar k trm1 trm2)) (xl := xl) (yl := yl) (n := k) (yv := yv) (xv := xv) (by rfl)
    unfold LGTM.wp at tmp ; dsimp only [LGTM.SHTs.set, LGTM.SHTs.htrm] at tmp
    simp only [labSet, Set.mem_singleton_iff, exists_eq_left,
      Set.setOf_eq_eq_singleton', Set.union_empty] at tmp
    apply htriple_conseq
    rw [hwp_ht_eq] at tmp ; apply tmp
    { whnf ; simp [lang_index, lang_fun_list, lang_squeeze_list, pay_index] }
    { apply hhimpl_refl }
    { intro hv hh hpre ; whnf at hpre ⊢ ; intro a ; specialize hpre a ; split
      next h=>
        simp only [h, reduceIte] at hpre
        whnf ; intro j ; whnf ; intro h'
        simp at h h' ; rcases h with (h | h) <;> rcases h' with (h' | h') <;> rw [h'] at h <;> simp at h
        { simp [trm_funs] at h
          apply cfgexp_grammar_injective at h
          aesop
          unfold trm1; simp
          unfold trm2; simp
        }
        { aesop }
      next h=> simp only [Int.ofNat_eq_coe] at h ; simp only [h, reduceIte] at hpre ; assumption
    }
  }
