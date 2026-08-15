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
import WeirdLogic.WUnary

open Unary prim val trm
open ContextFreeGrammar

namespace WeirdLogic.Example2

/- L -> S1
  S1 -> trm1; S1
        | ε
  L = {trm1ⁿ, n ≥ 0}
  regular + for rule
  for a language instance in type trm, the outermost type must be trm_funs -/

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

/- old format -/
  -- {
  --   xl ~⟨i in {⟨0,(default_trm, (Int.ofNat n))⟩} ∪ {⟨1,(sn,default_payload)⟩}⟩~> xv
  -- }
  -- [0| p in {(default_trm, (Int.ofNat n))} => prog_c1(⸨xl: Loc⸩, ⟨p.val.2⟩)]
  -- [1| l in {(sn,default_payload)} => l.val.fst(⸨xl: Loc⸩)]
  -- { v,
  --   fun h => ∀ l ∈ ({(sn,default_payload)} : Set (trm × payload)), ∃ p ∈ ({(default_trm, (Int.ofNat n))} : Set (trm × payload)) , h ⟨1, l⟩= h ⟨0, p⟩
  -- }
lemma example2_single_iter (xv : ℤ) :
  ∀ n : ℕ,
  sn = [lang| fun ⸨xl: Loc⸩ => {regexp_grammar n trm1}] →
  [∗ in {⟨0, (default_trm, Int.ofNat n)⟩} ∪ {⟨1, (sn, default_payload)⟩}| xl ~~> xv] ==>
  LGTM.wp
    [{ s := ⟪0, {(default_trm, Int.ofNat n)}⟫, ht := fun p ↦ prog_c1.trm_call [xl, [lang| ⟨p.val.2⟩]] },
     { s := ⟪1, {(sn, default_payload)}⟫, ht := fun l ↦ l.val.1.trm_call [xl] }]
    fun _ h => ∀ l ∈ ({(sn, default_payload)} : Set (trm × payload)), ∃ p ∈ ({(default_trm, Int.ofNat n)} : Set (trm × payload)), h ⟨1, l⟩ = h ⟨0, p⟩
  := by
  intro n hsn
  unfold LGTM.wp labSet
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

set_option maxRecDepth 2000 in
set_option maxHeartbeats 6400000 in
lemma example2_spec (xv : ℤ):
  {
    xl ~⟨_ in ⟪0,pay_index⟫ ∪ ⟪1,lang_index⟫⟩~> xv
  }
  [0| p in pay_index => prog_c1(⸨xl: Loc⸩, ⟨p.val.2⟩)]
  [1| l in lang_index => l.val.fst(⸨xl: Loc⸩)]
  { v,
    fun h => ∀ l ∈ lang_index, ∃ p ∈ pay_index , h ⟨1, l⟩= h ⟨0, p⟩
  }
  := by
  unfold LGTM.triple hhsingle
  dsimp
  rw [← bighstar_hhstar_disj_dir (s₁ := {⟨0,(default_trm,p)⟩ | p <0 }) (s₂ := {⟨0,(default_trm,p)⟩ | p ≥ 0} ∪ ⟪1, lang_index⟫ )]
  rotate_left
  { apply Set.disjoint_union_right.mpr
    simp;
    constructor
    · srw Set.disjoint_iff_inter_eq_empty Set.eq_empty_iff_forall_notMem=>x//==
      move=> x1 h1 [x2] h2 Z; cases Z
      exact lt_irrefl x1 (lt_of_lt_of_le h1 h2)
    · unfold labSet
      srw Set.disjoint_iff_inter_eq_empty Set.eq_empty_iff_forall_notMem=>x//==
      move=>y1 H1 [y2] H2 Z; cases Z
      simp
  }
  { rw [←Set.union_assoc]
    apply Set.union_eq_union_iff_right.mpr
    have eq : {x | ∃ p < 0, ⟨0, (default_trm, p)⟩ = x} ∪ {x | ∃ p ≥ 0, ⟨0, (default_trm, p)⟩ = x} = ⟪0, pay_index⟫ := by
      unfold labSet pay_index
      ext x
      constructor
      · intro hx
        rcases hx with ⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩
        · simp;
        · simp
      · intro hx
        rcases hx with ⟨p, hp, rfl⟩
        simp_all only [Set.mem_univ, true_and, Set.mem_setOf_eq, ge_iff_le, Set.mem_union, Labeled.mk.injEq]
        obtain ⟨fst, snd⟩ := p
        obtain ⟨w, h⟩ := hp
        simp_all only [Prod.mk.injEq, true_and, exists_eq_right]
        obtain ⟨left, right⟩ := h
        subst right left
        exact lt_or_ge w 0
    rw [eq]
    constructor <;> apply Set.subset_union_left
  }
  /- Step 1: remove negative payloads -/
  apply weird_weaken_lemma' (s' := {(default_trm,p) | p ≥ 0 })=>//
  unfold pay_index; simp; simp; apply disjoint_label_set.mpr; simp
  {
    /- first 1/2: p <0 -/
    dsimp [LGTM.wp, LGTM.SHTs.htrm]
    rw [hwp_ht_eq (ht₂ := (fun (p : (trm × payload)ˡ) => prog_c1.trm_call [xl, [lang| ⟨p.val.2⟩]]))] --remove union set
    on_goal 2=> simp only [Set.EqOn, fun_insert, Set.union_empty] ; intro a b ; simp only [b, reduceIte]
    have tmp := htriple_prod (α := (trm × payload)ˡ) (s := ⟪0, pay_index \ {x | ∃ p ≥ 0, (default_trm, p) = x}⟫ ∪ ∅)
      (ht := open Classical in (fun a => prog_c1.trm_call [xl, [lang| ⟨a.val.2⟩]]))
      (H := fun _ => xl ~~> xv)
      (Q := fun i v => fun h => i ∉ ⟪0, {x | ∃ p <0, (default_trm, p) = x}⟫ -> h = ∅)
    specialize tmp (by
      clear tmp
      intro a ha
      unfold prog_c1
      xwp ; xapp_pre
      apply xfor_empty_lemma
      {
        simp [pay_index] at ha
        rcases ha with ⟨ ha1,⟨p,ha2⟩,ha3⟩
        specialize ha3 p
        simp_all
        rw [←ha2]
        simp
        assumption
      }
      unfold hsingle qimpl himpl
      intro v h hh haa
      simp [pay_index] at ha
      rcases ha with ⟨ ha1,⟨p,ha2⟩,ha3⟩
      specialize ha3 p
      specialize haa ha1 p
      simp_all only [not_true_eq_false, imp_false, not_le]
    )
    have eq : [∗i in ⟪0, pay_index \ {x | ∃ p ≥ 0, (default_trm, p) = x}⟫ ∪ ∅| xl ~~> xv] = [∗i in {x | ∃ p < 0, ⟨0, (default_trm, p)⟩ = x}| xl ~~> xv] := by
      apply bighstar_set_eq
      unfold labSet; rw [Set.union_empty]
      unfold pay_index;
      ext x
      constructor
      · intro ⟨x₁, ⟨⟨p, ⟨h1,h2⟩⟩, hnot⟩, hx⟩
        simp at hnot
        refine ⟨p, ?_, ?_⟩
        · by_contra hge
          have hp0 : 0 ≤ p := le_of_not_lt hge
          have hcontra := hnot p hp0 h2
          contradiction
        · rw [←hx, ←h2]
      · intro ⟨p, hp, hx⟩
        refine ⟨(default_trm, p), ⟨⟨p, trivial, rfl⟩, ?_⟩, hx⟩
        intro ⟨p', hp', heq⟩
        simp [heq] at hp' hp
        simp_all
        exact lt_irrefl p (lt_of_lt_of_le hp hp')

    rw [←eq]; clear eq
    apply hhimpl_trans ; apply tmp
    clear tmp
    apply hwp_conseq
    unfold pay_index
    ysimp
    unfold bighstar bighstarDef ; open Classical in simp
    intro h hh a ha
    specialize hh a
    by_cases h : a.lab = 0
    · specialize ha h
      have hfalse :
        ¬((a.lab = 0) ∧ (∃ p, (default_trm, p) = a.val) ∧ ∀ (x : payload), 0 ≤ x → ¬(default_trm, x) = a.val) := by
        intro hcon
        rcases hcon with ⟨_, ⟨p, hp⟩, hforall⟩
        rcases ha p hp with ⟨x, hx₀, hxval⟩
        have hcontra := hforall x hx₀
        contradiction
      simp [hfalse] at hh
      assumption
    · simp [h] at hh
      assumption
  }
  dsimp
  set pay_index2 : Set (trm × payload) := {x | ∃ p ≥ 0, (default_trm, p) = x} with hp2
  have pidx_eq : {x | ∃ p ≥ 0, ⟨0, (default_trm, p)⟩ = x} = ⟪0,pay_index2⟫ := by
    unfold labSet pay_index2
    simp
  rw [pidx_eq]; clear pidx_eq
  /- Step 2: Infinite disjoint lemma -/
  apply weird_infdisj_lemma (s1 := pay_index2) (s2 := lang_index) (Hx := xl ~~> xv)
    (f := fun i => (default_trm, Int.ofNat i))
    (g := fun i => ([lang| fun ⸨xl: Loc⸩ => {regexp_grammar i trm1}],default_payload))
    (Idx := @Set.univ ℕ)
  simp; simp;
  { unfold pay_index2; simp;
    ext x
    constructor
    · intro ⟨p, hp₁, hp₂⟩
      have : p = Int.ofNat (Int.toNat p) := by
        subst hp₂
        simp_all only [ge_iff_le, Int.ofNat_eq_coe, Int.ofNat_toNat, sup_of_le_left, pay_index2]
      rw [←hp₂, this]
      exact ⟨Int.toNat p, rfl⟩
    · intro ⟨n, hn⟩
      use (n : Int)
      constructor
      · exact Int.ofNat_nonneg n
      · rw [←hn]
  }
  { unfold lang_index lang_fun_list lang_squeeze_list; simp; rfl }
  { simp; intro i j h; rw [Prod.ext_iff] at h;
    rcases h with ⟨h1,h2⟩
    simp_all
  }
  {
    intro i j h; rw [Prod.ext_iff] at h;
    rcases h with ⟨h1,h2⟩
    simp_all
    unfold trm_funs at h1; simp_all
    unfold trm_funs at h1
    apply regexp_grammar_injective (t := trm1)
    unfold trm1; simp
    assumption
  }
  intro k hk2
  dsimp
  have kreplace : ↑k = Int.ofNat k := by simp
  rw [kreplace]; clear kreplace
  have pr : {⟨0, (default_trm, Int.ofNat k)⟩} = ⟪0,{(default_trm, Int.ofNat k)}⟫ := by unfold labSet; simp
  have lr : {⟨1, (trm_funs [trm_varl "xl"] (regexp_grammar k trm1), default_payload)⟩} = ⟪1, {(trm_funs [trm_varl "xl"] (regexp_grammar k trm1), default_payload)}⟫ := by unfold labSet; simp
  rw [pr,lr]; clear pr lr
  have idx_eq : insert ⟨0, (default_trm, Int.ofNat k)⟩ ⟪1, {(trm_funs [trm_varl "xl"] (regexp_grammar k trm1), default_payload)}⟫ =
    {⟨0, (default_trm, Int.ofNat k)⟩ } ∪ {⟨1, (trm_funs [trm_varl "xl"] (regexp_grammar k trm1), default_payload)⟩} := by
    unfold labSet; aesop
  rw [idx_eq]; clear idx_eq
  apply example2_single_iter (sn := trm_funs [trm_varl "xl"] (regexp_grammar k trm1)) (xl := xl) (n := k) (xv := xv)
  simp

end WeirdLogic.Example2
