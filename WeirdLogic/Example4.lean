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
import WeirdLogic.GramDisjStandard
import WeirdLogic.WUnary

import WeirdLogic.GramSeq
import WeirdLogic.Example3_1
import WeirdLogic.Example0

open Unary prim val trm
open ContextFreeGrammar
-- #check Set.BijOn
open Classical

namespace WeirdLogic.Example4

/- L -> S1; S2
  S1 -> trm1; S1; trm2
        | ε
  S2 -> trm3 | trm4
  L = {trm1ⁿ;trm2ⁿ;(trm3|trm4) : n ≥ 0}
  context free + seq rule
-/
/-
def trm1 : trm := [lang| let xx := !xl in let temp0 := xx + 1 in xl := temp0]
def trm2 : trm := [lang| let yy := !yl in let temp1 := yy + 1 in yl := temp1]
-/
def trm3 : trm := [lang| let xx := !xl in let yy := !yl in let temp1 := xx + yy in xl := temp1]
def trm4 : trm := [lang| let xx := !xl in let yy := !yl in let temp1 := xx - yy in xl := temp1]
def r1 : ContextFreeRule trm String :=
  {
    input := "L",
    output := [Symbol.nonterminal "S1", Symbol.nonterminal "S2"],
  }

def r2 : ContextFreeRule trm String :=
  {
    input := "S1",
    output := [Symbol.terminal Example3.trm1, Symbol.nonterminal "S1", Symbol.terminal Example3.trm2],
  }

def r3 : ContextFreeRule trm String :=
  {
    input := "S1",
    output := [],
  }

def r4 : ContextFreeRule trm String :=
  {
    input := "S2",
    output := [Symbol.terminal trm3, Symbol.terminal trm4],
  }

def cfg1 : ContextFreeGrammar trm :=
  {
    NT := String,
    initial := "S1",
    rules := Finset.mk {r1, r2, r3, r4} (by unfold r1 r2 r3 r4 Example3.trm1 Example3.trm2; simp)
  }

def l1 : Language trm := cfg1.language

/-
lang_def' prog_c1_pre :=
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

lang_def' prog_c1_post :=
  fun ⸨xl: Loc⸩ ⸨yl: Loc⸩ ⸨pb:Val⸩ =>
    let xx := !xl in
    let yy := !yl in
    if pb > 10 then
      let temp0 := xx + yy in
      yl := temp0
    else
      let temp1 := xx - yy in
      yl := temp1
-/

lang_def' prog_c1 :=
  fun ⸨xl: Loc⸩ ⸨yl: Loc⸩ ⸨pa:Val⸩ ⸨pb:Val⸩=>
    Example3.prog_c1(⸨xl:Loc⸩, ⸨yl:Loc⸩, pa);
    Example0.prog_c1(⸨xl:Loc⸩, ⸨yl:Loc⸩, pb)
/-
def regexp_grammar : ℕ → trm → trm
  | 0, _ => trm_val val_unit
  | 1, t => t
  | (n+1), t => trm_seq t (regexp_grammar n t)

def cfgexp_grammar : ℕ → trm → trm → trm
  | 0, _, _ => trm_val val_unit
  | n, t1, t2 => trm_seq (regexp_grammar n t1) (regexp_grammar n t2)
-/

def orexp_grammar : Bool → trm
  | true => Example0.trm1
  | false => Example0.trm2

syntax "⌜" term "⌝" : lang

macro_rules
  | `([lang| ⌜ $f:term ⌝($xs:lang,*) ])     => `(trm_call ($f) [ $[[lang|$xs:lang]],* ])

def lang_sn1 i :=
  Example3.cfgexp_grammar i Example3.trm1 Example3.trm2

def lang_part1 i :=
  [lang| ⌜ [lang| fun ⸨xl: Loc⸩ ⸨yl : Loc⸩ => { (lang_sn1 i) }] ⌝(⸨xl: Loc⸩, ⸨yl : Loc⸩) ]

def lang_part2 b :=
  [lang| ⌜ (orexp_grammar b) ⌝(⸨xl: Loc⸩, ⸨yl : Loc⸩) ]

def lang_squeeze_list': Set trm :=
  {trm_seq
    (lang_part1 i)
    (lang_part2 j)
    | (i : ℕ) (j : Bool) }

def trm_seq_fst : trm → trm
  | trm_seq t1 _ => t1
  | _ => default_trm

def trm_seq_snd : trm → trm
  | trm_seq _ t2 => t2
  | _ => default_trm

def trm_call_fun : trm → trm
  | trm_call t1 _ => t1
  | _ => default_trm

def trm_call_args : trm → List trm
  | trm_call _ args => args
  | _ => []

/-
def lang_squeeze_list: Set trm :=
  {trm_seq (cfgexp_grammar i trm1 trm2) (trm3) | i : ℕ } ∪ {trm_seq (cfgexp_grammar i trm1 trm2) (trm4) | i : ℕ }

def lang_fun_set : Set trm :=
  {[lang| fun ⸨xl: Loc⸩ ⸨yl : Loc⸩ => {tt}] | tt ∈ lang_squeeze_list' }
-/
def pay_index : Set (trm × Example3.payload × payload) :=
  { x |
    ∃ p1 ∈ @Set.univ Example3.payload, ∃ p2 ∈ @Set.univ payload, (default_trm,(p1,p2))=x
  }

def lang_index : Set (trm × Example3.payload × payload ):=
  { (l, (Example3.default_payload,default_payload)) | l ∈ lang_squeeze_list'}
/-
def lang_index1 : Set (trm × payload × payload ):=
  { (l, (default_payload,default_payload)) | l  ∈ {trm_seq (cfgexp_grammar i trm1 trm2) (trm3) | i : ℕ } }

def lang_index2 : Set (trm × payload × payload ):=
  { (l, (default_payload,default_payload)) | l ∈ {trm_seq (cfgexp_grammar i trm1 trm2) (trm4) | i : ℕ } }
/-
lemma lang_union :
  lang_index = lang_index1 ∪ lang_index2 := by
  unfold lang_index1 lang_index2 lang_index lang_squeeze_list'
  aesop
-/
lemma lang_disjoint :
  Disjoint lang_index1 lang_index2 := by
  unfold lang_index1 lang_index2
  simp_all
  apply Set.disjoint_iff_inter_eq_empty.mpr
  ext e; simp
  intro n h1 n2
  rw [← h1]
  -- unfold trm_funs; simp
  -- unfold trm_funs; simp
  -- unfold trm_funs; simp
  -- intro hh
  unfold trm4 trm3
  simp

def pay_index1 : Set (trm × payload × payload) :=
  {x | ∃ p1 ∈ @Set.univ payload, ∃ p2 ∈ @Set.univ payload, p2 > 10 ∧ (default_trm,(p1,p2)) = x }

def pay_index2 : Set (trm × payload × payload) :=
  {x | ∃ p1 ∈ @Set.univ payload, ∃ p2 ∈ @Set.univ payload, p2 ≤ 10 ∧ (default_trm,(p1,p2)) = x }

lemma pay_union :
  pay_index = pay_index1 ∪ pay_index2 := by
  unfold pay_index pay_index1 pay_index2
  simp
  ext x
  constructor <;> simp_all;
  · intro x_1 h h2
    subst h2
    simp_all only [Prod.mk.injEq, true_and, exists_eq_right_right, exists_eq_right]
    exact Int.lt_or_le 10 h
  · intro h
    cases h with
    | inl h1 =>
      rcases h1 with ⟨p1,p2,hh1,hh2⟩
      subst hh2
      use p1; simp
    | inr h2 =>
      rcases h2 with ⟨p1,p2,hh1,hh2⟩
      use p1,p2

lemma pay_disjoint :
  Disjoint pay_index1 pay_index2 := by
  unfold pay_index1 pay_index2
  simp_all
  apply Set.disjoint_iff_inter_eq_empty.mpr
  ext e; simp
  intro p1 p2 h1 h2 p3 p4 h3
  subst h2
  simp
  intro h heq
  rw [heq] at h3
  have tmp := not_le_of_gt h1
  contradiction
-/
/-
  This is the proof for option 1
-/

attribute [-simp] Bool.exists_bool
-- attribute [simp] trm_seq_fst trm_seq_snd trm_call_fun

-- theorem exists_labType {p : ℕ → α → Prop} :
--   (∃ (x : αˡ), p x.lab x.val) ↔ (∃ (l : ℕ) (a : α), p l a) := by
--   constructor
--   · rintro ⟨⟨xl, xval⟩, h⟩ ; exists xl, xval
--   · rintro ⟨l, a, h⟩ ; exists ⟨l, a⟩
theorem exists_labType {p : αˡ → Prop} :
  (∃ (x : αˡ), p x) ↔ (∃ (l : ℕ) (a : α), p ⟨l, a⟩) := by
  constructor
  · rintro ⟨⟨xl, xval⟩, h⟩ ; exists xl, xval
  · rintro ⟨l, a, h⟩ ; exists ⟨l, a⟩

theorem forall_labType {p : αˡ → Prop} :
  (∀ (x : αˡ), p x) ↔ (∀ (l : ℕ) (a : α), p ⟨l, a⟩) := by
  constructor <;> aesop

set_option maxRecDepth 2000 in
set_option maxHeartbeats 6400000 in
lemma example4_spec (xv : ℤ) (yv : ℤ):
  let tfunc (i : trm) := [lang| fun ⸨xl: Loc⸩ ⸨yl : Loc⸩ => {i}]
  {
    [∗ in ⟪0,pay_index⟫ ∪ ⟪1,lang_index⟫ | xl ~~> xv ∗ yl ~~> yv]
  }
  [0| p in pay_index => prog_c1(⸨xl : Loc⸩, ⸨yl : Loc⸩, ⟨Int.ofNat p.val.2.1⟩, ⟨p.val.2.2⟩) ]
  [1| l in lang_index => ⌜ tfunc l.val.fst ⌝(⸨xl: Loc⸩, ⸨yl : Loc⸩)]
  { v,
    fun h => ∀ ll ∈ lang_index, ∃ pp ∈ pay_index , h ⟨1, ll⟩ = h ⟨0, pp⟩
  }
  := by
  intro tfunc
  yin 1 :
    try (first
      | (apply ywp_lemma_funs;
         { move=> ?; rfl }
         { move=> ?; rfl }
         { move=> ?; rfl }
         { move=> ?; simp [Unary.get_vars, Unary.type_match] } ))
  yin 0 :
    try (first
      | (apply ywp_lemma_funs;
         { move=> ?; rfl }
         { move=> ?; rfl }
         { move=> ?; rfl }
         { move=> ?; simp [Unary.get_vars, Unary.type_match] } ))
  dsimp [Unary.func_call_ctx_prepare]
  try simp [isubstE, Unary.reduce_call_isubst]
  clear tfunc

  -- for simplicity, use the axiom of choice to build the oracle
  have tmp := fun_union_exists (fun n => Set.singleton
    ([lang| fun ⸨xl: Loc⸩ ⸨yl : Loc⸩ => { (lang_sn1 n) }])) Set.univ
  specialize tmp ?_
  { simp ; intro i j hneq ; simp [Set.singleton, trm_funs, lang_sn1]
    intro heq ; apply Example3.cfgexp_grammar_injective at heq
    · contradiction
    · unfold Example3.trm1 ; simp
    · unfold Example3.trm2 ; simp
  }
  rcases tmp with ⟨aux, haux⟩ ; simp [Set.singleton] at haux

  apply LGTM.triple_conseq-- ; apply hhimpl_refl ; rotate_left
  rotate_left ; rotate_left
  apply weird_gram_seq_full_prod
    (α := (trm × Example3.payload × payload)ˡ)
    (β := (trm × Example3.payload)ˡ)
    (γ := (trm × payload)ˡ)
    (sht_prog1 := LGTM.SHT.mk ⟪0, Example3.pay_index⟫
      fun p ↦ Example3.prog_c1.trm_call [xl, yl, [lang| ⟨Int.ofNat p.val.2⟩]])
    (sht_lang1 := LGTM.SHT.mk ⟪1, Example3.lang_index⟫
      fun l ↦ l.val.1.trm_call [xl, yl])
    (sht_prog2 := LGTM.SHT.mk ⟪0, Example0.pay_index⟫
      fun p ↦ Example0.prog_c1.trm_call [xl, yl, [lang| ⟨p.val.2⟩]])
    (sht_lang2 := LGTM.SHT.mk ⟪1, Example0.lang_index⟫
      fun l ↦ l.val.1.trm_call [xl, yl])
    (proj1 := fun a => ⟨a.lab, (trm_call_fun <| trm_seq_fst a.val.1, a.val.2.1)⟩)
    (proj2 := fun a => ⟨a.lab, (trm_call_fun <| trm_seq_snd a.val.1, a.val.2.2)⟩)
    (part1_oracle := fun a => ⟨0, (default_trm, aux a.val.1 |>.getD 0)⟩)
    (H1 := fun _ => xl ~~> xv ∗ yl ~~> yv)
    (Q1 := fun n =>
      hforall fun j =>
      hforall fun (_ :
      n ∈ (({⟨0, (default_trm, j)⟩} ∪
      {⟨1, ([lang| fun ⸨xl: Loc⸩ ⸨yl : Loc⸩=> {Example3.cfgexp_grammar j Example3.trm1 Example3.trm2}], Example3.default_payload)⟩}) : Set (trm × Example3.payload)ˡ)) =>
      (xl ~~> (xv + Int.ofNat j) ∗ yl ~~> (yv + Int.ofNat j)))
  { simp [lang_index, lang_squeeze_list']
    exists (((lang_part1 0).trm_seq (lang_part2 false)), Example3.default_payload, default_payload)
    simp }
  { simp [pay_index] ; exists (default_trm, Nat.zero, 0) ; simp }
  { clear aux haux
    ext a ; dsimp only ; rcases a with ⟨⟨al, ⟨atrm, ap⟩⟩, ⟨bl, ⟨btrm, bp⟩⟩⟩
    simp [lang_index, lang_squeeze_list',
      Example3.lang_index, Example3.lang_fun_list, Example3.lang_squeeze_list,
      Example0.lang_index, Example0.lang_index'_unfold,
      lang_part1, lang_part2]
    simp [← lang_sn1.eq_1, exists_labType, Bool.exists_bool, orexp_grammar]
    constructor
    · intro h ; aesop
    · intro h ; exists 1 ; aesop
  }
  { clear aux haux
    ext a ; dsimp only ; rcases a with ⟨⟨al, ⟨atrm, ap⟩⟩, ⟨bl, ⟨btrm, bp⟩⟩⟩
    simp [pay_index,
      Example3.pay_index,
      Example0.pay_index, Example0.pay_index',
      default_trm]
    simp [exists_labType]
    aesop
  }
  { rw [disjoint_label_set] ; left ; decide }
  { rw [disjoint_label_set] ; left ; decide }
  { rw [disjoint_label_set] ; left ; decide }
  { simp ; ext a ; rcases a with ⟨al, ⟨atrm, ap⟩⟩
    simp [Example3.pay_index, Example3.lang_index, Example3.lang_fun_list, Example3.lang_squeeze_list,
      exists_labType, ← lang_sn1.eq_1]
    constructor
    { rintro ⟨_, _⟩ ; subst al atrm
      exists 1, trm_funs [trm_varl "xl", trm_varl "yl"] (lang_sn1 ap)
      simp ; rw [(haux _ ap).mp rfl] ; rfl
    }
    { simp ; intros ; subst_eqs ; simp }
  }
  { dsimp only
    rintro hh hpre ⟨ll, ⟨ltrm, lp⟩⟩ lin
    -- on the lang side first
    whnf at hpre ; unfold hforall at hpre ; dsimp at hpre
    have hpre' := hpre ⟨ll, ⟨ltrm, lp⟩⟩ ; rw [if_pos] at hpre'
    on_goal 2=> simp only [Set.mem_union] ; right ; assumption
    simp [Example3.lang_index, Example3.lang_fun_list, Example3.lang_squeeze_list] at lin
    rcases lin with ⟨_, ⟨n, lin⟩, _⟩ ; subst ll lp ; dsimp
    specialize hpre' n (by subst ltrm ; simp)
    -- on the payload side
    specialize hpre ⟨0, ⟨default_trm, n⟩⟩ ; rw [if_pos] at hpre
    on_goal 2=> simp [Example3.pay_index]
    specialize hpre n (by simp)
    constructor
    on_goal 1=> simp [Example3.pay_index]
    -- trick
    have tmp := HPropExact.isExact _ _ hpre' hpre
    rw [(haux ltrm n).mp (by subst ltrm ; rfl)] ; exact tmp
  }
  { dsimp
    rintro ⟨il, ⟨itrm, ip⟩⟩ hin
    simp [Example3.pay_index, Example3.lang_index, Example3.lang_fun_list, Example3.lang_squeeze_list] at hin
    constructor
    intro he1 he2 h1 h2 ; simp [hforall] at h1 h2
    rcases hin with (hin | hin)
    · specialize h1 ip (by left ; simp [hin])
      specialize h2 ip (by left ; simp [hin])
      have tmp := HPropExact.isExact _ _ h1 h2 ; exact tmp
    · rcases hin with ⟨_, ⟨n, hin⟩, _⟩ ; subst_eqs ; simp at h1 h2
      specialize h1 n rfl ; specialize h2 n rfl
      have tmp := HPropExact.isExact _ _ h1 h2 ; exact tmp
  }
  { dsimp only
    rintro ⟨al, ⟨atrm, ap1, ap2⟩⟩ ; dsimp
    intro hin ; simp [lang_index, lang_squeeze_list'] at hin
    rcases hin with ⟨_, ⟨p1, p2, _⟩, _, _⟩ ; subst_eqs
    dsimp only [trm_call_fun, trm_seq_fst, trm_seq_snd, lang_part1, lang_part2, trm_funs, lang_sn1]
    -- bug ????
    -- simp [isubstE]
    dsimp only [isubst, isubst.go] ; congr! 1
    { congr! 3 ; rw [Example3.cfgexp_grammar_isubst] ; rfl }
    { cases p2 <;> rfl }
  }
  { simp }
  { apply Example3.example3_spec_ }
  { rintro ⟨jl, ⟨jtrm, jp⟩⟩ jin
    simp [Example3.pay_index, Example3.lang_index, Example3.lang_fun_list, Example3.lang_squeeze_list] at jin
    rcases jin with ⟨_, ⟨n, jin⟩, _⟩ ; subst jl jp ; symm at jin
    dsimp only
    -- involving the oracle here
    apply LGTM.triple_conseq
    on_goal 3=> apply Example0.example1_spec (xv + Int.ofNat (aux jtrm |>.getD 0)) (yv + Int.ofNat (aux jtrm |>.getD 0))
    { apply bighstar_himpl
      intro a ain hh hpre ; simp [hforall] at hpre ; specialize hpre n jin
      rw [(haux jtrm n).mp jin] ; exact hpre
    }
    { intro hv hh hpre ; simp
      rintro ⟨ll, ⟨ltrm, lp⟩⟩ lin ; simp at lin ; subst ll
      simp [Example0.lang_index, Example0.lang_index'_unfold, Example0.pay_index, exists_labType] at hpre ⊢
      intro h ; apply hpre at h
      clear *- h ; aesop
    }
  }
  { simp }
  { simp [forall_labType, exists_labType, lang_index, lang_squeeze_list', pay_index]
    intro hv hh hpre a b c d ; specialize hpre _ a b c rfl d ; exact hpre
  }

/- Previously, constraints for payloads in the heap are in the post-condition
    -- ∧ arr⟨{⟨0,p⟩}⟩(pa , i in pa_len => p.2.1[i]!) h
    -- ∧ arr⟨{⟨0,p⟩}⟩(pb , i in pb_len => p.2.2[i]!) h
  And pre-condition is default
  -- arr⟨⋆⟩(pa , i in pa_len =>g i) ∗
  -- arr⟨⋆⟩(pb , i in pb_len =>q i)
-/
