import Mathlib.Computability.ContextFreeGrammar

import Lgtm.Hyper.ProofMode
import Lgtm.Hyper.ArraysFun
import Lgtm.Unary.Lang
import Lgtm.Experiments.HyperCommon

import WeirdLogic.Gram
import WeirdLogic.WLogic
import WeirdLogic.WTriple
import WeirdLogic.WUtil
import WeirdLogic.GramDisjStandard
import WeirdLogic.WUnary

import WeirdLogic.GramSeq
import WeirdLogic.Examples.ForWM
import WeirdLogic.Examples.IfWM

open Unary prim val trm
open ContextFreeGrammar
-- #check Set.BijOn
open Classical

namespace WeirdLogic.VulnWM

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


lang_def' prog_c1 :=
  fun ⸨xl: Loc⸩ ⸨yl: Loc⸩ ⸨pa:Val⸩ ⸨pb:Val⸩=>
    Example3.prog_c1(⸨xl:Loc⸩, ⸨yl:Loc⸩, pa);
    Example0.prog_c1(⸨xl:Loc⸩, ⸨yl:Loc⸩, pb)

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


def pay_index : Set (trm × payload × payload) :=
  { x |
    ∃ p1 ∈ @Set.univ payload, ∃ p2 ∈ @Set.univ payload, (default_trm,(p1,p2))=x
  }

def lang_index : Set (trm × payload × payload ):=
  { (l, (default_payload,default_payload)) | l ∈ lang_squeeze_list'}


attribute [-simp] Bool.exists_bool

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
lemma vulnwm_spec (xv : ℤ) (yv : ℤ):
  let tfunc (i : trm) := [lang| fun ⸨xl: Loc⸩ ⸨yl : Loc⸩ => {i}]
  {
    [∗ in ⟪0,pay_index⟫ ∪ ⟪1,lang_index⟫ | xl ~~> xv ∗ yl ~~> yv]
  }
  [0| p in pay_index => prog_c1(⸨xl : Loc⸩, ⸨yl : Loc⸩, ⟨p.val.2.1⟩, ⟨p.val.2.2⟩) ]
  [1| l in lang_index => ⌜ tfunc l.val.fst ⌝(⸨xl: Loc⸩, ⸨yl : Loc⸩)]
  { v,
    fun h => ∀ ll ∈ lang_index, ∃ pp ∈ pay_index , h ⟨1, ll⟩ = h ⟨0, pp⟩
  }
  := by
  intro tfunc

  let s' := { (default_trm, p, p2) | (p : ℤ) (p2 : ℤ) (_h : 0 ≤ p) }
  rw [← bighstar_hhstar_disj_dir
    (s₁ := ⟪0, pay_index⟫ \ ⟪0, s'⟫)
    (s₂ := ⟪0, s'⟫ ∪ ⟪1, lang_index⟫)]
  on_goal 2=>
    simp [disjoint_label_set, pay_index, s']
    rw [Set.disjoint_iff_forall_ne]
    aesop
  on_goal 2=>
    ext a ; rcases a with ⟨_, ⟨_, _, _⟩⟩ ; simp [s', pay_index] ; aesop ; omega

  apply weird_weaken_lemma (s' := s')
  { simp }
  { simp }
  { simp [s', pay_index] ; aesop }
  { simp [disjoint_label_set] }
  { simp }
  { simp
    have tmp := htriple_prod (α := (trm × payload × payload)ˡ)
      (s := ⟪0, pay_index \ s'⟫)
      (ht := fun p ↦ prog_c1.trm_call [xl, yl, [lang| ⟨p.val.2.1⟩], [lang| ⟨p.val.2.2⟩]])
      (H := fun _ => xl ~~> xv ∗ yl ~~> yv)
      (Q := fun _ _ => htop)
    specialize tmp ?_
    { clear tmp
      rintro ⟨_, ⟨_, _, _⟩⟩ ha ; simp [pay_index, s'] at ha ; rcases ha with ⟨_, _, ha⟩ ; subst_eqs ; simp at ha
      unfold prog_c1 ; dsimp
      xwp; xseq_xlet_if_needed
      unfold Example3.prog_c1
      xwp; xseq_xlet_if_needed
      apply xfor_empty_lemma ; omega
      xsimp
      apply xfor_empty_lemma ; omega
      xsimp
      unfold Example0.prog_c1
      xstep ; xstep ; xwp ; xapp triple_gt
      rename_i snd rr ; cases (decide (snd > 10)) <;> xwp <;> xif <;> intros <;> try contradiction
      · xstep ; xapp ; xsimp
      · xstep ; xapp ; xsimp
    }
    unfold LGTM.wp ; simp ; rw [hwp_ht_eq] ; apply htriple_conseq ; apply tmp
    · ysimp
    · ysimp
    · whnf ; aesop
  }
  simp [s']

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
    (α := (trm × payload × payload)ˡ)
    (β := (trm × payload)ˡ)
    (γ := (trm × payload)ˡ)
    (sht_prog1 := LGTM.SHT.mk ⟪0, Example3.pay_index⟫
      fun p ↦ Example3.prog_c1.trm_call [xl, yl, [lang| ⟨p.val.2⟩]])
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
      {⟨1, ([lang| fun ⸨xl: Loc⸩ ⸨yl : Loc⸩=> {Example3.cfgexp_grammar j Example3.trm1 Example3.trm2}], default_payload)⟩}) : Set (trm × payload)ˡ)) =>
      (xl ~~> (xv + Int.ofNat j) ∗ yl ~~> (yv + Int.ofNat j)))
  { simp [lang_index, lang_squeeze_list']
    exists (((lang_part1 0).trm_seq (lang_part2 false)), default_payload, default_payload)
    simp }
  { simp [pay_index] ; exists (default_trm, 0, 0) ; simp }
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
    { rintro ⟨_, _, _⟩ ; subst al atrm
      exists 1, trm_funs [trm_varl "xl", trm_varl "yl"] (lang_sn1 (Int.toNat ap))
      simp ; rw [(haux _ (Int.toNat ap)).mp rfl] ; simp ; assumption
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
    · specialize h1 (Int.toNat ip) (by left ; simp [hin])
      specialize h2 (Int.toNat ip) (by left ; simp [hin])
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
  { apply Example3.forwm_spec }
  { rintro ⟨jl, ⟨jtrm, jp⟩⟩ jin
    simp [Example3.pay_index, Example3.lang_index, Example3.lang_fun_list, Example3.lang_squeeze_list] at jin
    rcases jin with ⟨_, ⟨n, jin⟩, _⟩ ; subst jl jp ; symm at jin
    dsimp only
    -- involving the oracle here
    apply LGTM.triple_conseq
    on_goal 3=> apply Example0.ifwm_spec (xv + Int.ofNat (aux jtrm |>.getD 0)) (yv + Int.ofNat (aux jtrm |>.getD 0))
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
    intro hv hh hpre a b c d ; specialize hpre _ a b c rfl d ; aesop
  }
