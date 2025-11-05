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

open Unary prim val trm
open ContextFreeGrammar

namespace WeirdLogic

/- L -> S1; S2
  S1 -> trm1; S1; trm2
        | ε
  S2 -> trm3 | trm4
  L = {trm1ⁿ;trm2ⁿ;(trm3|trm4) : n ≥ 0}
  context free + seq rule
-/
def trm1 : trm := [lang| let xx := !xl in let temp0 := xx + 1 in xl := temp0]
def trm2 : trm := [lang| let yy := !yl in let temp1 := yy + 1 in yl := temp1]
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
    output := [Symbol.terminal trm1, Symbol.nonterminal "S1", Symbol.terminal trm2],
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
    rules := Finset.mk {r1, r2, r3, r4} (by unfold r1 r2 r3 r4 trm1 trm2; simp)
  }

def l1 : Language trm := cfg1.language


lang_def' prog_c1 :=
  fun ⸨xl: Loc⸩ ⸨yl: Loc⸩ ⸨pa:Val⸩ ⸨pb:Val⸩=>
    for k in [0:pa] {
      let xx := !xl in
      let temp0 := xx + 1 in
      xl := temp0
    };
    for j in [0:pa] {
      let yy := !yl in
      let temp1 := yy + 1 in
      yl := temp1
    };
    let xx := !xl in
    let yy := !yl in
    if pb > 10 then
      let temp0 := xx + yy in
      yl := temp0
    else
      let temp1 := xx - yy in
      yl := temp1


def regexp_grammar : ℕ → trm → trm
  | 0, _ => trm_val val_unit
  | 1, t => t
  | (n+1), t => trm_seq t (regexp_grammar n t)

def cfgexp_grammar : ℕ → trm → trm → trm
  | 0, _, _ => trm_val val_unit
  | n, t1, t2 => trm_seq (regexp_grammar n t1) (regexp_grammar n t2)

def lang_squeeze_list: Set trm :=
  {trm_seq (cfgexp_grammar i trm1 trm2) (trm3) | i : ℕ } ∪ {trm_seq (cfgexp_grammar i trm1 trm2) (trm4) | i : ℕ }

def lang_fun_set : Set trm :=
  {[lang| fun ⸨xl: Loc⸩ ⸨yl : Loc⸩ => {tt}] | tt ∈ lang_squeeze_list }

def pay_index : Set (trm × payload × payload) :=
  { x |
    ∃ p1 ∈ @Set.univ payload, ∃ p2 ∈ @Set.univ payload, (default_trm,(p1,p2))=x
  }

def lang_index : Set (trm × payload × payload ):=
  { (l, (default_payload,default_payload)) | l ∈ lang_fun_set}

def lang_index1 : Set (trm × payload × payload ):=
  { (l, (default_payload,default_payload)) | l ∈ {[lang| fun ⸨xl: Loc⸩ ⸨yl : Loc⸩ => {tt}] | tt ∈ {trm_seq (cfgexp_grammar i trm1 trm2) (trm3) | i : ℕ } }}

def lang_index2 : Set (trm × payload × payload ):=
  { (l, (default_payload,default_payload)) | l ∈ {[lang| fun ⸨xl: Loc⸩ ⸨yl : Loc⸩ => {tt}] | tt ∈ {trm_seq (cfgexp_grammar i trm1 trm2) (trm4) | i : ℕ } }}

lemma lang_union :
  lang_index = lang_index1 ∪ lang_index2 := by
  unfold lang_index1 lang_index2 lang_index lang_fun_set lang_squeeze_list
  aesop

lemma lang_disjoint :
  Disjoint lang_index1 lang_index2 := by
  unfold lang_index1 lang_index2
  simp_all
  apply Set.disjoint_iff_inter_eq_empty.mpr
  ext e; simp
  intro n h1 n2
  rw [← h1]
  unfold trm_funs; simp
  unfold trm_funs; simp
  unfold trm_funs; simp
  intro hh
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

lemma hhstar_flip_exp4 :
  hpy ∗ hl1y ∗ hl2y ∗ hpx ∗ hl1x ∗ hl2x =
  (hpx ∗ hpy) ∗ (hl1x ∗ hl1y) ∗ (hl2x ∗ hl2y) := by
  sorry

/-
  Option 1: with SeqU rule
  Option 2: without SeqU rule
  This is the proof for option 2
-/
set_option maxRecDepth 2000 in
set_option maxHeartbeats 6400000 in
lemma example4_spec (xv : ℤ) (yv : ℤ):
  {
    [∗ in ⟪0,pay_index⟫ ∪ ⟪1,lang_index⟫ | xl ~~> xv ∗ yl ~~> yv]
  }
  [0| p in pay_index => prog_c1(⸨xl : Loc⸩, ⸨yl : Loc⸩, ⟨p.val.2.1⟩, ⟨p.val.2.2⟩) ]
  [1| l in lang_index => l.val.fst(⸨xl: Loc⸩, ⸨yl : Loc⸩)]
  { v,
    fun h => ∀ ll ∈ lang_index, ∃ pp ∈ pay_index , h ⟨1, ll⟩ = h ⟨0, pp⟩
  }
  := by
  unfold LGTM.triple
  rw [← bighstar_hhstar_disj_dir (s₁ := ⟪0, pay_index⟫) (s₂ := ⟪1, lang_index⟫ ) ]
  rotate_left
  apply disjoint_label_set.mpr; simp; rfl
  rw [← bighstar_hhstar_disj_dir (s₁ := ⟪1, lang_index1⟫ ) (s₂ := ⟪1, lang_index2⟫ ) (s := ⟪1, lang_index⟫)]
  rotate_left
  apply disjoint_label_set.mpr; right; apply lang_disjoint;
  rw [lang_union]; unfold labSet; aesop
  -- Step 1 : GrmDisj rule
  apply weird_grmdisj_lemma_standard (s1 := lang_index1) (s2 := lang_index2) (s' := pay_index)
  rfl; rfl; apply disjoint_label_set.mpr; simp; apply Set.disjoint_iff_inter_eq_empty.mp lang_disjoint; apply eq_comm.mpr lang_union
  simp; simp; simp
  · rw [← bighstar_hhstar_disj_dir (s₁ := ⟪0, pay_index2⟫) (s₂ := ⟪0, pay_index1⟫ )]
    rotate_left
    apply disjoint_label_set.mpr; simp; apply disjoint_comm.mpr pay_disjoint; rw [labSet_union]; rw [Set.union_comm]; apply pay_union
    rw [hhstar_assoc]

    -- Step 2: Weaken rule
    apply weird_weaken_lemma' (s' := pay_index1)=>//
    { have tmp := pay_union
      simp_all only [Set.subset_union_left] }
    { simp; apply disjoint_label_set.mpr; simp }
    {
      -- Prove the termination of the useless part
      dsimp
      have tmp : pay_index2 = pay_index \ pay_index1 := by
        rw [pay_union]; simp
        exact Eq.symm (Disjoint.sdiff_eq_right pay_disjoint)
      rw [←tmp]
      dsimp [LGTM.wp, LGTM.SHTs.htrm]
      rw [hwp_ht_eq (ht₂ := (fun (p : (trm × payload × payload)ˡ) => prog_c1.trm_call [xl, yl, [lang| ⟨p.val.2.1⟩], [lang| ⟨p.val.2.2⟩]] ))] --remove union set
      on_goal 2=> simp only [Set.EqOn, fun_insert, Set.union_empty] ; intro a b ; simp only [b, reduceIte]
      unfold prog_c1
      have tmp := htriple_prod (α := (trm × payload × payload)ˡ) (s := ⟪0, pay_index2⟫)
        (ht := open Classical in (fun a => prog_c1.trm_call [xl, yl, [lang| ⟨a.val.2.1⟩], [lang| ⟨a.val.2.2⟩]]))
        (H := fun _ => xl ~~> xv ∗ yl ~~> yv)
        (Q := fun i v => fun h => ∀ a ∉ ⟪0, pay_index2⟫, h = ∅)
      specialize tmp (by
        clear tmp
        intro a ha
        unfold prog_c1
        xwp ; xseq_xlet_if_needed
        by_cases hav : a.val.2.1 ≥ 0
        {
          stop -- faster for debugging
          xfor (fun a => xl ~~> ((xv + a) : ℤ))
          · intro i hi hia
            xstep; xwp; xlet; xstep; xapp; xsimp
          · intro _; dsimp
            xwp; xseq
            xfor (fun a => yl ~~> ((yv + a) : ℤ))
            {
              intro i hi hia; xwp; xlet;
              xapp; xwp; xlet; xapp; xapp; xsimp
            }
            intro _; dsimp
            xwp; xlet;
            xapp; xwp; xlet; xapp
            xwp; xlet;
            apply triple_conseq_frame ; apply triple_gt ; xsimp;
            intro k; dsimp;
            xsimp_start -- something wrong with xsimp here
            xsimp_step
            -- apply xsimp_r_hpure;
            -- xsimp_step
            -- xsimp_step
            -- xsimp_step
            -- xsimp_step
            -- try rev_pure
            -- try hide_mvars
            -- try hsimp
            -- rotate_left
            sorry
        }
        {
          stop -- faster for debugging
          apply xfor_empty_lemma
          { simp_all [not_le, gt_iff_lt] }
          intro _; dsimp
          xwp; xseq
          apply xfor_empty_lemma
          { simp_all [not_le, gt_iff_lt] }
          intro _; dsimp
          xwp; xlet; xapp; xwp; xlet; xapp; xwp; xlet
          apply triple_conseq_frame ; apply triple_gt ; xsimp;
          intro k; dsimp;
          xsimp -- something wrong with xsimp here
        }
      )
      apply hhimpl_trans ; apply tmp
      clear tmp
      rw [Set.union_empty]
      unfold prog_c1;
      apply hwp_conseq
      unfold bighstar bighstarDef;
      intro hv hh pre a ha;
      specialize pre a
      simp [ha] at pre
      assumption
    }
    {
      -- Step 3: InfDisj rule
      dsimp
      -- need to use ymerge to merge all positive p.val.2.2
      apply ymerge_lemma
        («μ» := fun x => (x.1, (x.2.1, 10)))
        (t := pay_index1) (l := 0)
        (H' := [∗i in ⟪1, lang_index1⟫| xl ~~> xv ∗ yl ~~> yv])

      ymerge 0 with (μ := fun x => (x.1, (x.2.1, 10)))

      stop
      apply weird_infdisj_lemma (s1 := pay_index1) (s2 := lang_index1) (Hx := xl ~~> xv ∗ yl ~~> yv)
        (f := fun i => (default_trm, Int.ofNat i))
        (g := fun i => ([lang| fun ⸨xl: Loc⸩ ⸨yl : Loc⸩ => {trm_seq (cfgexp_grammar i trm1 trm2) (trm3)}],default_payload))
        (Idx := @Set.univ ℕ)
      rfl; rfl; unfold pay_index1; simp;
      sorry
    }
  · rw [← bighstar_hhstar_disj_dir (s₁ := ⟪0, pay_index1⟫) (s₂ := ⟪0, pay_index2⟫ )]
    rotate_left
    apply disjoint_label_set.mpr; simp; apply pay_disjoint; rw [labSet_union]; apply pay_union
    rw [hhstar_assoc]
    apply weird_weaken_lemma' (s' := pay_index2)=>//
    { have tmp := pay_union
      simp_all only [Set.subset_union_right] }
    { simp; apply disjoint_label_set.mpr; simp }
    {
      -- same issue as the Step 2 above
      sorry
    }
    {
      -- Step 3: InfDisj rule
      sorry
    }

/- Previously, constraints for payloads in the heap are in the post-condition
    -- ∧ arr⟨{⟨0,p⟩}⟩(pa , i in pa_len => p.2.1[i]!) h
    -- ∧ arr⟨{⟨0,p⟩}⟩(pb , i in pb_len => p.2.2[i]!) h
  And pre-condition is default
  -- arr⟨⋆⟩(pa , i in pa_len =>g i) ∗
  -- arr⟨⋆⟩(pb , i in pb_len =>q i)
-/
