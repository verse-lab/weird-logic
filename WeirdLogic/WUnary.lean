import Lean

-- import Ssreflect.Lang
import Mathlib.Data.Finmap
import Mathlib.Data.List.Indexes

import Lgtm.Common.State
import Lgtm.Common.Util

import Lgtm.Unary.WP1

open trm val prim

namespace Unary

lemma trm_seq_neq (t t2 : trm) : t ≠ trm_seq t t2 := by
  intro h ; apply congrArg sizeOf at h ; simp at h ; omega

lemma trm_seq_neq' (t t2 : trm) : t2 ≠ trm_seq t t2 := by
  intro h ; apply congrArg sizeOf at h ; simp at h ;

lemma empty_pre (H : hProp):
  triple [lang| ()] H fun _ => H := by
  xwp; xval; simp

lemma eval_for_val (v : val) : eval s v Q ↔ Q v s := by
  constructor
  · intro h ; cases h ; assumption
  · intro h ; constructor ; assumption

lemma empty_for_loop (a : Int) :
  eval s (trm_for i a a t) Q ↔ Q val_unit s := by
  constructor
  · intro h ; cases h ; rename_i h ; simp at h ; rw [eval_for_val] at h ; assumption
  · intro h ; constructor ; simp ; rw [eval_for_val] ; assumption

lemma empty_for_loop2 (z n : ℤ):
  z ≥ n ->
  (eval s (trm_for i z n t) Q ↔ Q val_unit s ):= by
  move=> hzn
  have hn : ¬ z < n := by simp; assumption
  constructor
  · intro h ; cases h ; rename_i h ;
    simp [hn] at h ; rw [eval_for_val] at h ; assumption
  · intro h ; constructor ; simp [hn]; rw [eval_for_val] ; assumption

lemma xfor_empty_lemma (z n : ℤ) (x : var) (H : hProp) (Q : val → hProp):
  z > n ->
  (fun _ => H) ===> Q ->
  H ==> Unary.wp (trm_for x z n F1) Q := by
  move=> h hini
  unfold wp
  move=> hh hpre
  rw [empty_for_loop2]
  {
    unfold qimpl himpl at hini
    specialize hini val_unit hh
    simp_all
  }
  { exact le_of_lt h }

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
