import Lean

-- import Ssreflect.Lang
import Mathlib.Data.Finmap
import Mathlib.Data.List.Indexes

import Lgtm.Common.State
import Lgtm.Common.Util

import Lgtm.Unary.WP1

open trm val prim

namespace Unary

lemma xfor_empty_lemma (z n : ℤ) (x : var) (H : hProp) (Q : val → hProp):
  z > n ->
  (fun _ => H) ===> Q ->
  H ==> Unary.wp (trm_for x z n F1) Q := by
  move=> h hini
  sorry
  -- apply Int.le_induction_down
  -- move: z => z; apply Int.le_induction_down
  -- { move=> ?? ??
  --   constructor=> /==;constructor; aesop }
  -- move=> j ? ih step hfin
  -- move=> ??;
  -- constructor=> /==; srw if_pos; rotate_left; omega
  -- constructor
  -- { apply step <;> try omega
  --   sdone }
  -- move=> _ > ?; apply ih=> // *
  -- apply step <;> omega
