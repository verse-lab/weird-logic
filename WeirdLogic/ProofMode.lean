import Lean
-- lemmas on heaps
import Mathlib.Data.Finmap
import Qq

import Lgtm.Common.LabType
import Lgtm.Common.Util

import Lgtm.Unary.WP1

import Lgtm.Hyper.YSimp
import Lgtm.Hyper.YChange
import Lgtm.Hyper.WP
import Lgtm.Hyper.WPUtil
import Lgtm.Hyper.Subst.Theory
import Lgtm.Hyper.Subst.YLemmas
import Lgtm.Hyper.ArraysFun
import Lgtm.Hyper.HProp
import Lgtm.Hyper.Loops.YLemmas
import Lgtm.Hyper.Merge

open Classical trm val prim
open Lean hiding Meta.subst
open Elab Term

variable {α : Type} (s : Set α)

local macro "LabType" : term => `(ℕ)

class IsGeneralisedJoin (z n) (s' : Set α) (add) (valid) [PartialCommMonoidWRT val add valid]
  (H₀ : hhProp α) (Q : Int -> hval α -> hhProp α)
  (β : outParam Type)
  (Qgen : outParam (Int -> β -> hhProp α))
  (Qind : outParam (Int -> β -> hval α -> hhProp α))
  (Qsum : outParam (hval α -> hhProp α)) where
  eqGen : ∀ (hv : Int -> hval α), ∀ j ∈ ⟦z,n⟧, ∃ v H, hhlocal s' H ∧ H₀ + ∑ i ∈ ⟦z, j⟧, Q i (hv i) = Qgen j v ∗ H
  eqInd : ∀ j hv v, Qind j v hv = Q j hv + Qgen j v
  eqSum : ∀ hv, Qsum hv = H₀ + ∑ i ∈ ⟦z,n⟧, Q i hv

namespace JoinPCM

@[simp]
abbrev add : val -> val -> val
  | .val_int i, .val_int j => if i=j then val.val_int i else val.val_int 0
  | _, _ => val.val_unit
@[simp]
abbrev valid : val -> Prop
  | .val_int _ => True
  | _ => False

scoped instance : PartialCommMonoid val where
  add := add
  add_assoc := by
    move=> [] // a [] // b [] /==;
    all_goals
      unfold HAdd.hAdd instHAdd=> /=;
      by_cases h: a=b <;> simp [h];
      all_goals
        intro c;
        by_cases h2: b=c <;> sby simp [h2];
  add_comm := by
    move=> a b; scase: a <;> scase: b=> //==
    move=> c d
    unfold HAdd.hAdd instHAdd=> /=;
    by_cases h: c=d <;> sby simp [h];
  valid := valid
  valid_add := by
    move=> a b; scase: a <;> scase: b=> //==
  add_valid := by
    move=> v v'; scase: v => /== ; scase: v' => /==
    unfold HAdd.hAdd instHAdd=> /=;
    intro a b
    by_cases h : b = a <;> simp [h]

scoped instance inst : PartialCommMonoidWRT val add valid where
  validE := by rfl
  addE := by rfl

@[simp]
lemma Heap.join_single (p : loc) (v v' : val) [PartialCommMonoid val] :
  Heap.add (Finmap.singleton p v) (Finmap.singleton p v') = (Finmap.singleton p (v + v')) := by
  apply Finmap.ext_lookup; srw Heap.add_lookup /== => l
  scase: [l = p]=> [?|->//]; srw ?Finmap.lookup_eq_none.mpr //

lemma hjoin_single_gen (v v' : val) [PartialCommMonoid val] :
  PartialCommMonoid.valid v ->
  PartialCommMonoid.valid v' ->
  (p ~~> v) + (p ~~> v') = if v=v' then p ~~> (v) else p ~~> (val.val_int 0):= by
  move=> ?? !h //
  constructor
  all_goals
    by_cases h: v=v' <;> simp [h];
  unfold HAdd.hAdd instHAdd=> /=;
  stop
  srw -Heap.add_single; exists (Finmap.singleton p v), (Finmap.singleton p v')
  sdo 3 constructor=> //
  move=> /==; apply PartialCommMonoid.add_valid=> //

lemma hadd_single (v v' : Bool) :
  (p ~~> v) + (p ~~> v') = p ~~> (v || v') := by
  stop
  apply hadd_single_gen=> //

instance GenInst (op : hval α -> Int -> Bool) (x : α -> loc) (s : Set α) :
  IsGeneralisedJoin
    z n s
    JoinPCM.add JoinPCM.valid
    (x i ~⟨i in s⟩~> 0)
    (fun i hv => x j ~⟨j in s⟩~> op hv i)
    (Int)
    (fun _ j =>  x i ~⟨i in s⟩~> j)
    (fun i j hv => x k ~⟨k in s⟩~> if i=j then val.val_int (op hv i) else val.val_int 0)
    (fun hv => x k ~⟨k in s⟩~> if (∀ i ∈ ⟦z,n-1⟧, op hv i = op hv (i+1)) then val.val_int (op hv z) else val.val_int 0 ) where
    eqGen := by
      move=> > ?
      stop
      exists (∃ i ∈ ⟦z, j-1⟧, op (hv i) i) , emp ; simp [hhlocalE]
      srw or_hhsingle; ysimp=> //
    eqInd := by stop move=> >; srw hhadd_hhsingle_gen //
    eqSum := by stop move=> >; srw or_hhsingle //

@[simp]
lemma validE : PartialCommMonoid.valid = JoinPCM.valid := by trivial

@[simp]
lemma addE : (· + ·) = JoinPCM.add := by trivial


@[app_unexpander hharrayFun]
def hharrayFunUnexpander : Lean.PrettyPrinter.Unexpander
  | `($_ $s $f $n fun $_ => $p) =>
    match f with
    | `(fun $x:ident => $f) =>
      `(arr($p ⟨$s:term⟩ , $x:ident in $n => $f))
    | _ => throw ( )
  | _ => throw ( )

end JoinPCM
