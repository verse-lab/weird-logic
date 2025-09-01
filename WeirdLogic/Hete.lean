import Lgtm.Hyper.ProofMode

namespace LGTM

structure HSHT (α β : Type) extends (@SHT β) where
  -- β : Type
  f : β → α   -- in general, `f` can be injective
  -- sht : @SHT β

-- NOTE: another inverse function requires `Nonempty`, which is ... reasonable,
-- so only personal choice here

def Labeled.map (f : α → β) : αˡ → βˡ
  | Labeled.mk lab a => Labeled.mk lab (f a)

noncomputable
def HSHT.mkSHT (hsht : HSHT α β) : @SHT α :=
  { s := hsht.f '' hsht.s,
    ht := fun a => match Function.partialInv hsht.f a with
      | some b => hsht.ht b
      | none => default }

def HSHT.mkSHT' (hsht : HSHT α β) (finv : α → Option β) : @SHT α :=
  { s := hsht.f '' hsht.s,
    ht := fun a => match finv a with
      | some b => hsht.ht b
      | none => default }

theorem HSHT.mkSHT_inv_known (hsht : HSHT α β) (finv : α → Option β)
  -- (h : Set.EqOn finv (Function.partialInv hsht.f) (hsht.f '' hsht.s)) :
  (h : finv = Function.partialInv hsht.f) :
  hsht.mkSHT = hsht.mkSHT' finv := by
  dsimp [HSHT.mkSHT, HSHT.mkSHT'] ; congr! ; solve_by_elim

theorem HSHT.mkSHT_sum_left (sht : @SHT α) :
  letI hsht := HSHT.mk sht (f := @Sum.inl α β)
  hsht.mkSHT = hsht.mkSHT' Sum.getLeft? := by
  apply HSHT.mkSHT_inv_known ; dsimp ; ext x a ; simp
  unfold Function.partialInv ; split_ifs with h <;> simp_all
  · rcases h with ⟨b, h⟩ ; subst x ; simp_all
  · intro hh ; subst hh ; simp at h

theorem HSHT.mkSHT_sum_right (sht : @SHT α) :
  letI hsht := HSHT.mk sht (f := @Sum.inr β α)
  hsht.mkSHT = hsht.mkSHT' Sum.getRight? := by
  apply HSHT.mkSHT_inv_known ; dsimp ; ext x a ; simp
  unfold Function.partialInv ; split_ifs with h <;> simp_all
  · rcases h with ⟨b, h⟩ ; subst x ; simp_all
  · intro hh ; subst hh ; simp at h

syntax "[" num "| " term "| " ident " in " term " => " lang "]" : sht

macro_rules
  | `([sht| [$n | $f | $i in $s => $t]]) =>
    `($(Lean.mkIdent ``HSHT.mkSHT) <|
      $(Lean.mkIdent ``HSHT.mk) ([sht| [$n | $i in $s => $t] ])
        ($(Lean.mkIdent ``Labeled.map) ($f)))   -- complicated by the label type ... well

@[app_unexpander LGTM.HSHT.mkSHT] def unexpandHSHT : Lean.PrettyPrinter.Unexpander
  | `($(_) $stx) =>
    match stx with
    | `($(_) $stx $(_)) => `($stx)
    | `({ toSHT := [sht| [$n | $i in $s => $t] ] , f := $f }) => do
      let f := match f with
        | `($mp:ident $ff) => if mp.getId.isSuffixOf ``Labeled.map then ff else f
        | _ => f
      `([sht| [$n | $f | $i in $s => $t] ])
    | _ => throw ( )
  | _ => throw ( )

-- open Unary prim val trm in
#check [sht| [1 | (@Sum.inl Nat Nat) | p in (@Set.univ Nat) => ()]]
#check [sht| [1 | Sum.inl | p in (@Set.univ Nat) => ()]]

-- macro_rules
--   | `({ $H } $sht* { $v, $Q }) => `(
--     LGTM.triple [ $[ [sht| $sht] ],* ] $H (fun $v => $Q)
--   )

-- noncomputable
-- def SHT.mk' (h : HSHT α β) : @SHT α :=
--   { s := h.f '' h.sht.s,
--     ht := fun a => match Function.partialInv h.f a with
--       | some b => h.sht.ht b
--       | none => default }
