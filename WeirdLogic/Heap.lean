import Mathlib.Data.Finmap
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Int.Interval
import Mathlib.Order.Interval.Finset.Basic

import Batteries.Data.List.Perm

import Ssreflect.Lang

open Classical
open Std (Commutative Associative)

abbrev loc := Nat
abbrev var := String

-- aux lemmas
lemma List.kerase_noterased {α : Type u} {β : α → Type v} [DecidableEq α] (l : List (Sigma β))
  (a a' : α) (hneq : a ≠ a') (b : β a) : ⟨a, b⟩ ∈ l ↔ ⟨a, b⟩ ∈ List.kerase a' l := by
  induction l with
  | nil => simp
  | cons c l ih =>
    simp
    by_cases (a' = c.1)
    · rw [List.kerase_cons_eq] <;> try assumption
      aesop
    · rw [List.kerase_cons_ne] <;> try assumption
      aesop

section Option.merge

variable {α : Type u} (f : α → α → α)

lemma Option.merge_none_l (a : Option α) : Option.merge f none a = a := by cases a <;> rfl

lemma Option.merge_none_r (a : Option α) : Option.merge f a none = a := by cases a <;> rfl

lemma Option.merge_comm [h : Commutative f] (a b : Option α) :
  Option.merge f a b = Option.merge f b a := by
  cases a <;> cases b <;> simp [Option.merge] ; apply h.comm

lemma Option.merge_assoc [Associative f] (a b c : Option α) :
  Option.merge f (Option.merge f a b) c = Option.merge f a (Option.merge f b c) := by
  cases a <;> cases b <;> cases c <;> simp [Option.merge] ; ac_rfl

end Option.merge

abbrev Heap.heap (val : Type) := Finmap (λ _ : loc ↦ val)

class PartialCommMonoid (α : Type) extends AddCommSemigroup α where
  valid : α -> Prop
  valid_add : ∀ x, valid (x + y) -> valid x
  add_valid : ∀ x y, valid x -> valid y -> valid (x + y)
  -- NOTE: for now, this axiom is added so that we do not have to put it as a premise in the statements
  -- of some lemmas; in other cases, we should avoid using this axiom since it seems not common in
  -- formalizations of PCM

class PartialCommMonoidWRT (α : Type) (add' : semiOutParam (α -> α -> α)) (valid' : semiOutParam (α -> Prop)) extends PartialCommMonoid α where
  addE : (· + ·) = add'
  validE : PartialCommMonoid.valid = valid'

open PartialCommMonoid (valid)

section

variable {val : Type} [PartialCommMonoid val] -- [Inhabited val]

local notation "heap" => Heap.heap val

private def kmerge1 (l : loc) (v : val) (l₂ : List (Sigma (fun _ : loc => val))) : val :=
  match l₂.dlookup l with
  | .some v' => v + v'
  | _ => v

@[simp]
def kmerge : List (Sigma (fun _ : loc => val)) → List (Sigma (fun _ : loc => val)) → List (Sigma (fun _ : loc => val))
  | [], l₂ => l₂
  | s :: l₁, l₂ =>
    (if s.1 ∈ l₂.keys then
      ⟨s.1, kmerge1 s.1 s.2 l₂⟩ :: kmerge l₁ (l₂.kerase s.1)
    else s :: kmerge l₁ l₂)

-- #check List.kerase

-- @[simp]
-- lemma kerase_mem (l₂ : List (Sigma (fun _ : loc => val))) :
--   l₁ ∈ l₂.keys ->
--   l ∈ (List.kerase l₁ l₂).keys ↔ l ≠ l₁ ∧ l ∈ l₂.keys :=
--   by
--     elim: l₂ l₁=> //== l' v l ih  l₁
--     { scase: [l₁ = l']=> [?|->]
--       { srw List.kerase_cons_ne //== ih => ⟨|⟩// [] // -> ⟨|⟩ // ? // }
--       srw List.kerase_cons_eq // =>  }

@[simp]
lemma kmerge_empty_r (l : List (Sigma (fun _ : loc => val))) : kmerge l [] = l := by elim: l=> //

@[simp]
lemma kmerge_mem (l₁ : List (Sigma (fun _ : loc => val))) : l ∈ (kmerge l₁ l₂).keys ↔ l ∈ l₁.keys ∨ l ∈ l₂.keys :=
  by
    elim: l₁ l₂=> // [] /= l' v l₁ ih l₂
    scase: [l' ∈ l₂.keys]=> /=
    { srw /== ih => ? ⟨[|[]]|[[]|]⟩ // }
    move=> ?; scase: [l = l']=> [?|->] /==
    srw ih List.mem_keys_kerase_of_ne /== //

lemma kmerge_mem2 (l₁ l₂ : List (Sigma (fun _ : loc => val))) (nd₁ : l₁.NodupKeys) (nd₂ : l₂.NodupKeys) -- necessary
    (a : Sigma (fun _ : loc => val)) : a ∈ (kmerge l₁ l₂) ↔
      if a.1 ∈ l₁.keys
      then (if a.1 ∈ l₂.keys then Option.merge (· + ·) (l₁.dlookup a.1) (l₂.dlookup a.1) = .some a.2 else a ∈ l₁)
      else a ∈ l₂ :=
  by
    scase: a=> l v /=
    elim: l₁ l₂=> // [] /= l' v' l₁ ih hq
    simp at hq
    scase: hq=> hnotin1 nd₁ l₂ nd₂
    have h1 := List.mem_keys_of_mem (s := ⟨l, v⟩) (l := l₁)
    have h2 := List.mem_keys_of_mem (s := ⟨l, v⟩) (l := l₂)
    dsimp at h1 h2
    have h3 : ¬ ⟨l, v⟩ ∈ List.kerase l l₂ := by
      move=> /List.mem_keys_of_mem /List.not_mem_keys_kerase //
    have h4 := fun h => List.kerase_noterased l₂ l l' h v
    scase: [l' ∈ l₂.keys]=> hin? /==
    all_goals (srw ih=> { ih } <;> try solve
      | assumption
      | apply List.NodupKeys.kerase=> //)
    all_goals (scase: [l ∈ l₂.keys]=> ?)
    all_goals (scase: [l ∈ l₁.keys]=> ?)
    all_goals (scase: [l = l']=> ? //=)
    subst_eqs
    simp [Option.merge, kmerge1]
    scase: (l₂.dlookup l)=> //

lemma kmerge_dlookup (l₁ l₂ : List (Sigma (fun _ : loc => val))) (nd₁ : l₁.NodupKeys) (nd₂ : l₂.NodupKeys)
    (a : loc) : (kmerge l₁ l₂).dlookup a = Option.merge (· + ·) (l₁.dlookup a) (l₂.dlookup a) := by
    sorry
  -- rcases h : (kmerge l₁ l₂).dlookup a with ⟨⟩ | v
  -- { srw List.dlookup_eq_none kmerge_mem at h
  --   move: h=> /== h1 h2
  --   srw -List.dlookup_eq_none at h1; srw -List.dlookup_eq_none at h2; srw h1 h2 // }
  -- { apply List.of_mem_dlookup at h
  --   srw kmerge_mem2 at h=> //; simp at h
  --   rcases h1 : l₁.dlookup a with ⟨⟩ | v1
  --   { srw List.dlookup_eq_none at h1; srw h1 at h; dsimp at h
  --     srw List.mem_dlookup=> // }
  --   { srw h1 at h
  --     have h1' := h1; apply List.of_mem_dlookup at h1; apply List.mem_keys_of_mem at h1; dsimp at h1; srw h1 at h; dsimp at h
  --     rcases h2 : l₂.dlookup a with ⟨⟩ | v2
  --     { srw List.dlookup_eq_none at h2; srw h2 at h; dsimp at h
  --       apply List.mem_dlookup at h=> // }
  --     { srw h2 at h
  --       apply List.of_mem_dlookup at h2; apply List.mem_keys_of_mem at h2; dsimp at h2; srw h2 at h; simp_all } } }

-- both nd₁ and nd₂ are necessary
lemma kmerge_NodupKeys (l₁ l₂ : List (Sigma (fun _ : loc => val))) (nd₁ : l₁.NodupKeys) (nd₂ : l₂.NodupKeys) : (kmerge l₁ l₂).NodupKeys :=
  by
    elim: l₁ l₂=> // [] /= l v l₁ ih nd₁ l₂ nd₂
    split_ifs=> /== ⟨|⟩ //; apply ih=> //; apply List.NodupKeys.kerase=> //

lemma kmerge_comm_perm (l₁ l₂ : List (Sigma (fun _ : loc => val))) (nd₁ : l₁.NodupKeys) (nd₂ : l₂.NodupKeys) :
  (kmerge l₁ l₂).Perm $ (kmerge l₂ l₁) := by
  apply List.lookup_ext <;> try (apply kmerge_NodupKeys=> //)
  move=> l v
  srw !kmerge_dlookup=> //
  srw Option.merge_comm=> //

lemma kmerge_assoc_perm (l₁ l₂ l₃ : List (Sigma (fun _ : loc => val))) (nd₁ : l₁.NodupKeys) (nd₂ : l₂.NodupKeys) (nd₃ : l₃.NodupKeys) :
  (kmerge (kmerge l₁ l₂) l₃).Perm $ (kmerge l₁ (kmerge l₂ l₃)) := by
  apply List.lookup_ext <;> try (repeat'(apply kmerge_NodupKeys=> //))
  move=> l v
  (srw !kmerge_dlookup=> //) <;> try (repeat'(apply kmerge_NodupKeys=> //))
  rw [Option.merge_assoc]=> //

noncomputable def AList.merge (h₁ h₂ : AList (fun _ : loc => val)) :  AList (fun _ : loc => val) :=
  ⟨kmerge h₁.entries h₂.entries, by
    scase: h₁ h₂=> /= e₁ /[swap] [] /= *
    apply kmerge_NodupKeys=> //⟩

@[simp]
lemma AList.merge_empty_r (h : AList (fun _ : loc => val)) : AList.merge h ∅ = h := by
  scase: h=> ?? ; unfold AList.merge ; simp

theorem Perm.kmerge {l₁ l₂ l₃ l₄ : List (Sigma (fun _ : loc => val))} (nd₁ : l₁.NodupKeys) /- nd₁ is necessary -/ (nd₃ : l₃.NodupKeys)
    (p₁₂ : l₁.Perm l₂) (p₃₄ : l₃.Perm l₄) : (kmerge l₁ l₃).Perm $ kmerge l₂ l₄ := by
  have nd₂ := nd₁
  rw [List.perm_nodupKeys p₁₂] at nd₂
  have nd₄ := nd₃
  rw [List.perm_nodupKeys p₃₄] at nd₄
  rw [List.perm_ext_iff_of_nodup] <;> try (apply List.NodupKeys.nodup ; apply kmerge_NodupKeys=> //)
  move=> [] l v
  srw !kmerge_mem2 // (List.perm_dlookup _ nd₁ nd₂ p₁₂) // (List.perm_dlookup _ nd₃ nd₄ p₃₄)
  dsimp [List.keys]
  srw (List.Perm.mem_iff (List.Perm.map Sigma.fst p₁₂)) (List.Perm.mem_iff (List.Perm.map Sigma.fst p₃₄)) (List.Perm.mem_iff p₁₂) (List.Perm.mem_iff p₃₄)

noncomputable def Heap.add (h₁ h₂ : heap) : heap :=
  Finmap.liftOn₂ h₁ h₂ (fun h₁ h₂ => (h₁.merge h₂).toFinmap) (by
    move=> > ??; srw AList.toFinmap_eq
    apply Perm.kmerge <;> (try apply AList.nodupKeys)
    all_goals assumption)

infixr:55 " +ʰ " => Heap.add

@[simp]
lemma Heap.add_lookup (h₁ h₂ : heap) (l : loc) :
  (h₁ +ʰ h₂).lookup l = Option.merge (·+·) (h₁.lookup l) (h₂.lookup l) := by
  induction h₁ using Finmap.induction_on ; rename_i l₁
  induction h₂ using Finmap.induction_on ; rename_i l₂
  simp [Heap.add]
  move: l₁ l₂=> []l₁ ? []l₂ ? /==
  apply kmerge_dlookup=> //

@[simp]
lemma Heap.add_mem (h₁ h₂ : heap) : (l ∈  h₁ +ʰ h₂) = (l ∈ h₁ ∨ l ∈ h₂) := by
  induction h₁ using Finmap.induction_on ; rename_i l₁
  induction h₂ using Finmap.induction_on ; rename_i l₂
  simp [Heap.add, AList.merge, AList.mem_keys, AList.keys]

@[simp]
lemma Heap.add_empty_r (h : heap) : h +ʰ ∅ = h := by
  induction h using Finmap.induction_on ; rename_i l
  unfold Heap.add
  srw -Finmap.empty_toFinmap Finmap.liftOn₂_toFinmap=> //

@[simp]
lemma Heap.add_empty_l (h : heap) : ∅ +ʰ h = h := by
  induction h using Finmap.induction_on
  unfold Heap.add
  srw -Finmap.empty_toFinmap Finmap.liftOn₂_toFinmap=> //

lemma Heap.add_comm (h₁ h₂ : heap) : h₁ +ʰ h₂ = h₂ +ʰ h₁ := by
  induction h₁ using Finmap.induction_on ; rename_i l₁
  induction h₂ using Finmap.induction_on ; rename_i l₂
  simp [Heap.add, AList.merge, AList.toFinmap_eq]
  move: l₁ l₂=> []?? []?? /=
  apply kmerge_comm_perm=> //

lemma Heap.add_assoc (h₁ h₂ h₃ : heap) : (h₁ +ʰ h₂) +ʰ h₃ = h₁ +ʰ h₂ +ʰ h₃ := by
  induction h₁ using Finmap.induction_on ; rename_i l₁
  induction h₂ using Finmap.induction_on ; rename_i l₂
  induction h₃ using Finmap.induction_on ; rename_i l₃
  simp [Heap.add, AList.merge, AList.toFinmap_eq]
  move: l₁ l₂ l₃=> []?? []?? []?? /=
  apply kmerge_assoc_perm=> //

def validLoc (l : loc) (h : heap) : Prop := (h.lookup l).any (valid (α := val))

def validInter (h₁ h₂ : heap) : Prop :=
  ∀ l ∈ h₁, l ∈ h₂ -> ((h₁ +ʰ h₂).lookup l).any (valid (α := val))
  -- NOTE: originally it was `validLoc l h₁ ∧ validLoc l h₂`,
  -- but in some cases it is not sufficient to imply the validity of the `((h₁ +ʰ h₂).lookup l)`;
  -- another possible fix is to allow the axiom like
  -- `valid x → valid y → valid (x + y)`

lemma Heap.addE_of_disjoint (h₁ h₂ : heap) :
  h₁.Disjoint h₂ ->  h₁ +ʰ h₂ = h₁ ∪ h₂ := by
  sorry
  -- move=> dj; apply Finmap.ext_lookup=> l /==
  -- rcases h : Finmap.lookup l h₁ with ⟨⟩ | v₁
  -- { srw Finmap.lookup_eq_none at h
  --   apply Finmap.lookup_union_right at h
  --   srw h Option.merge_none_l=> // }
  -- { have hh : l ∈ h₁ := by rw [← Finmap.lookup_isSome, h]=> //
  --   apply dj at hh; srw Finmap.lookup_union_left_of_not_in=> //
  --   srw -Finmap.lookup_eq_none at hh; rw [hh, h]=> // }

infixr:55 " ⊥ʰ " => validInter

lemma validInter_comm (h₁ h₂ : heap) :
  h₁ ⊥ʰ h₂ = h₂ ⊥ʰ h₁ := by simp [validInter]; apply Iff.intro=> ???? <;> srw [1](Option.merge_comm)=> //

lemma validInter_empty_r (h : heap) : h ⊥ʰ ∅ := by simp [validInter, Finmap.not_mem_empty]

lemma validInter_empty_l (h : heap) : ∅ ⊥ʰ h := by simp [validInter, Finmap.not_mem_empty]

@[simp]
lemma disjoint_add_eq (h₁ h₂ h₃ : heap) :
  (h₁ +ʰ h₂).Disjoint h₃ = (h₁.Disjoint h₃ ∧ h₂.Disjoint h₃) := by
  move=> !⟨dj⟨|⟩|[dj₁ dj₂]⟩ l /==
  { move: (dj l)=> // }
  { move: (dj l)=> // }
  scase=> [/dj₁|/dj₂] //

lemma validInter_assoc_l (h₁ h₂ h₃ : heap) :
  h₁ ⊥ʰ h₂ -> (h₁ +ʰ h₂) ⊥ʰ h₃ -> h₁ ⊥ʰ (h₂ +ʰ h₃) := by
  simp [validInter]
  move=> h1 h2 l hin1 /[tac (specialize h1 _ hin1 ; specialize h2 _ (Or.intro_left _ hin1))] [ hin2 | hin3 ]
  { rcases h : Finmap.lookup l h₃
    { rw [Option.merge_none_r] ; aesop }
    {sorry}
    -- { srw h at h2 ; rw [← Option.merge_assoc, h2] ; apply Finmap.mem_of_lookup_eq_some at h=> // }
    }
  { rw [← Option.merge_assoc, h2]=> // }

lemma validInter_assoc_r (h₁ h₂ h₃ : heap) :
  h₂ ⊥ʰ h₃ -> h₁ ⊥ʰ (h₂ +ʰ h₃) -> (h₁ +ʰ h₂) ⊥ʰ h₃ := by
  simp [validInter]
  move=> h1' h2' l /[swap] hin3 /[tac (have h1 := (fun H => h1' _ H hin3) ; have h2 := (fun H => h2' _ H (Or.intro_right _ hin3)) ; clear h1' h2')] [ hin1 | hin2 ]
  { rw [Option.merge_assoc, h2]=> // }
  { rcases h : Finmap.lookup l h₁
    { rw [Option.merge_none_l] ; aesop }
    sorry
    -- { srw h at h2 ; rw [Option.merge_assoc, h2] ; apply Finmap.mem_of_lookup_eq_some at h=> // }
    }

lemma validInter_hop_distr_l (h₁ h₂ h₃ : heap) :
  (h₁ +ʰ h₂) ⊥ʰ h₃ -> (h₁ ⊥ʰ h₃ ∧ h₂ ⊥ʰ h₃) := by
  sorry
  -- simp [validInter]
  -- move=> h ⟨|⟩ l /[tac (specialize h l)]-- | [] h1 h2 l [] /[tac (specialize h1 l; specialize h2 l)] ⟩
  -- all_goals (move=> /[dup] hin1 /[swap] /[dup] hin2)
  -- all_goals (srw [1]Finmap.mem_iff=> []v3 hv3 ; srw Finmap.mem_iff=> []v hv)
  -- all_goals (srw hv hv3 at h ⊢)
  -- all_goals (dsimp [Option.merge]; try solve
  --   | aesop)
  -- { move: h; scase: (Finmap.lookup l h₂)=> > //==
  --   all_goals (simp [Option.merge]=> //)
  --   srw add_assoc (add_comm _ v3) -add_assoc
  --   have hq := fun y => PartialCommMonoid.valid_add (v + v3) (y := y)
  --   aesop }
  -- { move: h; scase: (Finmap.lookup l h₁)=> > //==
  --   all_goals (simp [Option.merge]=> //)
  --   srw add_assoc [1]add_comm
  --   have hq := fun y => PartialCommMonoid.valid_add (v + v3) (y := y)
  --   aesop }

lemma validInter_hop_distr_r (h₁ h₂ h₃ : heap) :
  h₁ ⊥ʰ (h₂ +ʰ h₃) -> (h₁ ⊥ʰ h₂ ∧ h₁ ⊥ʰ h₃) := by srw [3]validInter_comm [2]validInter_comm [1]validInter_comm ; apply validInter_hop_distr_l

lemma validInter_of_disjoint (h₁ h₂ : heap) :
  h₁.Disjoint h₂ ->  h₁ ⊥ʰ h₂ := by simp [validInter, Finmap.Disjoint]; aesop

end

namespace EmptyPCM

variable {val : Type} [Inhabited val]

abbrev add : val -> val -> val := fun _ _ => default
abbrev valid : val -> Prop := fun _ => False

scoped instance (priority := low) : AddCommSemigroup val where
  add := add
  add_assoc := by sdone
  add_comm := by sdone

scoped instance (priority := 1) EPCM : PartialCommMonoid val where
  valid := valid
  valid_add := by sdone
  add_valid := by sdone

scoped instance (priority := 0) EPCM' : PartialCommMonoidWRT val add valid where
  addE := by sdone
  validE := by sdone

@[simp]
lemma validE : PartialCommMonoid.valid (α := val) = fun _ => False := by sdone

@[simp]
lemma validLocE : validLoc (val := val) l h = False := by
  srw validLoc; scase: (Finmap.lookup l h)=> //==


lemma validInter_disjoint (h₁ h₂ : Heap.heap val) :
  h₁ ⊥ʰ h₂ = h₁.Disjoint h₂ := by
  srw validInter /==
  have hh : ∀ (o : Option val), Option.any (fun _ => decide False) o = false := by sorry
  sorry
  --   move=> []//
  -- simp [Finmap.Disjoint, hh]=> ⟨|⟩ <;> (try solve
  --   | aesop)

@[simp]
lemma Heap.add_union_validInter (h₁ h₂ : Heap.heap val) {h : h₁ ⊥ʰ h₂} :
  h₁ +ʰ h₂ = h₁ ∪ h₂ := by sorry
  -- srw validInter_disjoint at h; srw Heap.addE_of_disjoint=> //

end EmptyPCM

notation "⟦" z ", " n "⟧" => Finset.Ico (α := ℤ) z n

-- in mathlib, useful lemmas are only about intervals on ℕ
-- here, "replicate" minimal dependency lemmas to port those lemmas
lemma Int.Ico_succ_left : ⟦i+1, j⟧ = Finset.Ioo (α := ℤ) i j := by
  ext x
  rw [Finset.mem_Ico, Finset.mem_Ioo]
  omega

lemma Int.Ico_succ_right : ⟦i, j+1⟧ = Finset.Icc (α := ℤ) i j := by
  ext x
  rw [Finset.mem_Ico, Finset.mem_Icc]
  omega

lemma Int.Ico_insert_succ_left (h : i < j) : insert i ⟦i+1, j⟧ = ⟦i, j⟧ := by
  rw [Int.Ico_succ_left, ← Finset.Ioo_insert_left h]

lemma Int.Ico_succ_right_eq_insert_Ico (h : i ≤ j) : ⟦i, j+1⟧ = insert j ⟦i, j⟧ := by
  rw [Ico_succ_right, ← Finset.Ico_insert_right h]

lemma sum_Ico_succl {_ : AddCommMonoid M} (f : Int -> M) (i j : Int) :
  i < j ->
  ∑ i ∈ ⟦i, j⟧, f i = f i + ∑ i ∈ ⟦i+1, j⟧, f i := by
  move=> h
  have ha : i ∉ ⟦i+1, j⟧ := by simp
  rw [← Finset.sum_insert ha, Int.Ico_insert_succ_left h]

lemma sum_Ico_succlr {_ : AddCommMonoid M} (f : Int -> M) (i j : Int) :
  ∑ i ∈ ⟦i, j⟧, f (i+1) = ∑ i ∈ ⟦i+1, j+1⟧, f i := by
  rw [← Finset.map_add_right_Ico, Finset.sum_map]=> //

lemma sum_Ico_predr {_ : AddCommMonoid M} (f : Int -> M) (i j : Int) :
  i < j ->
  ∑ i ∈ ⟦i, j⟧, f i = (∑ i ∈ ⟦i, j - 1⟧, f i) + f (j -1) := by
  move=> h
  have ha : i ≤ j - 1 := by sorry /- linarith -/
  have hb := Int.Ico_succ_right_eq_insert_Ico ha
  simp at hb
  rw [hb, Finset.sum_insert Finset.right_not_mem_Ico, add_comm]
