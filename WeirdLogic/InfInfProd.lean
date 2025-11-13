import Lgtm.Hyper.ProofMode

import WeirdLogic.LgtmMisc

open Classical trm val prim

section

variable (pf : β → Set α) (s : Set β)
  (hdj : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (pf i) (pf j))

include hdj in
theorem fun_union_exists :
  ∃ aux : α → Option β,
    (∀ a i, i ∈ s ∧ a ∈ pf i ↔ aux a = some i) := by
  have tmp := skolem (b := fun _ => Option β) (p := fun a c => ∀ (i : β), i ∈ s ∧ a ∈ pf i ↔ c = some i)
  rw [← tmp]
  intro a
  by_cases h : ∃ i ∈ s, a ∈ pf i
  · rcases h with ⟨i, iin, ain⟩
    exists some i
    intro v ; constructor
    · rintro ⟨vin, ain'⟩
      congr ; specialize hdj i iin v vin ; rw [Set.disjoint_iff_forall_ne] at hdj
      rw [← @not_not (i = v)] ; intro c ; specialize hdj c ; apply hdj ain ain' ; rfl
    · intro h ; simp at h ; subst_eqs ; aesop
  · simp at h
    exists none
    clear tmp ; intro v ; aesop

variable (Q : β → hval α → hhProp α)
  -- this is required in some form (maybe not this strong), since
  -- `Q v` might assert on some initial heap that can be modified by others;
  -- if not asserted here, then the form of the post-condition in the goal
  -- must change

  -- NOTE: in this case, `Q` cannot be something like `bighstar`,
  -- since `bighstar` asserts on the whole hyper-heap, including parts
  -- outside `pf v`

  -- `hhlocal (pf v) (Q v hv)` DOES NOT imply this
  (hQlocal2 : ∀ v ∈ s, ∀ hv hh1 hh2, (∀ a, a ∈ pf v → hh1 a = hh2 a) → Q v hv hh1 = Q v hv hh2)
  -- same reason as above
  (hQlocal1 : ∀ v ∈ s, ∀ hv1 hv2, (∀ a, a ∈ pf v → hv1 a = hv2 a) → Q v hv1 = Q v hv2)

include hQlocal2 hQlocal1 in
theorem heval_heval_prod
  (hh : β → hheap α) (ht : β → htrm α)
  -- `aux` is to be eliminated; it is just auxiliary here
  (aux : α → Option β)
  :
  -- this implies that `pf`s are disjoint
  (∀ a i, i ∈ s ∧ a ∈ pf i ↔ aux a = some i) →
  -- writing in this form to facilitate skolemization
  (∀ (a : { a : β // a ∈ s }), heval (pf a) (hh a) (ht a) (Q a)) →
  heval (⋃ i ∈ s, pf i)
    (fun a => (aux a).elim ∅ (hh · a))
    (fun a => (aux a).elim [lang| ()] (ht · a))
    (fun hv => h∀ i, h∀ (_ : i ∈ s), Q i hv) := by
  intro haux h1
  unfold heval at h1 ; rw [skolem] at h1 ; rcases h1 with ⟨hQQ, h1⟩
  exists (fun a v => hexists fun x => hexists fun (_ : a ∈ pf x.val) => (hQQ x a v))   -- ?
  constructor
  · whnf ; simp ; intro a x xin ain
    specialize h1 ⟨_, xin⟩ ; apply And.left at h1 ; whnf at h1 ; simp at h1
    specialize h1 _ ain
    specialize haux a x ; simp [xin, ain] at haux ; rw [haux] ; simp
    apply eval_conseq ; assumption
    intro vv hh hq
    exists ⟨x, xin⟩ ; dsimp ; exists ain
  · intro hv h
    unfold bighstarDef ; simp
    intro hpre
    exists hv ; dsimp ; whnf ; intro v ; whnf ; intro vin
    specialize h1 ⟨_, vin⟩ ; apply And.right at h1
    specialize h1 hv (fun a => (if a ∈ pf v then h a else hh v a))
    unfold bighstarDef at h1 ; simp at h1
    specialize h1 (by
      intro a ; specialize hpre a ; split
      next h=>
        rw [if_pos] at hpre
        on_goal 2=> exists v
        rcases hpre with ⟨⟨v', v'in⟩, z, hpre⟩ ; dsimp at z
        have haux1 := haux a v ; simp [vin, h] at haux1
        have haux2 := haux a v' ; simp [v'in, z] at haux2
        rw [haux1] at haux2 ; simp at haux2 ; subst v'
        have eqproof : vin = v'in := by simp
        rw [eqproof] ; assumption
      next hnotin=>
        intro ; contradiction
    )
    rcases h1 with ⟨hv', h1⟩
    rw [hQlocal2 (hh2 := h)] at h1 <;> try assumption
    on_goal 2=> simp ; intros ; contradiction
    revert h1 ; apply Iff.mp ; rw [← propext_iff] ; apply congr_fun ; apply hQlocal1 <;> try assumption
    intro a h ; simp ; intros ; contradiction

include hdj hQlocal2 hQlocal1 in
theorem htriple_htriple_partition
  (hh : α → hProp) (ht : β → htrm α) (ht' : htrm α) :
  (∀ k ∈ s, htriple (pf k) (ht k) [∗ i in (pf k)| hh i] (Q k)) →
  (∀ i ∈ s, ∀ j ∈ pf i, ht' j = ht i j) →
  -- `[∗ i in (⋃ j ∈ s, pf j)| hh i]` might be restrictive,
  -- but generalizing it requires a different notation of
  -- "big separating conjunction" over disjoint unions, so leave it for now
  htriple (⋃ i ∈ s, pf i) ht' [∗ i in (⋃ j ∈ s, pf j)| hh i]
    (fun hv => h∀ i, h∀ (_ : i ∈ s), Q i hv) := by
  intro h1 hht
  apply fun_union_exists at hdj
  rcases hdj with ⟨aux, hdj_aux⟩
  intro h hpre ; unfold bighstar bighstarDef at hpre ; simp at hpre
  have tmp := heval_heval_prod pf s Q hQlocal2 hQlocal1 (fun _ => h) ht aux hdj_aux ; simp at tmp
  have eq1 : (fun a ↦ (aux a).elim ∅ fun x ↦ h a) = h := by
    funext a
    rcases ho : aux a with _ | x
    · simp ; specialize hpre a ; split at hpre
      next hh=> rcases hh with ⟨i, hh⟩ ; rw [hdj_aux] at hh ; rw [hh] at ho ; contradiction
      next => rw [hpre]
    · rfl
  rw [eq1] at tmp ; clear eq1
  specialize tmp (by
    intro k kin ; specialize h1 _ kin (fun a => if a ∈ pf k then h a else ∅)
    unfold bighstar bighstarDef at h1 ; simp at h1
    specialize h1 (by
      intro a ; split
      next hh=>
        specialize hpre a ; split at hpre
        next=> assumption
        next hhh=> simp at hhh ; clear *- kin hh hhh ; aesop
      next=> intros ; contradiction
    )
    -- well, why need to prove this?
    whnf at h1 ⊢ ; rcases h1 with ⟨hQ', hnr, hbd⟩
    exists hQ' ; constructor
    · whnf at hnr ⊢ ; intro a ain ; specialize hnr _ ain ; simp [ain] at hnr ; assumption
    · intro hv hha hpre ; unfold bighstarDef at hpre ; simp at hpre
      specialize hbd hv (fun a => if a ∈ pf k then hha a else ∅) (by
        simp ; intro a ; split
        next hh=> specialize hpre a ; simp [hh] at hpre ; assumption
        next=> rfl
      )
      rcases hbd with ⟨hv', hbd⟩ ; exists hv'
      dsimp ; rw [hQlocal2] <;> (try assumption) ; intro a ain ; simp [ain]
  )
  rw [heval_ht_eq] ; assumption
  whnf ; simp ; intro a b bin ain
  specialize hdj_aux a b ; simp [ain, bin] at hdj_aux ; rw [hdj_aux] ; simp ; apply hht <;> assumption

omit Q in
include hdj in
/-- `htriple_htriple_partition` but specialized for `bighstar` -/
theorem htriple_htriple_bighstar_partition
  (Q : α → val → hProp)
  (hh : α → hProp) (ht : β → htrm α) (ht' : htrm α) :
  (∀ k ∈ s, htriple (pf k) (ht k) [∗ i in (pf k)| hh i]
    (fun hv => [∗ i in (pf k)| Q i (hv i) ])) →
  (∀ i ∈ s, ∀ j ∈ pf i, ht' j = ht i j) →
  htriple (⋃ i ∈ s, pf i) ht' [∗ i in (⋃ j ∈ s, pf j)| hh i]
    (fun hv => [∗ i in (⋃ j ∈ s, pf j)| Q i (hv i)]) := by
  intro h1 hht
  let Qd : β → hval α → hhProp α := fun k hv hh => ∀ i ∈ pf k, Q i (hv i) (hh i)
  have tmp : ∀ k ∈ s, htriple (pf k) (ht k) [∗i in pf k| hh i] (Qd k) := by
    intro k kin ; specialize h1 k kin
    apply htriple_conseq ; assumption ; apply hhimpl_refl
    intro hv hh hpre ; whnf at hpre ; simp at hpre ; simp [Qd]
    intro a ain ; specialize hpre a ; simp [ain] at hpre ; assumption
  clear h1
  apply htriple_htriple_partition (ht := ht) (ht' := ht') at tmp ; rotate_left
  { assumption }
  { intros ; simp [Qd] ; aesop }
  { intros ; simp [Qd] ; aesop }
  specialize tmp ‹_› ; rw [htriple_hlocal_add_to_post] at tmp
  on_goal 2=> simp
  apply htriple_conseq ; assumption ; apply hhimpl_refl
  rintro hv hh ⟨hl, hpre⟩ ; simp [hhforall, Qd] at hpre ; whnf
  intro a ; split
  next h=> simp at h ; rcases h with ⟨k, kin, hq⟩ ; apply hpre <;> assumption
  next => apply hl ; assumption

-- is this anywhere?
theorem triple_single_htriple (H : hProp) (Q : val → hProp) (t : trm) :
  triple t H Q ↔
  htriple {a} (fun _ => t) [∗ in {a} | H] (fun hv => [∗ in {a} | Q (hv a)]) := by
  constructor
  · intro h hh hpre ; whnf at hpre ; simp at hpre
    have hpre' := hpre a
    simp at hpre' ; specialize h _ hpre'
    whnf
    exists (fun _ => Q) ; constructor
    · whnf ; simp ; assumption
    · intro hv h' hpre' ; whnf at hpre' ; simp at hpre'
      simp ; exists hv ; simp ; whnf ; simp
      intro a' ; specialize hpre' a' ; split
      · subst a' ; simp at hpre' ; assumption
      · rename_i hi ; specialize hpre a' ; simp [hi] at hpre' hpre ; rw [hpre', hpre]
  · intro h hh hpre
    specialize h (fun a' => if a = a' then hh else ∅)
      (by
        whnf ; simp ; intro a' ; split
        · subst a' ; simp ; assumption
        · intro ; subst_eqs ; contradiction)
    rcases h with ⟨hQ', hnr, hbd⟩
    whnf at hnr ; unfold bighstarDef at hbd ; simp at hnr hbd
    apply eval_conseq ; assumption
    intro v hh hhh
    specialize hbd (fun _ => v) (fun a' => if a = a' then hh else ∅)
      (by
        simp ; intro a' ; split
        · subst a' ; simp ; assumption
        · rename_i hi ; aesop)
    rcases hbd with ⟨hv, hq⟩ ; whnf at hq ; simp at hq
    specialize hq a ; simp at hq ; assumption

section Replay

omit pf s Q in
private theorem htriple_prod_again {s : Set α} (H : α -> hProp) (Q : α -> val -> hProp) :
  (∀ a ∈ s, triple (ht a) (H a) (Q a)) ->
  htriple s ht [∗ i in s| H i] (fun hv => [∗ i in s| Q i (hv i)]) := by
  intro h
  apply htriple_conseq
  rw [← htriple_hlocal_add_to_post]
  rw [← Set.biUnion_of_singleton s]
  apply htriple_htriple_partition (hh := H) (Q := fun k hv hhe => Q k (hv k) (hhe k))
  · simp
  · simp ; introv ; intro vin ; introv ; intro heq ; rw [heq]
  · simp ; introv ; intro vin ; introv ; intro heq ; rw [heq]
  · intro k kin ; specialize h k kin ; rw [triple_single_htriple (a := k)] at h
    have tmp : [∗x in {k}| H k] = [∗i in {k}| H i] := by
      funext h ; unfold bighstar bighstarDef ; simp
      constructor <;> intro h1 a <;> specialize h1 a <;> aesop
    rw [tmp] at h ; clear tmp
    rw [← hwp_equiv] at h ⊢
    rw [hwp_ht_eq (ht₂ := ht)] at h
    apply hhimpl_trans ; apply h ; apply hwp_conseq ; intro hv hhh hpre ; whnf at hpre ; simp at hpre ; specialize hpre k ; simp at hpre ; assumption
    whnf ; simp
  · simp
  · simp
  · rw [Set.biUnion_of_singleton] ; apply hhimpl_refl
  · rintro hv hhh ⟨hl, hpre⟩ ; whnf at hpre ⊢ ; unfold hhforall at hpre ; simp at *
    intro a ; split ; aesop ; rw [hl] ; assumption

end Replay

abbrev Set.dprod (s : Set α) (pf : α → Set β) : Set (α × β) :=
  ⋃ i ∈ s, ({i} : Set α) ×ˢ (pf i)

include hQlocal2 hQlocal1 in
theorem htriple_htriple_prod
  (hh : β → α → hProp) (ht : β → htrm α) :
  (∀ k ∈ s, htriple (pf k) (ht k) [∗ i in (pf k)| hh k i] (Q k)) →
  htriple (Set.dprod s pf) (Function.uncurry ht)
    [∗ ij in (Set.dprod s pf)| hh ij.1 ij.2]
    (fun hv hh =>
      ∀ i ∈ s, Q i (Function.curry hv i) (Function.curry hh i)) := by
  intro hprod
  -- do the injective substitution first
  have hprod' : ∀ k ∈ s, htriple (({k} : Set β) ×ˢ (pf k)) (Function.uncurry ht)
    [∗ ij in (({k} : Set β) ×ˢ (pf k))| hh ij.1 ij.2]
    (fun hv hh => Q k (Function.curry hv k) (Function.curry hh k)) := by
    intro k kin ; specialize hprod k kin
    rw [← hwp_equiv, hwp_ht_eq (ht₂ := (ht k) ∘ Prod.snd)]
    on_goal 2=> whnf ; simp ; intros ; subst_eqs ; rfl
    -- CHECK the localness requirement of `htriple_hsubst`
    rw [hwp_equiv, htriple_hlocal_add_to_post]
    on_goal 2=> simp
    apply htriple_hsubst
    · whnf ; simp ; intros ; subst_eqs ; simp
    · simp
    · intro hv ; whnf ; simp +unfoldPartialApp [Function.curry] ; intros ; assumption
      -- apply hQlocal2' at hq <;> try assumption
      -- whnf at hq ⊢ ; simp at hq ⊢ ; intros
    · rw [ssubst_image'', Set.snd_image_prod]
      on_goal 2=> simp
      rw [htriple_hlocal_add_to_post] at hprod
      apply htriple_conseq ; assumption
      · intro h hpre ; whnf at hpre ⊢ ; rcases hpre with ⟨h', heq, hpre1, hpre2⟩
        whnf at hpre1 ; simp at hpre1
        subst h ; intro b
        simp ; split
        next hin=>
          apply fsubst_σ (x := (k, b)) at hpre2 ; simp at hpre2
          specialize hpre1 k b ; simp [hin] at hpre1
          simp [hin] at hpre2 ; rw [hpre2] ; assumption
        next =>
          rw [fsubst_out] ; rfl ; rw [ssubst_image''] ; simp ; assumption
      · rintro hv h ⟨hl, hpre⟩
        whnf-- ; exists (fun ij => if ij.fst = k then h ij.snd else ∅)
        -- exists (h ∘ Prod.snd) ; split_ands
        exists (fun ij => if ij.fst = k then h ij.snd else ∅) ; split_ands
        · -- why this thing keeps appearing?
          funext a ; symm
          by_cases hin : a ∈ pf k
          · --rw [fsubst_comp_σ] ; assumption
            have tmp := fun f hh => fsubst_σ (@Prod.snd β α) (({k} ×ˢ pf k)) (γ := heap) (x := (k, a)) f hh (by simp ; exact hin)
            dsimp at tmp ; rw [tmp] ; simp
            whnf ; simp ; aesop
          · rw [hl] <;> try assumption
            apply fsubst_out ; simp [ssubst_image''] ; assumption
        · whnf at hl ⊢ ; simp ; aesop
        · simp +unfoldPartialApp [Function.curry] ; apply hpre
        · whnf ; simp ; aesop
      · simp
  apply htriple_htriple_partition (α := β × α) (ht := fun _ => Function.uncurry ht)
    (ht' := Function.uncurry ht) at hprod' ; rotate_left
  · intros ; simp ; left ; assumption
  · unfold Function.curry ; simp
    intros ; rw [hQlocal2] <;> try assumption
    rename_i hh ; intros ; apply hh <;> (solve | rfl | assumption)
  · unfold Function.curry
    intros ; funext hh ; rw [hQlocal1] <;> try assumption
    rename_i hhh ; intros ; apply hhh ; simp ; assumption
  · specialize hprod' (by intros ; rfl)
    apply htriple_conseq ; assumption ; apply hhimpl_refl
    intro hv h ; simp [hhforall]

end
