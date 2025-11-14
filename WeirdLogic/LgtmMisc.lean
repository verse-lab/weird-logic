import Lgtm.Hyper.ProofMode

open Unary prim val trm
open Classical

section AddLocal

-- is this anywhere?
theorem heval_hlocal_add_to_post :
  hlocal s h →
  (heval s h ht hQ ↔ heval s h ht (fun hv hh => hlocal s hh ∧ hQ hv hh)) := by
  intro hl ; constructor
  on_goal 2=> intro h ; apply heval_conseq ; exact h ; intro hv hh ; simp
  intro hpre
  rcases hpre with ⟨hQ', h2a, h2b⟩
  unfold heval
  exists hQ'
  constructor
  · assumption
  · intro hv ; specialize h2b hv
    unfold bighstarDef at *
    intro h_ hh_ ; specialize h2b h_ hh_
    rcases h2b with ⟨hv1, h2b⟩
    dsimp
    exists hv1 ; dsimp ; constructor <;> try assumption
    intro a hnotin ; specialize hh_ a ; simp [hnotin] at hh_ ; rw [hh_] ; aesop

theorem htriple_hlocal_add_to_post :
  hhlocal s H →
  (htriple s ht H Q ↔ htriple s ht H (fun hv hh => hlocal s hh ∧ Q hv hh)) := by
  intro hl ; unfold htriple
  conv => enter [2, hh, a] ; simp [← heval_hlocal_add_to_post (hl _ a)]

theorem LGTM.triple_hlocal_add_to_post :
  hhlocal shts.set H →
  (LGTM.triple shts H Q ↔ LGTM.triple shts H (fun hv hh => hlocal shts.set hh ∧ Q hv hh)) := by
  intro hl ; unfold LGTM.triple LGTM.wp ; (repeat rw [hwp_equiv]) ; apply htriple_hlocal_add_to_post ; assumption

end AddLocal

section ssubst

theorem ssubst_image' {f : α → β} {s s' : Set α} :
  validSubst f s s' → s' ⊆ s →
  ssubst f s s' = f '' s' := by
  intro h hsub ; ext a ; simp [fsubst_inE _ _ h]
  whnf at hsub ; aesop

theorem ssubst_image'' {f : α → β} {s : Set α} :
  ssubst f s s = f '' s := by apply ssubst_image' <;> simp

/-- Derived from `ssubst_image'` and `ssubst_image''`. -/
theorem ssubst_subset_change {f : α → β} {s s' : Set α} :
  validSubst f s s' → s' ⊆ s →
  ssubst f s s' = ssubst f s' s' := by
  intro h hsub ; rw [ssubst_image''] ; rw [ssubst_image'] <;> assumption

theorem ssubst_set_union_union {f : α → β} {s1 s2 : Set α} :
  ssubst f (s1 ∪ s2) (s1 ∪ s2) =
  (ssubst f s1 s1) ∪ (ssubst f s2 s2) := by ext a ; simp [fsubst_inE] ; aesop

end ssubst

section validSubst

lemma validSubst_subset {s s' : Set α} {f : α → β} {g : α → γ} :
  s' ⊆ s → validSubst f s s' → validSubst f s g → validSubst f s' g := by intros ; whnf at * ; aesop

-- is this present anywhere? no?
lemma validSubst_comp {s : Set α} {f : α → β} {h : β → γ} :
  validSubst f s (h ∘ f) := by exact fun a a_1 b a_2 ↦ congrArg h

-- need a version with premise/conclusion about `s'`?
-- is this present anywhere? no?
lemma validSubst_restricted {s s' : Set α} {f : α → β} [Inhabited γ] {h : α → γ}
  [dec : ∀ a, Decidable (a ∈ s')] :
  validSubst f s h →
  validSubst f s s' →
  s' ⊆ s →
  validSubst f s (fun a => if a ∈ s' then h a else default) := by
  intro hv1 hv2 hsub ; whnf ; simp
  intro a ain b bin heq
  have heq' := heq ; apply hv1 at heq' <;> (try assumption)
  have heq'' := heq ; apply hv2 at heq'' <;> (try assumption)
  simp [Set.instMembership, Set.Mem, heq', heq'']

lemma validSubst_comp_restricted {s : Set α} {f : α → β} {h : β → γ} [Inhabited γ]
  [dec : ∀ a, Decidable (a ∈ s)] :
  validSubst f s (fun a => if a ∈ s then h (f a) else default) := by
  apply validSubst_restricted ; apply validSubst_comp ; simp ; simp

theorem validSubst_bighstar {s : Set α} {f : α → β} {H : β → hProp}
  -- write in this way to avoid having no forward dependency
  (inst : ∀ i ∈ s, HPropExact (H (f i))) :
  [∗i in s| H (f i)] ==> validSubst f s := by
  intro h hh ; whnf at hh ⊢ ; simp at *
  intro a ain b bin heq
  have hha := hh a ; have hhb := hh b
  simp [ain] at hha ; simp [bin] at hhb
  rw [← heq] at hhb
  specialize inst a ain ; rcases inst with ⟨inst⟩
  apply inst <;> assumption

instance : HPropExact (x ~~> v) := by
  constructor ; intro he1 he2 h1 h2 ; whnf at h1 h2 ; subst_eqs ; rfl

end validSubst

section fsubst

/-- An alternative to `fsubst_out` requiring a different premise -/
lemma fsubst_out' {s : Set α} {b : β} [Inhabited γ] (g : α → γ) :
  (∀ a ∈ s, f a = b → g a = default) → fsubst f s g b = default := by
  intro h
  rw [fsubst, partialInvSet] ; simp
  split <;> try rfl
  rename_i hh ; have ⟨tmp1, tmp2⟩ := Classical.choose_spec hh
  rw [h] <;> (try rfl) <;> assumption

lemma fsubst_comp_σ_whole [Inhabited γ] (g : β → γ) :
  (∀ x, x ∉ f '' s → g x = default) →
  ∀ x, fsubst f s (g ∘ f) x = g x := by
  intro h x ; by_cases hin : x ∈ f '' s
  · apply fsubst_comp_σ ; rw [ssubst_image''] ; assumption
  · rw [fsubst_out', h _ hin]
    intro a ain heq ; subst x ; apply h ; assumption

/-- A general form of the variants of `fsubst_σ` -/
lemma fsubst_σ_gen {s s' : Set α} [Inhabited γ] {g : α → γ}
  (hvfsg : validSubst f s' g)
  (hvfss : validSubst f s s') :
  s' ⊆ s → x ∈ s' → fsubst f s g (f x) = g x := by
  intro hsub xin
  unfold fsubst partialInvSet
  simp ; have xin' := hsub xin
  have tmp : ∃ a ∈ s, f a = f x := by exists x
  simp [tmp]
  have ⟨tmp1, tmp2⟩ := Classical.choose_spec tmp
  apply hvfsg <;> try assumption
  have ha := tmp2 ; apply hvfss at tmp2 <;> try assumption
  simp [Set.instMembership, Set.Mem] ; aesop

private lemma fsubst_σ_original {s : Set α} [Inhabited γ] (g : α → γ) :
  validSubst f s g → x ∈ s → fsubst f s g (f x) = g x := by
  intros ; apply fsubst_σ_gen <;> (try assumption) <;> (try simp)

-- a simple derivation of `fsubst_σ_gen`
lemma fsubst_σ_subset {s s' : Set α} [Inhabited γ] {g : α → γ}
  (hvfsg : validSubst f s' g)
  (hvfss : validSubst f s s') :
  s' ⊆ s → x ∈ f '' s' → fsubst f s g x = fsubst f s' g x := by
  intro hsub hin ; simp at hin ; rcases hin with ⟨a, hin, heq⟩ ; subst x
  rw [fsubst_σ_gen] <;> try assumption
  rw [fsubst_σ_gen] <;> (try assumption) <;> (try simp)

lemma fsubst_comp_σ_restricted {s s' : Set α} [Inhabited γ] {g : β → γ}
  (hvfss : validSubst f s s')
  (hsub : s' ⊆ s)
  [dec : ∀ a, Decidable (a ∈ s')] :
  (∀ x, x ∉ f '' s' → g x = default) →
  ∀ b, fsubst f s (fun a => if a ∈ s' then g (f a) else default) b = g b := by
  intro h b
  by_cases hin : b ∈ ssubst f s s'
  · simp [ssubst_image' hvfss hsub] at hin
    rcases hin with ⟨a, ain, faeq⟩ ; subst b
    rw [fsubst_σ_gen _ hvfss] <;> try assumption
    simp [ain] ; apply validSubst_comp_restricted
  · -- specialize hh b ; simp [hin] at hh ; rw [hh]
    rw [ssubst_image' hvfss hsub] at hin ; apply h at hin ; rw [hin]
    by_cases hin' : b ∈ f '' s
    · simp at hin' ; rcases hin' with ⟨a, hin', heq⟩ ; subst b
      rw [fsubst_σ] <;> try assumption
      · rw [hin] ; simp
      · apply validSubst_restricted <;> try assumption
        apply validSubst_comp
    · rw [fsubst_out]
      rw [ssubst_image''] ; assumption

lemma fsubst_comp_σ_restricted_restricted {s s' : Set α} [Inhabited γ] {g : β → γ}
  (hvfss : validSubst f s s')
  (hsub : s' ⊆ s)
  [dec : ∀ a, Decidable (a ∈ s')] :
  ∀ b, fsubst f s (fun a => if a ∈ s' then g (f a) else default) b =
    (if b ∈ f '' s' then g b else default) := by
  intro b
  have tmp := fsubst_comp_σ_restricted (g := fun b => if b ∈ f '' s' then g b else default) hvfss hsub
  rw [← tmp]
  · congr! 3 ; rename_i h ; simp [Set.mem_image_of_mem _ h]
  · intro x hin ; simp [hin]

end fsubst

section hsubst

set_option maxHeartbeats 800000 in
/-- A rewritten, more general version of `hsubst_bighstar` -/
lemma hsubst_bighstar_gen (f : α → β)
  (s s' : Set α) (H : β → hProp) :
  s' ⊆ s →
  validSubst f s s' →
  hsubst f s [∗ i in s' | H (f i)] =
  [∗ i in ssubst f s s' | H i] := by
  intro hsub hvs ; funext h ; simp
  unfold bighstar bighstarDef hsubst ; dsimp
  constructor
  · intro hh ; whnf at hh ; rcases hh with ⟨h', heq, hh1, hh2⟩
    subst h
    simp [fsubst_inE _ _ hvs]
    intro a -- ; rw [fsubst_inE] <;> try assumption
    -- open Classical in simp
    -- TODO simplify?
    split
    next h=>
      rcases h with ⟨x, ⟨_, xin⟩, haeq⟩ ; subst a
      specialize hh1 x ; simp [xin] at hh1
      rw [fsubst_σ f s h' hh2 (hsub xin)] ; assumption
    next h=>
      simp at h
      apply fsubst_out' ; intro y yin haeq
      by_cases hy : y ∈ s'
      · subst a ; specialize h _ yin hy ; contradiction
      · specialize hh1 y ; simp [hy] at hh1 ; assumption
  · intro hh ; dsimp
    -- exists (h ∘ f) ; split_ands
    -- exists (fun a => if a ∈ s then (h (f a)) else ∅) ; split_ands
    let target := (fun a => if a ∈ s' then (h (f a)) else ∅)
    exists target ; split_ands
    · unfold target
      symm ; funext b ; apply fsubst_comp_σ_restricted hvs hsub
      intro x hin ; specialize hh x ; simp only [ssubst_image' hvs hsub, hin, reduceIte] at hh
      exact hh
    · simp [target] ; intro a ; split
      next h=> specialize hh (f a) ; simp only [ssubst_image' hvs hsub, Set.mem_image_of_mem _ h, reduceIte] at hh ; assumption
      next h=> intro ; contradiction
    · -- apply validSubst_local
      unfold target ; apply validSubst_restricted <;> try assumption
      apply validSubst_comp

end hsubst

section SubstRule

set_option maxHeartbeats 800000 in
/-- `hsubst_heval` without a strong premise -/
lemma hsubst_heval_gen (s : Set α) :
  -- this might be overly strong!!!
  -- (∀ᵉ (a ∈ s) (a' ∉ s), f a ≠ f a') ->
  validSubst f s hh →
  hlocal s hh →
  (∀ hv₁ hv₂, Set.EqOn hv₁ hv₂ s → Q hv₁ = Q hv₂) →
  heval s hh (ht ∘ f) Q →
  heval (ssubst f s s) (fsubst f s hh) ht (fun hv => hsubst f s (Q (hv ∘ f))) := by
  move=> vs hl Qeq /heval_strongest' ![hev himp]
  shave vsP: validSubst f s (hsP hh (ht ∘ f))
  { move; simp [hsP]=> ???? /[dup] /vs->// }
  -- ?
  exists fsubst f s (hsP hh (ht ∘ f))=> ⟨b/fsubst_inE //==![a ain <-]|⟩
  { sby srw ?fsubst_σ }
  move=> hv h hP
  specialize himp (hv ∘ f) (fun a => if a ∈ s then h (f a) else ∅) ?_
  { move=> a--; move: (hP (f a))
    simp ; split
    next h=>
      specialize hP (f a) ; simp only [ssubst_image'', Set.mem_image_of_mem _ h] at hP
      simp at hP ; rw [fsubst_σ] at hP <;> assumption
    next => rw [hl] ; assumption
  }
  scase: himp=> hv' /= QP
  exists fsubst f s hv'=> /=
  exists (fun a => if a ∈ s then h (f a) else ∅) ; split_ands
  { funext b
    by_cases hin : b ∈ ssubst f s s
    · rw [ssubst_image''] at hin ; simp at hin ; rcases hin with ⟨a, ain, faeq⟩ ; subst b
      rw [fsubst_σ] ; simp [ain]
      · whnf ; simp ; clear *- ; aesop
      · assumption
    · whnf at hP ; specialize hP b ; simp [hin] at hP ; rw [hP]
      (repeat rw [fsubst_out]) <;> try assumption
  }
  { rw [Qeq] ; assumption
    whnf ; intro x xin ; simp [fsubst_in _ _ xin, xin] }
  { whnf ; simp ; clear *- ; aesop }

/-- `hsubst_htriple` without a strong premise -/
lemma hsubst_htriple_gen (ht : htrm β) (H : hhProp α) (Q : hval α → hhProp α) (f : α → β) :
  hhlocal s H →
  (∀ hv₁ hv₂, Set.EqOn hv₁ hv₂ s → Q hv₁ = Q hv₂) →
  htriple s (ht ∘ f) H Q →
  htriple (ssubst f s s) ht (hsubst f s H) (fun hv => hsubst f s (Q (hv ∘ f))) := by
  move=> Hl Ql htr hh ![hh -> ??]; apply hsubst_heval_gen=>//

end SubstRule

section DerivedRules

-- relying on `hwpgen_seq`
theorem htriple_seq :
  htriple s ht1 H (fun _ => Q) →
  htriple s ht2 Q QQ →
  htriple s (fun a => trm_seq (ht1 a) (ht2 a)) H QQ := by intro h1 h2 ; ywp ; yapp h1

theorem LGTM.triple_seq (shts : LGTM.SHTs α) (ht_list1 ht_list2 : List (htrm α)) :
  List.Forall₂ (fun sht (ht1, ht2) => ∀ a ∈ sht.s, sht.ht a = trm_seq (ht1 a) (ht2 a))
    shts (List.zip ht_list1 ht_list2) →
  LGTM.triple (shts.zipWith (fun sht ht1 => ⟨sht.s, ht1⟩) ht_list1) H (fun _ => Q) →
  LGTM.triple (shts.zipWith (fun sht ht2 => ⟨sht.s, ht2⟩) ht_list2) Q QQ →
  LGTM.triple shts H QQ := by
  intro h h1 h2
  unfold LGTM.triple LGTM.wp
  rw [hwp_ht_eq (ht₂ := fun a =>
    trm_seq
      (LGTM.SHTs.htrm (shts.zipWith (fun sht ht1 => ⟨sht.s, ht1⟩) ht_list1) a)
      (LGTM.SHTs.htrm (shts.zipWith (fun sht ht2 => ⟨sht.s, ht2⟩) ht_list2) a))]
  on_goal 2=>
    whnf ; intro x hin ; dsimp ; clear h1 h2
    generalize he : (ht_list1.zip ht_list2) = l at h
    induction h generalizing ht_list1 ht_list2 with
    | nil => simp at hin ⊢
    | @cons a b shts' l' hr hsub ih =>
      rcases a with ⟨s, ht⟩ ; rcases b with ⟨ht1, ht2⟩
      dsimp at hr
      rw [List.zip_eq_cons_iff] at he ; rcases he with ⟨ht_list1', ht_list2', hh1, hh2, hl'⟩
      subst ht_list1 ht_list2 l' ; dsimp
      split <;> aesop
  apply List.Forall₂.length_eq at h ; simp at h
  have hs1 :
    (LGTM.SHTs.set (shts.zipWith (fun sht ht1 => ⟨sht.s, ht1⟩) ht_list1)) = shts.set := by
    have h' : shts.length ≤ ht_list1.length := by omega
    clear *- h' ; induction shts generalizing ht_list1 with
    | nil => simp
    | cons sht shts' ih =>
      rcases ht_list1 with _ | ⟨ht1, ht_list1'⟩ <;> simp at h' ; simp [ih _ h']
  have hs2 :
    (LGTM.SHTs.set (shts.zipWith (fun sht ht2 => ⟨sht.s, ht2⟩) ht_list2)) = shts.set := by
    have h' : shts.length ≤ ht_list2.length := by omega
    clear *- h' ; induction shts generalizing ht_list2 with
    | nil => simp
    | cons sht shts' ih =>
      rcases ht_list2 with _ | ⟨ht2, ht_list2'⟩ <;> simp at h' ; simp [ih _ h']
  apply htriple_seq
  · rw [← hs1] ; exact h1
  · rw [← hs2] ; exact h2

theorem LGTM.triple_sequ1 (s1 : Set α) (ht1 ht2 : htrm α) (shts2 : LGTM.SHTs α) :
  Disjoint s1 shts2.set →
  LGTM.triple [⟨s1, ht1⟩] H (fun _ => R) →
  LGTM.triple (⟨s1, ht2⟩ :: shts2) R Q →
  LGTM.triple (⟨s1, fun a => trm_seq (ht1 a) (ht2 a)⟩ :: shts2) H Q := by
  intro hdisj h1 h2
  unfold LGTM.triple
  rw [LGTM.wp_cons] <;> try assumption
  dsimp ; ywp ; yseq
  unfold LGTM.triple LGTM.wp at h1 ; simp at h1
  apply htriple_conseq ; rw [← hwp_equiv, hwp_ht_eq] ; apply h1
  on_goal 1=> whnf ; aesop
  on_goal 1=> ysimp
  ysimp ; rw [LGTM.triple, LGTM.wp_cons] at h2 ; simp at h2 ; exact h2 ; assumption

theorem LGTM.triple_sequ2 (s1 : Set α) (ht1 ht2 : htrm α) (shts2 : LGTM.SHTs α) :
  Disjoint s1 shts2.set →
  LGTM.triple (⟨s1, ht1⟩ :: shts2) H Q →
  (∀ hv, LGTM.triple [⟨s1, ht2⟩] (Q hv) (fun hv' => R (hv' ∪_s1 hv))) →
  LGTM.triple (⟨s1, fun a => trm_seq (ht1 a) (ht2 a)⟩ :: shts2) H R := by
  intro hdisj h1 h2
  zseq_if_needed ; assumption ; zapp h1
  specialize h2 x ; unfold LGTM.triple LGTM.wp at h2 ; simp at h2
  apply htriple_conseq ; rw [← hwp_equiv, hwp_ht_eq] ; apply h2
  · whnf ; aesop
  · ysimp
  · ysimp

end DerivedRules
