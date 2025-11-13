import WeirdLogic.WLogic

-- TODO collect all these stuff
lemma hhlocal_union {s1 s2 : Set α} {h : hhProp _} :
  hhlocal s1 h ∨ hhlocal s2 h → hhlocal (s1 ∪ s2) h := by
  unfold hhlocal hlocal hhimpl ; aesop

lemma hdisjoint_of_hlocal :
  Disjoint s1 s2 → hlocal s1 h1 → hlocal s2 h2 → hdisjoint h1 h2 := by
  intro hdj hl1 hl2
  whnf ; intro a ; by_cases hin : a ∈ s1
  · rw [hl2] ; symm ; apply Finmap.disjoint_empty
    rw [Set.disjoint_left] at hdj ; apply hdj ; assumption
  · rw [hl1] ; apply Finmap.disjoint_empty
    assumption

set_option maxHeartbeats 3200000 in
lemma weird_grmdisj_lemma_standard (s' s : Set α) (sht_prog sht_lang : LGTM.SHT) :
  sht_prog.s = ⟪0, s'⟫ ->
  sht_lang.s = ⟪ 1, s⟫ ->
  Disjoint sht_prog.s sht_lang.s ->
  s1 ∩ s2 = ∅ -> s1 ∪ s2 = s ->
  hhlocal (⟪ 0, s'⟫) H₁ ->
  hhlocal (⟪ 1, s1⟫) H₂ ->
  hhlocal (⟪ 1, s2⟫) H₃ ->
  H₁ ∗ H₂ ==> LGTM.wp [⟨⟪ 0, s'⟫, sht_prog.ht ⟩, ⟨⟪ 1, s1⟫, sht_lang.ht ⟩ ]
   (fun _ h => (∀ ll ∈ s1, ∃ pp, pp ∈ s' ∧ h ⟨1, ll ⟩= h ⟨0, pp⟩)
    /- ∧ (hlocal (⟪1,s1⟫ ∪ ⟪0, s'⟫) h) -/
    ) ->
  H₁ ∗ H₃ ==> LGTM.wp [⟨⟪ 0, s'⟫, sht_prog.ht ⟩, ⟨⟪ 1, s2⟫, sht_lang.ht ⟩ ]
   (fun _ h => (∀ ll ∈ s2, ∃ pp,  pp ∈ s' ∧ h ⟨1, ll ⟩= h ⟨0, pp⟩)
    /- ∧ (hlocal (⟪1,s2⟫ ∪ ⟪0, s'⟫) h) -/
    ) ->
  H₁ ∗ H₂ ∗ H₃ ==> LGTM.wp [sht_prog, sht_lang]  (fun _ h => ∀ ll ∈ s, ∃ pp, pp ∈ s' ∧ h ⟨1, ll ⟩= h ⟨0, pp⟩) := by
  move=> prog lang subs sp1 sp2 hl1 hl2 hl3 part1 part2
  rw [← Set.disjoint_iff_inter_eq_empty, Set.disjoint_right] at sp1

  have simpledj : Disjoint ⟪0, s'⟫ ⟪1, s2⟫ := by
    rw [Set.disjoint_iff_forall_ne] ; simp ; rintro ⟨al, aval⟩ _ _ ⟨bl, bval⟩ _ _ ; simp at * ; aesop
  let f : αˡ → αˡ := (open Classical in (fun a =>
    -- if a ∈ ⟪0, s'⟫ then ⟨2, a.val⟩ else a))
    -- ↑ not "disjoint" enough
    if a.lab = 0 then ⟨2, a.val⟩ else (if a.lab = 2 then ⟨0, a.val⟩ else a)))
  have f_is_f_inv : ∀ a, f (f a) = a := by
    rintro ⟨al, aval⟩ ; open Classical in simp [f]
    split ; subst_eqs ; simp
    split ; subst_eqs ; simp ; simp
  let ht₁ := (open Classical in (fun a =>
    if a ∈ ⟪2, s'⟫ then sht_prog.ht ⟨0, a.val⟩ else sht_prog.ht a))
  rw [LGTM.wp_sht_eq (shts' :=
    [LGTM.SHT.mk ⟪0, s'⟫ (ht₁ ∘ f), LGTM.SHT.mk ⟪1, s2⟫ (sht_lang.ht ∘ f)])] at part2
  on_goal 2=>
    simp ; constructor
    · rintro ⟨al, aval⟩ ; simp [f, ht₁] ; intro h1 h2 ; subst_eqs ; open Classical in simp [h2]
    · rintro ⟨al, aval⟩ ; simp [f] ; intro h1 h2 ; subst_eqs ; open Classical in simp [h2]
  have tmp : ∀ a ∈ ⟪0, s'⟫, ∀ a' ∈ ⟪1, s2⟫, f a ≠ f a' := by
    simp ; rintro ⟨al, aval⟩ a ain ⟨a'l, a'val⟩ a' a'in ; open Classical in simp [f, ain] at * ; subst_eqs ; simp
  apply hsubst_wp
    (s := ⟪0, s'⟫ ∪ ⟪1, s2⟫)
    (Q' := fun x h ↦ ∀ ll ∈ s2, ∃ pp ∈ s', h ⟨1, ll⟩ = h ⟨0, pp⟩) -- TODO ?
    at part2 <;> (try first | rfl | assumption) ; rotate_left
  { open Classical in simp [Set.instMembership, Set.Mem, f] ; rintro a ain ⟨a'l, a'val⟩ aa ; clear *- aa ain ; simp [ain] ; split <;> aesop }
  { apply hhlocal_hhstar ; constructor <;> apply hhlocal_union <;> aesop }
  { aesop }
  { aesop }
  rw [← hsubst_hhstar (s := ⟪0, s'⟫ ∪ ⟪1, s2⟫)] at part2 <;> (try first | rfl | assumption)

  have tmp1 : (hsubst f (⟪0, s'⟫ ∪ ⟪1, s2⟫) fun h ↦ ∀ ll ∈ s2, ∃ pp ∈ s', h ⟨1, ll⟩ = h ⟨0, pp⟩) ==>
    (fun h ↦ ∀ ll ∈ s2, ∃ pp ∈ s', h ⟨1, ll⟩ = h ⟨2, pp⟩) := by
    intro h
    · rintro ⟨h', h'eq, hh1, hh2⟩
      apply congrFun at h'eq
      conv at h'eq => enter [a, 2] ; rw [← f_is_f_inv a]
      suffices hh : ∀ ll ∈ s2, ∃ pp, ∃ hk : pp ∈ s', h ⟨1, ll⟩ = h ⟨2, pp⟩ by clear *- hh ; aesop
      conv =>
        enter [ll, _, 1, pp, 1, hk]
        simp [h'eq]
        conv => lhs ; rw [fsubst_σ _ _ _ ‹_› (by simp [f] ; assumption)]
        conv => rhs ; rw [fsubst_σ _ _ _ ‹_› (by simp [f] ; assumption)]
      clear *- hh1 ; aesop
  apply LGTM.triple_conseq (hhimpl_refl _) (fun hv => tmp1) at part2
  clear tmp1

  have vsubst_l : validSubst f (⟪0, s'⟫ ∪ ⟪1, s2⟫) ⟪0, s'⟫ := by
    apply validSubst_union <;> (try assumption)
  have ssubst_l : (ssubst f (⟪0, s'⟫ ∪ ⟪1, s2⟫) ⟪0, s'⟫) = ⟪2, s'⟫ := by
    ext a ; rcases a with ⟨al, aval⟩
    trans ; apply fsubst_inE ; assumption
    rw [Set.union_inter_cancel_left] ; simp [f]
    clear *-
    constructor ; aesop ; rintro ⟨heq, ain⟩ ; subst_eqs ; exists ⟨0, aval⟩
  rw [ssubst_l] at part2

  have vsubst_r : validSubst f (⟪0, s'⟫ ∪ ⟪1, s2⟫) ⟪1, s2⟫ := by
    rw [Set.union_comm]
    apply validSubst_union ; rw [disjoint_comm] ; assumption ; clear *- tmp ; aesop
  have ssubst_r : (ssubst f (⟪0, s'⟫ ∪ ⟪1, s2⟫) ⟪1, s2⟫) = ⟪1, s2⟫ := by
    ext a ; rcases a with ⟨al, aval⟩
    trans ; apply fsubst_inE ; assumption
    rw [Set.union_inter_cancel_right] ; simp [f]
    clear *-
    constructor ; aesop ; rintro ⟨heq, ain⟩ ; subst_eqs ; exists ⟨1, aval⟩
  rw [ssubst_r] at part2

  have hsubst_aux : ∀ (h' : hheap αˡ), validSubst f (⟪0, s'⟫ ∪ ⟪1, s2⟫) h' → hlocal ⟪1, s2⟫ h' → fsubst f (⟪0, s'⟫ ∪ ⟪1, s2⟫) h' = h' := by
    intro h' hv hl ; funext a
    by_cases ha : a ∈ ⟪1, s2⟫
    · conv => lhs ; rw [← f_is_f_inv a]
      rcases a with ⟨al, aval⟩ ; simp at ha ; rcases ha with ⟨h1, h2⟩ ; subst_eqs
      rw [fsubst_σ _ _ _ ‹_› (by simp [f] ; assumption)]
      rfl
    · rw [fsubst_local_out] <;> try assumption
      · symm ; apply hl ; assumption
      · rw [ssubst_r] ; assumption

  have tmp1 : (hsubst f (⟪0, s'⟫ ∪ ⟪1, s2⟫) H₃) = H₃ := by
    ext h ; constructor
    · rintro ⟨h', h'eq, hh1, hh2⟩
      specialize hl3 _ hh1
      rw [hsubst_aux] at h'eq <;> try assumption
      subst_eqs ; assumption
    · intro hh ; specialize hl3 _ hh
      exists h ; apply (fun (p : _ → _) r => And.intro (p r) <| And.intro ‹_› r)
      · intro hv ; symm ; apply hsubst_aux <;> try assumption
      · apply validSubst_local (s' := ⟪1, s2⟫) <;> (try assumption)
        · whnf ; simp [f] ; clear *-; aesop
        · simp
        · simp [f] ; clear *-; aesop
  rw [tmp1] at part2 ; clear tmp1

  rintro h_ ⟨h1, h__, hh1, ⟨h2, h3, hh2, hh3, heq', hdj23⟩, heq, hdj1⟩
  have hl1' := hl1 _ hh1
  have hl2' := hl2 _ hh2
  have hl3' := hl3 _ hh3
  subst h_ h__
  have vsubst_h1 : validSubst f (⟪0, s'⟫ ∪ ⟪1, s2⟫) h1 := by
    apply validSubst_local (s' := ⟪0, s'⟫) <;> (try assumption)
    · whnf ; rintro ⟨al, aval⟩ _ ⟨bl, bval⟩ ; simp [f] ; clear *- ; aesop
    · simp
    · simp [f] ; clear *-; aesop
  rw [hdisjoint_hunion_right] at hdj1 ; rcases hdj1 with ⟨hdj12, hdj13⟩
  specialize part1 (h1 ∪ h2) ⟨_, _, hh1, hh2, rfl, hdj12⟩
  have a_fa_in : ∀ a ∉ ⟪2, s'⟫, f a ∉ ⟪0, s'⟫ := by
    intro a ha ; simp [f] ; clear *- ha ; aesop
  have fsubst_h1_eq : (fsubst f (⟪0, s'⟫ ∪ ⟪1, s2⟫) h1) = h1 ∘ f := by
    funext a
    by_cases ha : a ∈ ⟪2, s'⟫
    · conv => lhs ; rw [← f_is_f_inv a]
      rcases a with ⟨al, aval⟩ ; simp at ha ; rcases ha with ⟨h1, h2⟩ ; subst_eqs
      rw [fsubst_σ _ _ _ ‹_› (by simp [f] ; assumption)]
      rfl
    · rw [fsubst_local_out] <;> try assumption
      · symm ; apply hl1' ; apply a_fa_in ; assumption
      · rw [ssubst_l] ; assumption
  have hl1'' : hlocal ⟪2, s'⟫ (fsubst f (⟪0, s'⟫ ∪ ⟪1, s2⟫) h1) := by
    rw [fsubst_h1_eq] ; whnf ; intro a ha ; apply hl1' ; apply a_fa_in ; assumption
  specialize part2 ((fsubst f (⟪0, s'⟫ ∪ ⟪1, s2⟫) h1) ∪ h3) ⟨_, _, ?_, hh3, rfl, ?_⟩
  { exists h1 }
  { apply hdisjoint_of_hlocal (s1 := ⟪2, s'⟫) (s2 := ⟪1, s2⟫) <;> try assumption
    rw [Set.disjoint_iff_forall_ne] ; simp ; rintro ⟨al, aval⟩ _ _ ⟨bl, bval⟩ _ _ ; simp at * ; aesop }
  unfold LGTM.wp hwp at part1
  apply heval_imp_hevalExact at part1
  rcases part1 with ⟨hv1, h1p, hnr1, hbd1⟩
  simp [LGTM.SHTs.set] at hnr1 hbd1
  unfold LGTM.wp hwp at part2
  apply heval_imp_hevalExact at part2
  rcases part2 with ⟨hv2, h2p, hnr2, hbd2⟩
  simp [LGTM.SHTs.set] at hnr2 hbd2

  let hQQ := (open Classical in (fun a v h =>
    if a ∈ ⟪0, s'⟫ ∪ ⟪1, s⟫
    then
      if a ∈ ⟪0, s'⟫ ∪ ⟪1, s1⟫
      then v = hv1 a ∧ h = h1p a
      else v = hv2 a ∧ h = h2p a
    else v = val.val_unit ∧ h = ∅))
  exists hQQ ; constructor
  { simp [LGTM.SHTs.set, prog, lang]
    whnf ; simp ; rintro ⟨al, aval⟩ ; open Classical in simp
    intro hor ; rcases hor with ⟨_, ain⟩ | ⟨_, ain⟩ <;> subst_eqs <;> open Classical in simp [ain]
    · rw [hl2', hl3'] <;> (try solve | simp)
      open Classical in simp [hQQ, ain]
      specialize hnr1 ⟨0, aval⟩ (by simp ; assumption)
      open Classical in simp [ain] at hnr1 ; rw [hl2'] at hnr1 <;> (try solve | simp)
      simp at hnr1 ; apply exact_imp_eval ; assumption
    · simp at ain
      rw [hl1'] <;> (try solve | simp)
      open Classical in simp [hQQ, ain]
      rcases ain with ain | ain
      · rw [hl3']
        on_goal 2=> simp ; clear *- sp1 ain ; aesop
        open Classical in simp [hQQ, ain]
        specialize hnr1 ⟨1, aval⟩ (by simp ; assumption)
        open Classical in simp [ain] at hnr1 ; rw [hl1'] at hnr1 <;> (try solve | simp)
        simp at hnr1 ; apply exact_imp_eval ; assumption
      · specialize sp1 ain
        rw [hl2']
        on_goal 2=> simp ; assumption
        open Classical in simp [hQQ, sp1]
        specialize hnr2 ⟨1, aval⟩ (by simp ; assumption)
        open Classical in simp [ain] at hnr2 ; rw [hl1''] at hnr2 <;> (try solve | simp)
        simp at hnr2 ; apply exact_imp_eval ; assumption
  }
  { intro hv hh hpre
    specialize hbd1 (fun a => open Classical in if a ∈ (⟪0, s'⟫ ∪ ⟪1, s1⟫) then h1p a else ∅)
      (by
        whnf ; rintro ⟨al, aval⟩ ; open Classical in simp
        split
        next h => clear *- h ; aesop
        next h => clear *- h hl1' hl2' ; rw [hl1', hl2'] <;> simp <;> aesop)
    rcases hbd1 with ⟨_, hpre1⟩ ; open Classical in simp at hpre1
    specialize hbd2 (fun a => open Classical in if a ∈ (⟪2, s'⟫ ∪ ⟪1, s2⟫) then h2p a else ∅)
      (by
        whnf ; rintro ⟨al, aval⟩ ; open Classical in simp
        split
        next h => clear *- h ; aesop
        next h => clear *- h hl1'' hl3' ; rw [hl1'', hl3'] <;> simp <;> aesop)
    rcases hbd2 with ⟨_, hpre2⟩ ; open Classical in simp at hpre2
    open Classical in simp [LGTM.SHTs.set, prog, lang, bighstarDef, hQQ] at hpre
    simp ; exists hv ; simp
    intro ll hll ; subst s ; simp at hll ; rcases hll with hll | hll
    · specialize hpre1 _ hll
      rcases hpre1 with ⟨pp, hpp, heq⟩
      simp [hll, hpp] at heq
      have hprel := hpre ⟨1, ll⟩ ; open Classical in simp [hll] at hprel
      have hprer := hpre ⟨0, pp⟩ ; open Classical in simp [hpp] at hprer
      rcases hprel with ⟨_, hprel⟩ ; rcases hprer with ⟨_, hprer⟩
      exists pp ; rw [hprel, hprer] ; constructor <;> assumption
    · specialize hpre2 _ hll
      rcases hpre2 with ⟨pp, hpp, heq⟩
      simp [hll, hpp] at heq
      specialize sp1 hll
      have hprel := hpre ⟨1, ll⟩ ; open Classical in simp [sp1, hll] at hprel
      have hprer := hpre ⟨0, pp⟩ ; open Classical in simp [hpp] at hprer
      rcases hprel with ⟨_, hprel⟩ ; rcases hprer with ⟨_, hprer⟩
      -- need to use determinism here
      specialize hnr1 ⟨0, pp⟩ (by simp ; assumption)
      open Classical in simp [hpp] at hnr1 ; rw [hl2'] at hnr1 <;> (try solve | simp)
      simp at hnr1
      specialize hnr2 ⟨2, pp⟩ (by simp ; assumption)
      open Classical in simp [hpp, ht₁] at hnr2 ; rw [hl3'] at hnr2 <;> (try solve | simp)
      simp [fsubst_h1_eq, f] at hnr2
      have ⟨_, tmp⟩ := evalExact_det hnr1 hnr2
      exists pp ; rw [hprel, hprer] ; constructor ; assumption ; aesop
  }
