import WeirdLogic.WLogic

open Unary prim val trm
open Classical

abbrev preimageRestr {α β} (b : β) (f : α → β) (s : Set α) : Set α :=
  { x | x ∈ s ∧ f x = b }

theorem Set.mem_dprod {α β} {s : Set α} {pf : α → Set β} {a : α} {b : β} :
  (a, b) ∈ Set.dprod s pf ↔ a ∈ s ∧ b ∈ pf a := by simp

section

set_option maxHeartbeats 640000 in
theorem weird_gram_seq_full_gen
  (sht_prog sht_lang : @LGTM.SHT α)
  (prog_ht_1 prog_ht_2 : α → trm)
  (lang_ht_1 lang_ht_2 : α → trm)
  (sht_prog1 sht_lang1 : @LGTM.SHT β)
  (proj1 : α → β)
  (sht_prog2 sht_lang2 : β → @LGTM.SHT γ)
  (proj2 : β → α → γ)
  (H : α → hProp)
  (H1 Q1 : β → hProp)
  -- this could be refined like below, but for now seems not necessary
  [inst : ∀ i, HPropExact (H1 i)]
  -- (inst : ∀ i ∈ sht_prog.s ∪ sht_lang.s, HPropExact (H1 (proj1 i)))
  -- [inst' : ∀ i, HPropExact (Q1 i)]
  (inst' : ∀ i ∈ sht_prog.s ∪ sht_lang.s, HPropExact (Q1 (proj1 i)))
  (hdisj : Disjoint sht_prog.s sht_lang.s)
  (hdisj1 : Disjoint sht_prog1.s sht_lang1.s)
  (hdisj2 : ∀ j ∈ sht_lang1.s, Disjoint (sht_prog2 j).s (sht_lang2 j).s)
  (part1_oracle : β → β)
  (hsurjective : sht_prog1.s = (part1_oracle '' sht_lang1.s))
  -- exploit as much as we can from the equality between heaps
  (hQ1 : [∗ i in sht_prog1.s ∪ sht_lang1.s| Q1 i ] ==>
    (fun h => ∀ ll ∈ sht_lang1.s, part1_oracle ll ∈ sht_prog1.s ∧ h ll = h (part1_oracle ll)))
  -- shape: all `trm_seq`
  -- using `∃` might also work, but with skolemization this should be the same
  (hshape_lang : ∀ a ∈ sht_lang.s, sht_lang.ht a = trm_seq (lang_ht_1 a) (lang_ht_2 a))
  (hsub_lang1_s : sht_lang1.s = ssubst proj1 sht_lang.s sht_lang.s)
  (hsub_lang1_ht : sht_lang1.ht = fsubst proj1 sht_lang.s lang_ht_1)
  (hvsub_lang1_ht : validSubst proj1 sht_lang.s lang_ht_1)
  -- thing about `(sht_lang2 j).s`
  (hsub_lang2_s : ∀ j ∈ sht_lang1.s,
    (sht_lang2 j).s = ssubst (proj2 j)
    (preimageRestr j proj1 sht_lang.s)
    -- sht_lang.s
    -- sht_lang.s
    -- ... the subset that maps to j
    (preimageRestr j proj1 sht_lang.s)
    )
  -- (hvsub_lang2_s : ∀ j ∈ sht_lang1.s,
  --   validSubst (proj2 j) sht_lang.s
  --   (preimageRestr j proj1 sht_lang.s)
  --   )
  (hsub_lang2_ht : ∀ j ∈ sht_lang1.s,
    (sht_lang2 j).ht = fsubst (proj2 j)
    (preimageRestr j proj1 sht_lang.s)
    lang_ht_2
    )
  (hvsub_lang2_ht : ∀ j ∈ sht_lang1.s,
    validSubst (proj2 j)
    (preimageRestr j proj1 sht_lang.s)
    lang_ht_2
    )

  -- similar
  (hshape_prog : ∀ a ∈ sht_prog.s, sht_prog.ht a = trm_seq (prog_ht_1 a) (prog_ht_2 a))
  (hsub_prog1_s : sht_prog1.s = ssubst proj1 sht_prog.s sht_prog.s)
  (hsub_prog1_ht : sht_prog1.ht = fsubst proj1 sht_prog.s prog_ht_1)
  (hvsub_prog1_ht : validSubst proj1 sht_prog.s prog_ht_1)
  (hsub_prog2_s :
    ∀ j ∈ sht_lang1.s,
    (sht_prog2 j).s = ssubst (proj2 j)
    (preimageRestr (part1_oracle j) proj1 sht_prog.s)
    -- sht_prog.s
    -- sht_prog.s
    -- ... the subset that maps to `(part1_oracle j)`!!
    (preimageRestr (part1_oracle j) proj1 sht_prog.s)
    )
  -- (hvsub_prog2_s :
  --   ∀ j ∈ sht_lang1.s,
  --   validSubst (proj2 j) sht_prog.s
  --   (preimageRestr (part1_oracle j) proj1 sht_prog.s)
  --   )
  (hsub_prog2_ht :
    ∀ j ∈ sht_lang1.s,
    (sht_prog2 j).ht = fsubst (proj2 j)
    (preimageRestr (part1_oracle j) proj1 sht_prog.s)
    prog_ht_2
    )
  (hvsub_prog2_ht :
    ∀ j ∈ sht_lang1.s,
    validSubst (proj2 j)
    (preimageRestr (part1_oracle j) proj1 sht_prog.s)
    prog_ht_2
    )

  -- i.e., `H1 = fsubst sht_lang.s proj1 H`
  (hH1 : ∀ a ∈ sht_prog.s ∪ sht_lang.s, H a = H1 (proj1 a))

  (hpart1 : LGTM.triple [sht_prog1, sht_lang1]
    [∗ i in sht_prog1.s ∪ sht_lang1.s| H1 i ]
    (fun _ => [∗ i in sht_prog1.s ∪ sht_lang1.s| Q1 i ]))

  -- due to the "crossing", need to do such "normalization"
  (hpart2 : ∀ j ∈ sht_lang1.s,
    LGTM.triple [sht_prog2 j, sht_lang2 j]
    -- all start with the same heap, `Q1 j`
    [∗ in (sht_prog2 j).s ∪ (sht_lang2 j).s| Q1 j ]
    (fun _ h => ∀ ll ∈ (sht_lang2 j).s, ∃ pp ∈ (sht_prog2 j).s, h ll = h pp))
  :
  LGTM.triple [sht_prog, sht_lang]
  [∗ i in sht_prog.s ∪ sht_lang.s| H i ]
  (fun _ h => ∀ ll ∈ sht_lang.s, ∃ pp ∈ sht_prog.s, h ll = h pp)
  := by

  apply LGTM.triple_seq
    (Q := [∗i in sht_prog.s ∪ sht_lang.s| Q1 (proj1 i)])
    (ht_list1 := [prog_ht_1, lang_ht_1]) (ht_list2 := [prog_ht_2, lang_ht_2])
  on_goal 1=> simp ; aesop
  { dsimp only [List.zipWith]
    -- go manual here?
    unfold LGTM.triple LGTM.wp at hpart1 ⊢
    simp only [LGTM.SHTs.set, LGTM.SHTs.htrm] at hpart1 ⊢
    rw [hwp_ht_eq (ht₂ := (sht_prog1.ht ∪_sht_prog1.s sht_lang1.ht ∪_sht_lang1.s fun x ↦ [lang| ()]) ∘ proj1)] ; rotate_left
    { whnf ; simp ; rintro x (hin | hin) <;> simp [hin]
      { -- simp [Set.disjoint_left.mp hdisj hin]
        have hin' := hin ; apply fsubst_in at hin' ; rw [← hsub_prog1_s] at hin'
        simp [hin', hsub_prog1_ht] ; rw [fsubst_σ] <;> assumption
      }
      { simp [Set.disjoint_right.mp hdisj hin]
        have hin' := hin ; apply fsubst_in at hin' ; rw [← hsub_lang1_s] at hin'
        simp [hin', hsub_lang1_ht] ; rw [fsubst_σ] <;> try assumption
        simp [Set.disjoint_right.mp hdisj1 hin']
      }
    }
    { rw [bighstar_eq (H' := fun a => H1 (proj1 a))] <;> try assumption
      apply htriple_merge
      { simp ; apply validSubst_bighstar ; intros ; infer_instance }
      { intro hv ; simp [hhlocalE] }
      { simp [hhlocalE] }
      { repeat rw [hsubst_bighstar_gen] <;> try solve | simp | assumption
        simp [ssubst_set_union_union, ← hsub_lang1_s, ← hsub_prog1_s]
        simp at hpart1 ; exact hpart1
      }
    }
  }

  have tmp : ∀ j ∈ sht_lang1.s,
    let sp := (preimageRestr (part1_oracle j) proj1 sht_prog.s)
    let sl := (preimageRestr j proj1 sht_lang.s)
    htriple (sp ∪ sl)
    ((prog_ht_2 ∪_sp
      lang_ht_2 ∪_sl fun x ↦ [lang| ()]))
    [∗ in (sp ∪ sl)| Q1 j ]
    fun _ h => ∀ ll ∈ sl, ∃ pp ∈ sp, h ll = h pp
    := by
    intro j jin sp sl-- ; unfold sp sl
    specialize hpart2 j jin
    rw [← hwp_equiv, hwp_ht_eq (ht₂ := ((sht_prog2 j).ht ∪_(sht_prog2 j).s (sht_lang2 j).ht ∪_(sht_lang2 j).s fun x ↦ [lang| ()]) ∘ (proj2 j))] ; rotate_left
    { whnf ; simp ; rintro x (hin | hin) <;> simp [hin]
      { -- simp [Set.disjoint_left.mp hdisj hin]
        dsimp only [sp] at hin
        rw [hsub_prog2_s _ jin, ssubst_image'']
        · simp only [Set.mem_image_of_mem _ hin] ; simp [hsub_prog2_ht _ jin]
          rw [fsubst_σ] ; apply hvsub_prog2_ht _ jin ; assumption
        -- · apply hvsub_prog2_s _ jin
        -- · simp
      }
      { dsimp only [sp, sl] at hin ⊢
        rw [if_neg]
        on_goal 2=> apply And.left at hin ; apply Set.disjoint_right.mp hdisj at hin ; simp [hin]
        have hin' := hin ; apply Set.mem_image_of_mem at hin' ; rw [← ssubst_image'', ← hsub_lang2_s] at hin'
        on_goal 2=> assumption
        -- on_goal 2=> apply hvsub_lang2_s _ jin
        -- on_goal 2=> simp
        simp [hin', hsub_lang2_ht _ jin] ; rw [fsubst_σ]
        on_goal 2=> apply hvsub_lang2_ht _ jin
        on_goal 2=> assumption
        simp [Set.disjoint_right.mp (hdisj2 _ jin) hin']
      }
    }

    have tmpeq : (ssubst (proj2 j) (sp ∪ sl) (sp ∪ sl)) =
      (sht_prog2 j).s ∪ (sht_lang2 j).s := by
      simp only [ssubst_set_union_union]
      rw [hsub_prog2_s _ jin, hsub_lang2_s _ jin]

    apply htriple_conseq (Q := fun _ h ↦
      hlocal (sp ∪ sl) h ∧
        validSubst (proj2 j) (sp ∪ sl) h ∧
          ∀ ll ∈ (sht_lang2 j).s,
            ∃ pp ∈ (sht_prog2 j).s,
              fsubst (proj2 j) (sp ∪ sl) h ll =
              fsubst (proj2 j) (sp ∪ sl) h pp
      )
    on_goal 2=> apply hhimpl_refl
    rotate_left
    { rintro _ h ⟨h1, h2, h3⟩
      intro ll hll
      specialize h3 (proj2 j ll) (by rw [hsub_lang2_s _ jin, ssubst_image''] ; apply Set.mem_image_of_mem ; exact hll)-- ; apply hvsub_lang2_s _ jin ; simp)
      rcases h3 with ⟨pp, hpp, heq⟩
      rw [hsub_prog2_s _ jin, fsubst_inE] at hpp <;> try simp
      -- on_goal 2=> apply hvsub_prog2_s _ jin
      rcases hpp with ⟨x, ⟨xin1, xin2⟩, heqpp⟩ ; subst pp
      rw [fsubst_σ] at heq <;> try assumption
      on_goal 2=> simp ; right ; assumption
      rw [fsubst_σ] at heq <;> try assumption
      on_goal 2=> simp ; left ; assumption
      exists x
    }

    apply htriple_merge
    { apply validSubst_bighstar (H := fun _ => Q1 j) ; intros
      rw [hsub_lang1_s, ssubst_image''] at jin ; simp at jin ; rcases jin with ⟨x, xin, heq⟩ ; subst j
      apply inst' ; simp ; right ; assumption }
    { intro hv
      whnf ; simp ; intros ; assumption }
    { simp [hhlocalE] }
    {
      repeat rw [hsubst_bighstar_gen (H := fun _ => Q1 j)] <;> try solve | simp | assumption
      rw [tmpeq]
      rw [LGTM.triple_hlocal_add_to_post] at hpart2
      on_goal 2=> simp
      unfold LGTM.triple LGTM.wp at hpart2
      simp at hpart2

      apply htriple_conseq ; apply hpart2 ; apply hhimpl_refl
      rintro _ h ⟨hl, hpre⟩ ; whnf ; simp
      exists (fun a => if a ∈ (sp ∪ sl) then h (proj2 j a) else ∅)
      split_ands
      { rw [← tmpeq, ssubst_image''] at hl
        symm ; funext b ; apply fsubst_comp_σ_restricted <;> try solve | simp | assumption
      }
      { whnf ; intro a hnotin
        dsimp only ; rw [if_neg] ; assumption
      }
      { apply validSubst_restricted ; apply validSubst_comp ; simp ; simp }
      { intro aa bb
        specialize hpre _ bb
        rcases hpre with ⟨pp, hpp, heq⟩
        exists pp ; constructor ; assumption
        rw [← tmpeq, ssubst_image''] at hl
        trans ; apply fsubst_comp_σ_restricted <;> try solve | simp | assumption
        rw [heq] ; symm ; apply fsubst_comp_σ_restricted <;> try solve | simp | assumption
      }
      { apply validSubst_comp_restricted }
    }

  apply htriple_htriple_prod at tmp
  on_goal 2=>
    intro v vin hv hh1 hh2 heqon
    conv=>
      enter [1, ll, hll, 1, pp]
      rw [← exists_prop]
      enter [1, hpp]
      rw [heqon ll (by right ; assumption), heqon pp (by left ; assumption)]
    conv=>
      enter [2, ll, hll, 1, pp]
      rw [← exists_prop]
  on_goal 2=> intros ; rfl

  unfold Function.uncurry Function.curry at tmp ; dsimp only at tmp
  unfold LGTM.triple LGTM.wp
  dsimp only [List.zipWith, LGTM.SHTs.set, LGTM.SHTs.htrm]

  rw [← hwp_equiv, hwp_ht_eq (ht₂ := ((prog_ht_2 ∪_sht_prog.s lang_ht_2 ∪_sht_lang.s fun x ↦ [lang| ()]) ∘ Prod.snd))] at tmp
  on_goal 2=>
    whnf ; rintro ⟨b, a⟩ hin ; rw [Set.mem_dprod] at hin ; rcases hin with ⟨bin, ain⟩
    dsimp only
    generalize ha : preimageRestr (part1_oracle b) proj1 sht_prog.s = sp at ain ⊢
    generalize hb : preimageRestr b proj1 sht_lang.s = sl at ain ⊢
    -- why this seems much simpler than the proof above?
    simp at ain ⊢ ; rcases ain with (ain | ain)
    · simp [ain] ; rw [if_pos] ; subst sp ; simp at ain ; cases ain ; assumption
    · subst sp sl ; simp at ain ; rcases ain with ⟨ain1, ain2⟩ ; simp [ain1, ain2]
      apply Set.disjoint_right.mp hdisj at ain1 ; simp [ain1]

  apply hsubst_htriple_gen at tmp ; rotate_left
  { exact hhlocal_bighstar fun ⦃a⦄ a ↦ a }
  { intros ; rfl }

  rw [ssubst_image''] at tmp

  have set_eq : (Prod.snd '' (sht_lang1.s.dprod fun k ↦ preimageRestr (part1_oracle k) proj1 sht_prog.s ∪ preimageRestr k proj1 sht_lang.s)) =
    (sht_prog.s ∪ sht_lang.s) := by
    ext a ; simp only [Set.mem_image, Prod.exists, Set.mem_dprod]
    constructor
    · rintro ⟨k, w, ⟨kin, ain⟩, heq⟩ ; subst w
      simp at ain ⊢ ; clear *- ain ; aesop
    · intro ain ; simp at ain ; simp only [Set.mem_setOf_eq, exists_eq_right]
      rcases ain with (ain | ain)
      · -- here, apply the fully-used assumption
        have ain' := ain ; apply fsubst_in at ain ; rw [← hsub_prog1_s] at ain
        rw [hsurjective] at ain ; simp at ain ; rcases ain with ⟨k, kin, heq⟩
        exists k ; simp ; clear *- ain kin heq ; aesop
      · exists (proj1 a) ; constructor
        · rw [hsub_lang1_s] ; apply fsubst_in ; assumption
        · right ; simp ; assumption

  rw [set_eq] at tmp
  simp ; apply htriple_conseq ; apply tmp
  { -- rw [hsubst_bighstar]
    clear tmp
    -- oh, also need `validSubst_bighstar` here ...
    intro hh hpre ; have hpre' := hpre ; apply validSubst_bighstar at hpre'
    on_goal 2=> assumption
    whnf at hpre ; dsimp at hpre
    -- uses the implication from the first half
    specialize hQ1 (fun b => if b ∈ sht_prog1.s ∪ sht_lang1.s then fsubst proj1 (sht_prog.s ∪ sht_lang.s) hh b else ∅) ?_
    { whnf ; intro a ; dsimp ; split <;> try rfl
      rename_i h ; simp at h ; rcases h with (hin | hin)
      · rw [hsub_prog1_s, ssubst_image''] at hin ; simp at hin ; rcases hin with ⟨x, xin, heq⟩ ; subst a
        have hpre' := hpre x ; simp [xin] at hpre'
        rw [fsubst_σ] <;> try assumption
        · simp ; left ; assumption
      · rw [hsub_lang1_s, ssubst_image''] at hin ; simp at hin ; rcases hin with ⟨x, xin, heq⟩ ; subst a
        have hpre' := hpre x ; simp [xin] at hpre'
        rw [fsubst_σ] <;> try assumption
        · simp ; right ; assumption
    }
    dsimp at hQ1 ; whnf
    have hQ1' : ∀ ll ∈ sht_lang.s, ∀ pp ∈ sht_prog.s,
      proj1 pp = part1_oracle (proj1 ll) → hh ll = hh pp := by
      intro ll hll pp hpp heq
      have hinll : proj1 ll ∈ sht_lang1.s := by rw [hsub_lang1_s] ; apply fsubst_in ; assumption
      have hinpp : proj1 pp ∈ sht_prog1.s := by rw [hsub_prog1_s] ; apply fsubst_in ; assumption
      rw [heq] at hinpp
      specialize hQ1 _ hinll ; apply And.right at hQ1 ; simp [hinll, hinpp] at hQ1
      rw [fsubst_σ] at hQ1 <;> try assumption
      on_goal 2=> simp ; right ; assumption
      rw [← heq, fsubst_σ] at hQ1 <;> try assumption
      simp ; left ; assumption

    -- the existence is straightforward (by reading one subgoal), but ...
    exists (fun ij =>
      if ij.1 ∈ sht_lang1.s then
        if ij.2 ∈ (preimageRestr (part1_oracle ij.1) proj1 sht_prog.s ∪ preimageRestr ij.1 proj1 sht_lang.s)
        then hh ij.2
        else ∅
      else ∅)
    apply (fun (p : _ → _) q r => And.intro (p r) (And.intro q r))
    { whnf ; dsimp only
      rintro ⟨b, a⟩ ; rw [Set.mem_dprod] ; dsimp only
      split <;> rename_i h
      { rcases h with ⟨bin, ain⟩ ; simp [bin, ain]
        simp at ain ; rcases ain with (⟨ain, heq⟩ | ⟨ain, heq⟩)
        { rw [hsub_lang1_s, ssubst_image''] at bin ; simp at bin ; rcases bin with ⟨x, xin, heq'⟩ ; subst b
          -- use `hQ1'` here; a very important step
          specialize hQ1' x xin _ ain heq ; rw [← hQ1']
          specialize hpre x ; simp [xin] at hpre ; exact hpre
        }
        { subst b
          specialize hpre a ; simp [ain] at hpre ; exact hpre }
      }
      { rw [not_and_iff_not_or_not] at h
        rcases h with (h | h) <;> simp only [h, reduceIte] <;> try rfl
        simp
      }
    }
    { whnf ; rintro ⟨b, a⟩ hin ⟨b', a'⟩ hin' eq ; dsimp at eq ⊢ ; subst a'
      rw [Set.mem_dprod] at hin hin' ; rcases hin with ⟨bin, ain⟩ ; rcases hin' with ⟨bin', ain'⟩
      simp only [bin, bin', reduceIte, ain, ain']
    }
    { intro hr
      funext a
      by_cases hin : a ∈ sht_lang.s
      · have tmpeq1 : a = (proj1 a, a).snd := rfl
        rw [tmpeq1] ; clear tmpeq1
        have tmpin1 : proj1 a ∈ sht_lang1.s := by rw [hsub_lang1_s] ; apply fsubst_in ; assumption
        rw [fsubst_σ] <;> try assumption
        on_goal 2=> rw [Set.mem_dprod] ; simp ; constructor ; assumption ; right ; assumption
        simp [tmpin1, hin]
      · by_cases hin2 : a ∈ sht_prog.s
        ·
          have tmpin1 : proj1 a ∈ sht_prog1.s := by rw [hsub_prog1_s] ; apply fsubst_in ; assumption
          -- use `hsurjective` here??
          rw [hsurjective] at tmpin1 ; simp at tmpin1 ; rcases tmpin1 with ⟨k, kin, heq⟩
          symm at heq
          have tmpeq1 : a = (k, a).snd := rfl
          rw [tmpeq1] ; clear tmpeq1
          -- have tmpin1 : proj1 a ∈ sht_prog1.s := by rw [hsub_prog1_s] ; apply fsubst_in ; assumption
          rw [fsubst_σ] <;> try assumption
          on_goal 2=> rw [Set.mem_dprod] ; simp ; constructor ; assumption ; left ; constructor <;> assumption
          simp [kin, hin] ; simp [hin2, heq]
        · specialize hpre a ; simp [hin, hin2] at hpre ; rw [hpre]
          symm ; apply fsubst_out ; rw [ssubst_image'', set_eq] ; simp ; constructor <;> assumption
       }
  }
  { clear tmp
    -- erh, still similar to some proof above
    rintro hv hh ⟨h', hheq, h1, h2⟩ ll hll
    specialize h1 (proj1 ll) (by rw [hsub_lang1_s] ; apply fsubst_in ; assumption)
      ll (by simp ; assumption)
    rcases h1 with ⟨pp, hpp, heq⟩ ; simp at hpp ; rcases hpp with ⟨hpp1, hpp2⟩
    exists pp ; constructor ; assumption
    subst hh
    have tmpeq1 : ll = (proj1 ll, ll).snd := rfl
    have tmpeq2 : pp = (proj1 ll, pp).snd := rfl
    rw [tmpeq1, tmpeq2] ; clear tmpeq1 tmpeq2
    rw [fsubst_σ] <;> try assumption
    rw [fsubst_σ] <;> try assumption
    · rw [Set.mem_dprod] ; simp ; constructor
      · rw [hsub_lang1_s] ; apply fsubst_in ; assumption
      · left ; constructor <;> assumption
    · rw [Set.mem_dprod] ; simp ; constructor
      · rw [hsub_lang1_s] ; apply fsubst_in ; assumption
      · right ; assumption
  }

private theorem Set.prod_image_split (f : α → β) (g : α → γ) (s : Set α)
  (hne : s.Nonempty) :
  -- (fun x ↦ (f x.1, g x.2)) '' (s ×ˢ t) = (f '' s) ×ˢ (g '' t) := by aesop
  ((fun x => (f x, g x)) '' s = s1 ×ˢ s2) →
  (f '' s = s1) ∧ (g '' s = s2) := by
  intro h
  have h' := h ; rw [Set.ext_iff] at h' ; simp at h'
  have tmp : ∃ a b, a ∈ s1 ∧ b ∈ s2 := by
    rcases hne with ⟨x, hx⟩
    specialize h' (f x) (g x) ; apply Iff.mp at h' ; specialize h' (by aesop)
    exists (f x), (g x)
  rcases tmp with ⟨a0, b0, ha0, hb0⟩
  constructor <;> ext x <;> simp
  · constructor
    · rintro ⟨o, ho, heq⟩ ; subst x
      apply Set.mem_image_of_mem at ho ; rw [h] at ho ; simp at ho
      exact ho.left
    · intro hin
      specialize h' x b0 ; apply Iff.mpr at h' ; specialize h' (by constructor <;> assumption)
      aesop
  · constructor
    · rintro ⟨o, ho, heq⟩ ; subst x
      apply Set.mem_image_of_mem at ho ; rw [h] at ho ; simp at ho
      exact ho.right
    · intro hin
      specialize h' a0 x ; apply Iff.mpr at h' ; specialize h' (by constructor <;> assumption)
      aesop

private theorem Set.full_prod_image_with_preimageRestr (f : α → β) (g : α → γ) (s : Set α) :
  (∀ a ∈ s, ∀ b ∈ s, ∃ x ∈ s, f x = f a ∧ g x = g b) →
  ∀ a ∈ f '' s, g '' (preimageRestr a f s) = g '' s := by
  intro hprod a ain ; ext y ; simp
  constructor
  · rintro ⟨x, ⟨xin, aeq⟩, yeq⟩ ; subst a y ; aesop
  · rintro ⟨x, xin, yeq⟩ ; subst y
    simp at ain ; rcases ain with ⟨z, zin, aeq⟩ ; subst a
    specialize hprod z zin x xin ; aesop

private theorem Set.full_prod_from_image_eq {f : α → β} {g : α → γ} {s : Set α} :
  (fun x => (f x, g x)) '' s = s1 ×ˢ s2 →
  ∀ a ∈ s, ∀ b ∈ s, ∃ x ∈ s, f x = f a ∧ g x = g b := by
  intro h a ain b bin
  -- rcases hbij with ⟨h1, _, h2⟩
  have ha := Set.mem_image_of_mem (fun x ↦ (f x, g x)) ain
  have hb := Set.mem_image_of_mem (fun x ↦ (f x, g x)) bin
  rw [h] at ha hb ; simp at ha hb
  have hc := Set.mem_prod (s := s1) (t := s2) (p := (f a, g b))
  rw [← h] at hc ; simp at hc ; rw [hc] ; aesop

set_option maxHeartbeats 640000 in
/-- `weird_gram_seq_full_gen`, but when the set of programs
    is effectively a product -/
theorem weird_gram_seq_full_prod
  (sht_prog sht_lang : @LGTM.SHT α)
  (sht_prog1 sht_lang1 : @LGTM.SHT β)
  (sht_prog2 sht_lang2 : @LGTM.SHT γ)
  -- without this, the bijection does not make sense
  (hne_lang : sht_lang.s.Nonempty)
  (hne_prog : sht_prog.s.Nonempty)
  -- in this case, `proj2` is "uniform" (does not have to depend on `β`);
  -- all the sets are fixed
  -- make things `β`, `γ` centric; otherwise need the inverses of `mapping`
  -- (mapping : α → β × γ)
  -- splitting should be better?
  (proj1 : α → β)
  (proj2 : α → γ)

  -- maybe surjectivity and mapsto are enough?
  -- (hbij_lang : Set.BijOn (fun a => (proj1 a, proj2 a)) sht_lang.s (sht_lang1.s ×ˢ sht_lang2.s))
  -- (hbij_prog : Set.BijOn (fun a => (proj1 a, proj2 a)) sht_prog.s (sht_prog1.s ×ˢ sht_prog2.s))
  (himage_lang : (fun x => (proj1 x, proj2 x)) '' sht_lang.s = (sht_lang1.s ×ˢ sht_lang2.s))
  (himage_prog : (fun x => (proj1 x, proj2 x)) '' sht_prog.s = (sht_prog1.s ×ˢ sht_prog2.s))
  -- (hbij_lang1 : Set.BijOn proj1 sht_lang.s sht_lang1.s)
  -- (hbij_prog1 : Set.BijOn proj1 sht_prog.s sht_prog1.s)
  -- (hbij_lang2 : Set.BijOn proj2 sht_lang.s sht_lang2.s)
  -- (hbij_prog2 : Set.BijOn proj2 sht_prog.s sht_prog2.s)
  (hdisj : Disjoint sht_prog.s sht_lang.s)
  (hdisj1 : Disjoint sht_prog1.s sht_lang1.s)
  (hdisj2 : Disjoint sht_prog2.s sht_lang2.s)

  (part1_oracle : β → β)
  (hsurjective : sht_prog1.s = (part1_oracle '' sht_lang1.s))
  (H1 Q1 : β → hProp)
  (hQ1 : [∗ i in sht_prog1.s ∪ sht_lang1.s| Q1 i ] ==>
    (fun h => ∀ ll ∈ sht_lang1.s, part1_oracle ll ∈ sht_prog1.s ∧ h ll = h (part1_oracle ll)))
  [inst : ∀ i, HPropExact (H1 i)]
  -- [inst' : ∀ i, HPropExact (Q1 i)]
  (inst' : ∀ i ∈ sht_prog1.s ∪ sht_lang1.s, HPropExact (Q1 i))
  (hshape_lang : ∀ a ∈ sht_lang.s, sht_lang.ht a = trm_seq
    -- (sht_lang1.ht (mapping a).fst)
    -- (sht_lang2.ht (mapping a).snd))
    (sht_lang1.ht (proj1 a))
    (sht_lang2.ht (proj2 a)))
  (hshape_prog : ∀ a ∈ sht_prog.s, sht_prog.ht a = trm_seq
    (sht_prog1.ht (proj1 a))
    (sht_prog2.ht (proj2 a)))

  (hpart1 : LGTM.triple [sht_prog1, sht_lang1]
    [∗ i in sht_prog1.s ∪ sht_lang1.s| H1 i ]
    (fun _ => [∗ i in sht_prog1.s ∪ sht_lang1.s| Q1 i ]))

  -- due to the "crossing", need to do such "normalization"
  (hpart2 : ∀ j ∈ sht_lang1.s,
    LGTM.triple [sht_prog2, sht_lang2]
    -- all start with the same heap, `Q1 j`
    [∗ in sht_prog2.s ∪ sht_lang2.s| Q1 j ]
    (fun _ h => ∀ ll ∈ sht_lang2.s, ∃ pp ∈ sht_prog2.s, h ll = h pp))
  :
  LGTM.triple [sht_prog, sht_lang]
  [∗ i in sht_prog.s ∪ sht_lang.s| H1 (proj1 i) ]
  (fun _ h => ∀ ll ∈ sht_lang.s, ∃ pp ∈ sht_prog.s, h ll = h pp) := by
  -- need to do the restriction on `.ht` here, otherwise the equality about `fsubst` does not work
  let sht_prog' := LGTM.SHT.mk sht_prog.s (fun a => if a ∈ sht_prog.s then sht_prog.ht a else default)
  let sht_lang' := LGTM.SHT.mk sht_lang.s (fun a => if a ∈ sht_lang.s then sht_lang.ht a else default)
  let sht_prog1' := LGTM.SHT.mk sht_prog1.s (fun a => if a ∈ sht_prog1.s then sht_prog1.ht a else default)
  let sht_lang1' := LGTM.SHT.mk sht_lang1.s (fun a => if a ∈ sht_lang1.s then sht_lang1.ht a else default)
  let sht_prog2' := LGTM.SHT.mk sht_prog2.s (fun a => if a ∈ sht_prog2.s then sht_prog2.ht a else default)
  let sht_lang2' := LGTM.SHT.mk sht_lang2.s (fun a => if a ∈ sht_lang2.s then sht_lang2.ht a else default)
  unfold LGTM.triple
  rw [LGTM.wp_sht_eq (shts' := [sht_prog', sht_lang'])]
  on_goal 2=> simp [sht_prog', sht_lang'] ; clear *- ; aesop
  have tmpeq1 : sht_prog.s = sht_prog'.s := rfl
  have tmpeq2 : sht_lang.s = sht_lang'.s := rfl
  rw [tmpeq1, tmpeq2] ; clear tmpeq1 tmpeq2
  unfold LGTM.triple at hpart1
  rw [LGTM.wp_sht_eq (shts' := [sht_prog1', sht_lang1'])] at hpart1
  on_goal 2=> simp [sht_prog1', sht_lang1'] ; clear *- ; aesop
  have tmpeq1 : sht_prog1.s = sht_prog1'.s := rfl
  have tmpeq2 : sht_lang1.s = sht_lang1'.s := rfl
  rw [tmpeq1, tmpeq2] at hpart1 ; clear tmpeq1 tmpeq2

  -- other preparations
  have tmp := himage_lang
  apply Set.prod_image_split at tmp
  rcases tmp with ⟨himage_lang1, himage_lang2⟩
  have tmp := himage_prog
  apply Set.prod_image_split at tmp
  rcases tmp with ⟨himage_prog1, himage_prog2⟩
  have himage_lang2' : ∀ j ∈ sht_lang1.s,
    sht_lang2.s = proj2 '' preimageRestr j proj1 sht_lang.s := by
    intro j jin ; rw [Set.full_prod_image_with_preimageRestr]
    · symm ; assumption
    · apply Set.full_prod_from_image_eq ; assumption
    · rw [himage_lang1] ; assumption
  have himage_prog2' : ∀ j ∈ sht_prog1.s,
    sht_prog2.s = proj2 '' preimageRestr j proj1 sht_prog.s := by
    intro j jin ; rw [Set.full_prod_image_with_preimageRestr]
    · symm ; assumption
    · apply Set.full_prod_from_image_eq ; assumption
    · rw [himage_prog1] ; assumption

  apply weird_gram_seq_full_gen
    (H := fun a => H1 (proj1 a)) (H1 := H1) (Q1 := Q1)
    (sht_prog1 := sht_prog1') (sht_lang1 := sht_lang1')
    (sht_prog2 := fun _ => sht_prog2') (sht_lang2 := fun _ => sht_lang2')
    (lang_ht_1 := fun a => if a ∈ sht_lang.s then sht_lang1.ht (proj1 a) else default)
    (lang_ht_2 := fun a => if a ∈ sht_lang.s then sht_lang2.ht (proj2 a) else default)
    (prog_ht_1 := fun a => if a ∈ sht_prog.s then sht_prog1.ht (proj1 a) else default)
    (prog_ht_2 := fun a => if a ∈ sht_prog.s then sht_prog2.ht (proj2 a) else default)
    (proj2 := fun _ => proj2)
    (part1_oracle := part1_oracle)
  all_goals try assumption
  · intro i iin ; apply inst' ; rw [← himage_prog1, ← himage_lang1, ← Set.image_union]
    apply Set.mem_image_of_mem _ iin
  · intros ; simp ; assumption
  · intro a ain ; simp only [sht_lang', ain, reduceIte] ; apply hshape_lang ; assumption
  · rw [ssubst_image''] ; symm ; assumption
  · funext b
    rw [fsubst_comp_σ_restricted_restricted] <;> try solve | simp
    rw [himage_lang1]
  · apply validSubst_comp_restricted
  · intro j jin ; rw [ssubst_image''] ; apply himage_lang2' ; assumption
  · intro j jin ; funext b ; dsimp only [sht_lang2']
    split
    · rename_i hin ; have hin' := hin ; rw [himage_lang2' _ jin] at hin'
      simp at hin' ; rcases hin' with ⟨x, xin, heq⟩ ; subst b
      rw [fsubst_σ]
      · simp [sht_lang', xin]
      · whnf ; simp ; clear *- ; aesop
      · assumption
    · rw [fsubst_out] ; rw [ssubst_image'', ← himage_lang2' _ jin] ; assumption
  · intro j jin
    whnf ; simp ; clear *- ; aesop
  · intro a ain ; simp only [sht_prog', ain, reduceIte] ; apply hshape_prog ; assumption
  · rw [ssubst_image''] ; symm ; assumption
  · funext b
    rw [fsubst_comp_σ_restricted_restricted] <;> try solve | simp
    rw [himage_prog1]
  · apply validSubst_comp_restricted
  · intro j jin ; rw [ssubst_image''] ; apply himage_prog2'
    -- need to use `hsurjective` here
    rw [hsurjective] ; apply Set.mem_image_of_mem ; assumption
  · intro j jin ; funext b ; dsimp only [sht_prog2']
    have jin' := Set.mem_image_of_mem part1_oracle jin
    -- need to use `hsurjective` here
    rw [← hsurjective] at jin'
    split
    · rename_i hin ; have hin' := hin ; rw [himage_prog2' _ jin'] at hin'
      simp at hin' ; rcases hin' with ⟨x, xin, heq⟩ ; subst b
      rw [fsubst_σ]
      · simp [sht_prog', xin]
      · whnf ; simp ; clear *- ; aesop
      · assumption
    · rw [fsubst_out] ; rw [ssubst_image'', ← himage_prog2' _ jin'] ; assumption
  · intro j jin
    whnf ; simp ; aesop
  · intros ; rfl
  · intro j jin ; specialize hpart2 j jin
    unfold LGTM.triple at hpart2 ⊢
    rw [LGTM.wp_sht_eq] ; apply hpart2
    simp ; clear *- ; aesop


end
