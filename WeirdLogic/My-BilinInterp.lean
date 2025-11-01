-- import Mathlib.MeasureTheory.Integral.Bochner

-- import Mathlib.Data.Int.Interval
-- import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
-- import Mathlib.MeasureTheory.Integral.SetIntegral

-- import Lgtm.Hyper.ProofMode
-- import Lgtm.Hyper.ArraysFun

-- import Lgtm.Experiments.HyperCommon
-- import Lgtm.Experiments.Comparison.Code
-- import Lgtm.Experiments.Comparison.Hyper.SearchSRLE

-- open Lang Unary prim val trm
-- open Classical

-- attribute [-simp] fun_insert Bool.forall_bool
-- attribute [simp] Set.univ_inter

-- syntax "/=='" : ssrTriv
-- macro_rules | `(ssrTriv| /==') => `(tactic| try simp[Finset.mem_Ico, Finset.mem_Ico])

-- local
-- macro_rules | `(ssrTriv| //') => `(tactic| solve | (try intro); intros; aesop)
-- set_option maxHeartbeats 1600000

-- section Unary
-- variable (xleft xright xval : loc) (z n : ℤ) (N : ℕ)
-- variable (x_left x_right : ℤ -> ℝ) (x_val : ℤ -> ℝ)

-- variable (x_lr : ∀ i ∈ ⟦z, n⟧, x_left i <= x_right i)
-- variable (x_rl : ∀ i ∈ ⟦z, n-1⟧, x_right i <= x_left (i + 1))
-- variable (zLn : z < n) (oLz : 0 <= z) (nLN : n <= N)
-- include x_lr x_rl zLn oLz nLN

-- #check LGTM.triple
-- lemma searchSRLE_hspec : i ∈ ⟦z, n⟧ -> f '' s ⊆ Set.Ico (x_left i) (x_right i) ->
--   arr⟨⟪l,s⟫⟩(left, x in N => x_left x) ∗ arr⟨⟪l,s⟫⟩(right, x in N => x_right x) ==>
--     hwp ⟪l, s⟫ (fun i ↦ [lang| searchSRLE(⸨left:Loc⸩, ⸨right:Loc⸩, ⟨f i.val⟩ , z, n)])
--     fun v ↦ ⌜v = fun _ ↦ val_int i⌝ ∗ arr⟨⟪l,s⟫⟩(left, x in N => x_left x) ∗ arr⟨⟪l,s⟫⟩(right, x in N => x_right x) := by
--   move=> ? sub; yprod searchSparseRLE_spec'=> // ??; apply sub=> //

-- omit x_lr x_rl xleft xright xval x_val  in
-- lemma searchSRLE_hspec_out  :
--   Disjoint (f '' s) (⋃ i ∈ ⟦z, n⟧, Set.Ico (x_left i) (x_right i)) ->
--   arr⟨⟪l,s⟫⟩(left, x in N => x_left x) ∗ arr⟨⟪l,s⟫⟩(right, x in N => x_right x) ==>
--     hwp ⟪l, s⟫ (fun i ↦ [lang| searchSRLE(⸨left:Loc⸩, ⸨right:Loc⸩, ⟨f i.val⟩ , z, n)])
--     fun v ↦ ⌜v = fun _ ↦ val_int n⌝ ∗ arr⟨⟪l,s⟫⟩(left, x in N => x_left x) ∗ arr⟨⟪l,s⟫⟩(right, x in N => x_right x) := by
--   move=> /Set.disjoint_left ?; yprod searchSparseRLE_spec_out

-- omit x_lr x_rl  in
-- @[yapp]
-- lemma get_spec_out (l : ℕ) (s : Set ℝ) :
--   Disjoint s (⋃ i ∈ ⟦z, n⟧, Set.Ico (x_left i) (x_right i)) ->
--   arr⟨⟪l,s⟫⟩(xleft, x in N => x_left x) ∗
--   arr⟨⟪l,s⟫⟩(xright, x in N => x_right x) ∗
--   arr⟨⟪l,s⟫⟩(xval, x in N => x_val x) ==>
--     WP [l| i in s => Lang.get(⸨xleft:Loc⸩, ⸨xright:Loc⸩, ⸨xval:Loc⸩, ⟨i.val⟩ , z, n)] { v,
--     ⌜ v = fun _ => val_real 0 ⌝ ∗
--     arr⟨⟪l,s⟫⟩(xleft, x in N => x_left x) ∗
--     arr⟨⟪l,s⟫⟩(xright, x in N => x_right x) ∗
--     arr⟨⟪l,s⟫⟩(xval, x in N => x_val x) } := by
--   simp=> ?;
--   ystep searchSRLE_hspec_out (f := id) (zLn := zLn) (oLz := oLz) (nLN := nLN)=> /== //
--   ystep; yyifT; yyval; ysimp=> //'

-- open MeasureTheory
-- open scoped Function -- required for scoped `on` notation

-- omit zLn oLz nLN in
-- lemma disj_lr : Set.Pairwise ((Finset.Ico z n)) (Disjoint on fun x ↦ Set.Ico (x_left x) (x_right x)) := by
--   move=> x /== ?? y ?? ?
--   scase: [x < y]=> [?|]
--   { shave: y < x; omega
--     move=> /(left_right_monotone_rl _ _ x_lr); aesop }
--   move=> /(left_right_monotone_rl _ _ x_lr); aesop

-- attribute [aesop norm simp] Finset.mem_Ico
-- attribute [-simp] Finset.mem_Ico
-- set_option maxRecDepth 1500 in
-- lemma linearInterp_spec (r : ℝ)  :
--   { arr⟨⋆⟩(xleft, x in N => x_left x) ∗
--     arr⟨⋆⟩(xright, x in N => x_right x) ∗
--     arr⟨⋆⟩(xval, x in N => x_val x) }
--   [1| x in {r} => Lang.linearInterp(⸨xleft:Loc⸩, ⸨xright:Loc⸩, ⸨xval:Loc⸩, z, n)]
--   [2| i in ⋆ => Lang.get(⸨xleft:Loc⸩, ⸨xright:Loc⸩, ⸨xval:Loc⸩, ⟨i.val⟩ , z, n)]
--   {v,
--     ⌜v ⟨1,r⟩ = ∫ i, (v ⟨2,i⟩).toReal⌝ ∗
--     arr⟨⋆⟩(xleft, x in N => x_left x) ∗
--     arr⟨⋆⟩(xright, x in N => x_right x) ∗
--     arr⟨⋆⟩(xval, x in N => x_val x) } := by
--   yfocus 2, ⋃ i ∈ ⟦z,n⟧, Set.Ico (x_left i) (x_right i)
--   yapp=> //' <;> try exact Set.disjoint_sdiff_left
--   simp [fun_insert, OfNat.ofNat, Zero.zero]
--   yin 1: yyref ans
--   let op := (fun (hv : hval ℝˡ) (i : ℤ) => ∫ j in Set.Ico (x_left i) (x_right i), (hv ⟨2,j⟩).toReal)
--   let P := (fun (hv : hval ℝˡ) i => IntegrableOn (fun j => (hv ⟨2,j⟩).toReal) (Set.Ico (x_left i) (x_right i)))
--   yfor+. with
--     (Q := fun i hv => ans ~⟨k in ⟪1, {r}⟫⟩~> op hv i ∗ ⌜P hv i⌝)
--     (H₀ := ans ~⟨i in ⟪1, {r}⟫⟩~> val_real 0) <;> try simp [op, P]
--   { move=> j > /== ??; simp [Set.EqOn]=> eq; congr! 2; ext
--     rw [setIntegral_congr_fun (hs := measurableSet_Ico)]; move; aesop
--     rw [integrableOn_congr_fun (hs := measurableSet_Ico)]; move; aesop }
--   { move=> > ??;
--     yin 1: sdo 5 ystep=> //'; yapp
--     ystep @searchSRLE_hspec (f := id) (i := i)=> /== //
--     ystep; yyifF; yapp; ysimp=> //' /=='
--     srw mul_comm ENNReal.toReal_ofReal /== //' }
--   yapp=> ?; ysimp=> /==
--   srw -integral_finset_biUnion //'
--   { srw -[2](setIntegral_eq_integral_of_forall_compl_eq_zero
--              (s := ⋃ i ∈ Finset.Ico z n, (Set.Ico (x_left i) (x_right i))))
--     { apply setIntegral_congr_fun=> [|?]//
--       apply Finset.measurableSet_biUnion=> //' }
--     move=> /== ??; srw if_neg // }
--   sby apply disj_lr

-- end Unary

-- section Binary

-- variable (xleft xright yprt yleft yright yval : loc)
-- variable (x_left x_right y_left y_right : ℤ -> ℝ) (y_ptr : ℤ -> ℤ) (y_val : ℤ -> ℝ)
-- variable (N M : ℕ) (NG0 : N > 0)

-- variable (x_lr : ∀ i ∈ ⟦0, N⟧, x_left i < x_right i)
-- variable (x_rl : ∀ i ∈ ⟦0, N-1⟧, x_right i <= x_left (i + 1))

-- variable (y_ptr_mon : StrictMonoOn y_ptr ⟦0, N+1⟧)
-- variable (y_ptr_N : y_ptr N = M) (y_ptr_0 : y_ptr 0 = 0)

-- variable (y_lr : ∀ i ∈ ⟦0,N⟧, ∀ j ∈ ⟦y_ptr i, y_ptr (i + 1)⟧, y_left j <= y_right j)
-- variable (y_rl : ∀ i ∈ ⟦0,N⟧, ∀ j ∈ ⟦y_ptr i, y_ptr (i + 1)-1⟧, y_right j <= y_left (j + 1))

-- include NG0 x_lr x_rl y_ptr_mon y_ptr_N y_ptr_0 y_lr y_rl

-- open MeasureTheory

-- omit y_ptr_mon y_ptr_0 y_lr y_rl x_lr  x_rl y_ptr_N in
-- @[yapp]
-- lemma get2_spec_out (s : Set (ℝ × ℝ)) :
--   Disjoint s ((⋃ i ∈ ⟦0, N⟧, Set.Ico (x_left i) (x_right i)) ×ˢ ⋆) ->
--   arr⟨⟪l,s⟫⟩(xleft , x in N => x_left x)  ∗
--   arr⟨⟪l,s⟫⟩(xright, x in N => x_right x) ==>
--   WP [l| ij in s => Lang.get2(⸨xleft:Loc⸩, ⸨xright:Loc⸩, ⸨yprt:Loc⸩, ⸨yleft:Loc⸩, ⸨yright:Loc⸩, ⸨yval:Loc⸩, ⟨ij.val.1⟩ , ⟨ij.val.2⟩)] { v,
--     ⌜v = fun _ => val_real 0⌝ ∗
--     arr⟨⟪l,s⟫⟩(xleft , x in N => x_left x)  ∗
--     arr⟨⟪l,s⟫⟩(xright, x in N => x_right x) } := by
--     move=> /Set.disjoint_left dj; ystep
--     ystep searchSRLE_hspec_out=> //'
--     { ystep; yyifT; yyval; ysimp=> //' }
--     srw Set.disjoint_left; aesop

-- attribute [-simp] Finset.mem_Ico Set.singleton_prod

-- #check yfor_lemma

-- set_option maxRecDepth 2000 in
-- set_option maxHeartbeats 6400000 in
-- lemma bilinearInterp_spec_entire  :
--   { arr⟨⋆⟩(xleft , x in N => x_left x)  ∗
--     arr⟨⋆⟩(xright, x in N => x_right x) ∗

--     arr⟨⋆⟩(yprt  , x in N+1 => y_ptr x)   ∗
--     arr⟨⋆⟩(yleft , x in M => y_left x)  ∗
--     arr⟨⋆⟩(yright, x in M => y_right x) ∗

--     arr⟨⋆⟩(yval  , x in M => y_val x) }
--   [1| x in {(r₁, r₂)}         => Lang.bilinearInterp(⸨xleft:Loc⸩, ⸨xright:Loc⸩, ⸨yprt:Loc⸩, ⸨yleft:Loc⸩, ⸨yright:Loc⸩, ⸨yval:Loc⸩)]
--   [2| ij in @Set.univ (ℝ × ℝ) => Lang.get2(⸨xleft:Loc⸩, ⸨xright:Loc⸩, ⸨yprt:Loc⸩, ⸨yleft:Loc⸩, ⸨yright:Loc⸩, ⸨yval:Loc⸩, ⟨ij.val.1⟩ , ⟨ij.val.2⟩)]
--   {Grid,
--     ⌜Grid ⟨1,r₁,r₂⟩ = ∫ (i : ℝ) (j : ℝ), (Grid ⟨2,i,j⟩).toReal⌝ ∗ ⊤ } := by
--     unfold LGTM.triple
--     apply yfocus_set_lemma 2 ((⋃ i ∈ ⟦0, N⟧, Set.Ico (x_left i) (x_right i)) ×ˢ ⋆)
--     =>/=; -- focus, x is y in paper
--     try simp [disjE]; try simp [disjE]; skip
--     yapp get2_spec_out <;> try exact Set.disjoint_sdiff_left -- remove 0s, use get2_spec_out, second part: side goal
--     simp [fun_insert, OfNat.ofNat]; simp [Zero.zero] -- before yin: (9)
--     yin 1: yyref ans -- yyref: SEQU1
--     yin 1: ystep; simp [OfNat.ofNat]; simp [Zero.zero, One.one] -- ystep: SEQU1; after this: (9)
--     srw biUnion_prod_const
--     let op := fun (hv : hval (ℝ×ℝ)ˡ) i => ∫ i in Set.Ico (x_left i) (x_right i), ∫ j, (hv ⟨2,i,j⟩).toReal
--     let P := fun (hv : hval (ℝ×ℝ)ˡ) i => IntegrableOn (fun i => ∫ j, (hv ⟨2,i,j⟩).toReal) (Set.Ico (x_left i) (x_right i))

--     yfor+. with -- longest goal: the one before (13)
--       (Q := fun i hv => ans ~⟪1, {(r₁, r₂)}⟫~> op hv i ∗ ⌜P hv i⌝)
--       (H₀ := ans ~⟪1,{(r₁, r₂)}⟫~> val_real 0)<;> try simp [op, P]
--     { move=> j > /== ?? eq; congr! 2; ext
--       rw [setIntegral_congr_fun (hs := measurableSet_Ico)];
--       intro x _; simp [fun j => @eq ⟨2, x, j⟩ (by aesop)]
--       rw [integrableOn_congr_fun (hs := measurableSet_Ico)];
--       intro x _; simp [fun j => @eq ⟨2, x, j⟩ (by aesop)] }
--     { move=> ??
--       yin 1: sdo 3 ystep=> //'
--       yin 2: ystep
--              ystep @searchSRLE_hspec (i := i); rotate_left
--              { move=> ? /x_lr /le_of_lt //' }
--              ystep; yyifF; sdo 3 ystep=> //' -- (13)
--       ymerge 2 with (μ := fun x => ⟨x_left i, x.2⟩)=> //'
--       erw [(img_sep (f := fun _ => x_left i) (g := id)), Set.Nonempty.image_const]=> /== //' -- outmost integral
--       ysubst with (σ := Prod.snd)
--       zapp linearInterp_spec=> //' -- use (14), (15) --> (16)
--       { apply y_ptr_mon=> /== //' }
--       { srw -y_ptr_0 StrictMonoOn.le_iff_le=> // /== //' }
--       { srw /== -y_ptr_N StrictMonoOn.le_iff_le=> // /== //' }
--       move=> ->; sdo 3 ystep=> //'; ystep; yapp; ysimp
--       move=> ? _; srw mul_comm ENNReal.toReal_ofReal;
--       specialize x_lr i ?_=> //'; linarith }
--     yapp=> ?; ysimp=> /==
--     srw -integral_finset_biUnion //'
--     { srw -[2](setIntegral_eq_integral_of_forall_compl_eq_zero
--                (s := ⋃ i ∈ ⟦0, N⟧, (Set.Ico (x_left i) (x_right i))))
--       { apply setIntegral_congr_fun=> [|?]//
--         apply Finset.measurableSet_biUnion=> //' }
--       intros; simp (disch := aesop) only [if_neg]; simp }
--     apply disj_lr=> //' ? /x_lr /le_of_lt //'
