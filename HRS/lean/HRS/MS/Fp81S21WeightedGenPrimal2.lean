import HRS.MS.Fp81S21WeightedGenPrimal
import HRS.MS.ProClosureS111WeightedCompletion

/-! Exact all-test action of the continuously extended weighted generator. -/

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open Classical Filter Topology
open scoped RealInnerProductSpace

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R26T6 HRS.MS.ProClosureS111

/-- The chart encoding as a linear map on its full finite-norm test space. -/
def fp81s21_weightedChartEncodeMap {d r : ℕ} {Pw : ℝ}
    (E : r26t6_WeightedChart d r Pw) :
    weightedTestSubmodule d r Pw →ₗ[ℝ] fp81s21_F where
  toFun f := E.encode f
  map_add' f g := E.add _ _
    (weightedTestSubmodule_iff.1 f.property)
    (weightedTestSubmodule_iff.1 g.property)
  map_smul' a f := E.smul a f (weightedTestSubmodule_iff.1 f.property)

/-- The generator maps the full input weighted-test submodule linearly into
its bounded output weighted-test submodule. -/
def fp81s21_weightedGen_submoduleMap
    {p : Parameters} {δ : ℝ} (R : Trajectory p δ)
    (A : ℝ)
    (hb : fp81s21_bound R A) (hl : fp81s21_linear R)
    (u : ℝ) (hu : 0 ≤ u) :
    weightedTestSubmodule p.d (fp81s21_q p + 2) (fp81s21_P p) →ₗ[ℝ]
      weightedTestSubmodule p.d (fp81s21_q p) (fp81s21_P p + 2) where
  toFun f := ⟨generatorW (r26t3_coeff R) u f,
    weightedTestSubmodule_iff.2
      ((hb u hu f (weightedTestSubmodule_iff.1 f.property)).1)⟩
  map_add' := by
    intro f g
    apply Subtype.ext
    have h := hl u hu f g
      (weightedTestSubmodule_iff.1 f.property)
      (weightedTestSubmodule_iff.1 g.property) (1 : ℝ)
    simpa using h
  map_smul' := by
    intro a f
    apply Subtype.ext
    have hf : fp81s21_Input p f := weightedTestSubmodule_iff.1 f.property
    have hzero : fp81s21_Input p (0 : Euc p.d → ℝ) := by
      change IsR2WeightedTest (fp81s21_q p + 2) (fp81s21_P p) 0
      exact weightedTestSubmodule_iff.1
        (weightedTestSubmodule p.d (fp81s21_q p + 2) (fp81s21_P p)).zero_mem
    have hGzero := hl u hu (0 : Euc p.d → ℝ) 0 hzero hzero (1 : ℝ)
    have hGzero' : generatorW (r26t3_coeff R) u 0 = 0 := by
      have h' : 0 + generatorW (r26t3_coeff R) u 0 =
          generatorW (r26t3_coeff R) u 0 + generatorW (r26t3_coeff R) u 0 := by
        simpa using hGzero
      exact (add_right_cancel h').symm
    have h := hl u hu (0 : Euc p.d → ℝ) f hzero hf a
    simpa [hGzero'] using h

private theorem fp81s21_weightedGen_input_norm_le
    {p : Parameters} {δ : ℝ} (R : Trajectory p δ)
    (Es : r26t6_WeightedChart p.d (fp81s21_q p) (fp81s21_P p + 2))
    (E : r26t6_WeightedChart p.d (fp81s21_q p + 2) (fp81s21_P p))
    (A : ℝ) (hA : 0 ≤ A) (hb : fp81s21_bound R A)
    (u : ℝ) (hu : 0 ≤ u) (f : Euc p.d → ℝ)
    (hf : fp81s21_Input p f) :
    ‖Es.encode (generatorW (r26t3_coeff R) u f)‖ ≤ A * ‖E.encode f‖ := by
  have hres := hb u hu f hf
  have hnormIn := E.norm f hf
  have hnormOut := Es.norm (generatorW (r26t3_coeff R) u f) hres.1
  have hprod : ENNReal.ofReal A * fp81s21_Ein p f ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hf.2.ne
  have hreal := ENNReal.toReal_mono hprod hres.2
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hA] at hreal
  rw [hnormOut, hnormIn]
  exact hreal

theorem fp81s21_weightedGen_extension_apply_compact
    {p : Parameters} {δ : ℝ} (R : Trajectory p δ)
    (Es : r26t6_WeightedChart p.d (fp81s21_q p) (fp81s21_P p + 2))
    (E : r26t6_WeightedChart p.d (fp81s21_q p + 2) (fp81s21_P p))
    (hP : (p.d : ℝ) < 2 * fp81s21_P p)
    (A : ℝ) (hA : 0 ≤ A) (hb : fp81s21_bound R A)
    (hl : fp81s21_linear R) (u : ℝ) (hu : 0 ≤ u)
    (f : compactSmoothSubmodule p.d) :
    fp81s21_weightedGen_extension R Es E hP A hA hb hl u hu
      (E.encode f) = Es.encode (generatorW (r26t3_coeff R) u f) := by
  let S := fp81s21_embedField_strongRange hP E
  let e : S →L[ℝ] fp81s21_F := S.subtypeL
  let J0 : S →ₗ[ℝ] fp81s21_F :=
    (fp81s21_weightedGen_compactMap R Es E hP A hb hl u hu).comp
      (fp81s21_embedField_strongRangeEquiv hP E).symm.toLinearMap
  have hJbound : ∀ x : S, ‖J0 x‖ ≤ A * ‖(x : fp81s21_F)‖ := by
    intro x
    let g : compactSmoothSubmodule p.d :=
      (fp81s21_embedField_strongRangeEquiv hP E).symm x
    have hstrong : fp81s21_embedField_strongTestEncode hP E g = x.1 :=
      congrArg Subtype.val
        ((fp81s21_embedField_strongRangeEquiv hP E).apply_symm_apply x)
    have hstrong' : E.encode (g : Euc p.d → ℝ) = (x : fp81s21_F) := by
      simpa [fp81s21_embedField_strongTestEncode] using hstrong
    have hgin : fp81s21_Input p (g : Euc p.d → ℝ) :=
      weightedTestSubmodule_iff.1
        (weighted_test_of_compact_smooth
          (r := fp81s21_q p + 2) (Pw := fp81s21_P p) hP g.property)
    change ‖fp81s21_weightedGen_compactMap R Es E hP A hb hl u hu g‖ ≤
      A * ‖(x : fp81s21_F)‖
    change ‖Es.encode (generatorW (r26t3_coeff R) u g)‖ ≤
      A * ‖(x : fp81s21_F)‖
    calc
      ‖Es.encode (generatorW (r26t3_coeff R) u g)‖ ≤ A * ‖E.encode g‖ :=
      fp81s21_weightedGen_input_norm_le R Es E A hA hb u hu
          (g : Euc p.d → ℝ) hgin
      _ = A * ‖(x : fp81s21_F)‖ := by rw [hstrong']
  let J : S →L[ℝ] fp81s21_F := LinearMap.mkContinuous J0 A hJbound
  have hdense := fp81s21_embedField_strongRange_dense hP E
  have heNorm : ∀ x : S, ‖e x‖ = ‖(x : fp81s21_F)‖ := fun _ => rfl
  have heUniform : IsUniformInducing e :=
    (AddMonoidHomClass.isometry_of_norm e heNorm).isUniformInducing
  let x : S := ⟨E.encode f, ⟨f, by simp [fp81s21_embedField_strongTestEncode]⟩⟩
  have hx : e x = E.encode f := rfl
  have hI : (fp81s21_embedField_strongRangeEquiv hP E).symm x = f := by
    apply (fp81s21_embedField_strongRangeEquiv hP E).injective
    calc
      _ = x := (fp81s21_embedField_strongRangeEquiv hP E).apply_symm_apply x
      _ = _ := by apply Subtype.ext; rfl
  change ContinuousLinearMap.extend J e (E.encode f) = _
  rw [← hx, ContinuousLinearMap.extend_eq (h_dense := hdense) (h_e := heUniform)]
  change fp81s21_weightedGen_compactMap R Es E hP A hb hl u hu
      ((fp81s21_embedField_strongRangeEquiv hP E).symm x) = _
  rw [hI]
  rfl

/-- The extension agrees with the generator on every finite-norm input test,
not only on the compact smooth dense core. -/
theorem fp81s21_weightedGen_extension_apply_input
    {p : Parameters} {δ : ℝ} (R : Trajectory p δ)
    (Es : r26t6_WeightedChart p.d (fp81s21_q p) (fp81s21_P p + 2))
    (E : r26t6_WeightedChart p.d (fp81s21_q p + 2) (fp81s21_P p))
    (hP : (p.d : ℝ) < 2 * fp81s21_P p)
    (A : ℝ) (hA : 0 ≤ A) (hb : fp81s21_bound R A)
    (hl : fp81s21_linear R) (u : ℝ) (hu : 0 ≤ u)
    (f : Euc p.d → ℝ) (hf : fp81s21_Input p f) :
    fp81s21_weightedGen_extension R Es E hP A hA hb hl u hu
      (E.encode f) = Es.encode (generatorW (r26t3_coeff R) u f) := by
  let fw : weightedTestSubmodule p.d (fp81s21_q p + 2) (fp81s21_P p) :=
    ⟨f, weightedTestSubmodule_iff.2 hf⟩
  obtain ⟨g, hg, hconv⟩ := weighted_smooth_approximation hP fw
  have hjetErr : Tendsto
      (fun n => ‖weightedJetMap p.d (fp81s21_q p + 2) (fp81s21_P p) (g n) -
        weightedJetMap p.d (fp81s21_q p + 2) (fp81s21_P p) fw‖)
      atTop (𝓝 0) := tendsto_iff_norm_sub_tendsto_zero.1 hconv
  have hencodeErr : Tendsto
      (fun n => ‖E.encode (g n) - E.encode f‖) atTop (𝓝 0) := by
    have heq : ∀ n,
        ‖E.encode (g n) - E.encode f‖ =
          ‖weightedJetMap p.d (fp81s21_q p + 2) (fp81s21_P p) (g n) -
            weightedJetMap p.d (fp81s21_q p + 2) (fp81s21_P p) fw‖ := by
      intro n
      let dfn := g n - fw
      have hdf : fp81s21_Input p dfn :=
        weightedTestSubmodule_iff.1 dfn.property
      have hE := E.norm dfn hdf
      have hJ := weightedJetMap_norm dfn
      have hmapE : E.encode (dfn : Euc p.d → ℝ) = E.encode (g n) - E.encode f := by
        change fp81s21_weightedChartEncodeMap E dfn = _
        rw [map_sub]
        rfl
      have hmapJ : weightedJetMap p.d (fp81s21_q p + 2) (fp81s21_P p) dfn =
          weightedJetMap p.d (fp81s21_q p + 2) (fp81s21_P p) (g n) -
            weightedJetMap p.d (fp81s21_q p + 2) (fp81s21_P p) fw := by
        rw [map_sub]
      calc
        ‖E.encode (g n) - E.encode f‖ = ‖E.encode (dfn : Euc p.d → ℝ)‖ := by
          rw [hmapE]
        _ = ‖weightedJetMap p.d (fp81s21_q p + 2) (fp81s21_P p) dfn‖ := by
          rw [hE, hJ]
        _ = _ := by rw [hmapJ]
    simpa only [heq] using hjetErr
  have hsource : Tendsto (fun n => E.encode (g n)) atTop (𝓝 (E.encode f)) :=
    (tendsto_iff_norm_sub_tendsto_zero).2 hencodeErr
  let G := fp81s21_weightedGen_submoduleMap R A hb hl u hu
  let Emap := fp81s21_weightedChartEncodeMap E
  let Hmap := fp81s21_weightedChartEncodeMap Es
  let H : weightedTestSubmodule p.d (fp81s21_q p + 2) (fp81s21_P p) →ₗ[ℝ]
      fp81s21_F := Hmap.comp G
  have hHerror : ∀ n,
      ‖H (g n) - H fw‖ ≤ A * ‖E.encode (g n) - E.encode f‖ := by
    intro n
    let dfn := g n - fw
    have hdf : fp81s21_Input p dfn := weightedTestSubmodule_iff.1 dfn.property
    have hbound := fp81s21_weightedGen_input_norm_le
      R Es E A hA hb u hu dfn hdf
    have hencodeSub : E.encode (dfn : Euc p.d → ℝ) =
        E.encode (g n) - E.encode f := by
      change Emap dfn = _
      rw [map_sub]
      rfl
    calc
      ‖H (g n) - H fw‖ = ‖H dfn‖ := by rw [← map_sub]
      _ = ‖Es.encode (generatorW (r26t3_coeff R) u dfn)‖ := by rfl
      _ ≤ A * ‖E.encode (dfn : Euc p.d → ℝ)‖ := hbound
      _ = A * ‖E.encode (g n) - E.encode f‖ := by rw [hencodeSub]
  have hmulErr : Tendsto
      (fun n => A * ‖E.encode (g n) - E.encode f‖) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul hencodeErr)
  have hHerrorTendsto : Tendsto (fun n => ‖H (g n) - H fw‖) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hmulErr
      (fun n => norm_nonneg _) hHerror
  have hH : Tendsto (fun n => H (g n)) atTop (𝓝 (H fw)) :=
    (tendsto_iff_norm_sub_tendsto_zero).2 hHerrorTendsto
  have hcompact : ∀ n,
      fp81s21_weightedGen_extension R Es E hP A hA hb hl u hu
          (E.encode (g n)) = H (g n) := by
    intro n
    let cn : compactSmoothSubmodule p.d := ⟨g n, hg n⟩
    have hc := fp81s21_weightedGen_extension_apply_compact
      R Es E hP A hA hb hl u hu cn
    simpa [H, Hmap, G, fp81s21_weightedChartEncodeMap,
      fp81s21_weightedGen_submoduleMap, cn] using hc
  have hTsource : Tendsto
      (fun n => fp81s21_weightedGen_extension R Es E hP A hA hb hl u hu
        (E.encode (g n))) atTop
      (𝓝 (fp81s21_weightedGen_extension R Es E hP A hA hb hl u hu (E.encode f))) :=
    ((fp81s21_weightedGen_extension R Es E hP A hA hb hl u hu).continuous.tendsto
      (E.encode f)).comp hsource
  have hTsource' : Tendsto (fun n => H (g n)) atTop
      (𝓝 (fp81s21_weightedGen_extension R Es E hP A hA hb hl u hu (E.encode f))) :=
    hTsource.congr' (Eventually.of_forall hcompact)
  have hlimit := tendsto_nhds_unique hTsource' hH
  change fp81s21_weightedGen_extension R Es E hP A hA hb hl u hu
      (E.encode f) = Es.encode (generatorW (r26t3_coeff R) u f)
  simpa [H, Hmap, G, fp81s21_weightedChartEncodeMap,
    fp81s21_weightedGen_submoduleMap, fw] using hlimit

theorem fp81s21_b3_primal
    {p : Parameters} {δ : ℝ} (R : Trajectory p δ)
    (Es : r26t6_WeightedChart p.d (fp81s21_q p) (fp81s21_P p + 2))
    (E : r26t6_WeightedChart p.d (fp81s21_q p + 2) (fp81s21_P p))
    (A : ℝ) (hA : 0 ≤ A)
    (hb : fp81s21_bound R A) (hl : fp81s21_linear R) :
    ∃ T : ℝ → fp81s21_F →L[ℝ] fp81s21_F,
      fp81s21_primal R Es E A T := by
  have hP : (p.d : ℝ) < 2 * fp81s21_P p := by
    dsimp [fp81s21_P]
    have hd : 0 ≤ (p.d : ℝ) := Nat.cast_nonneg _
    linarith
  let T : ℝ → fp81s21_F →L[ℝ] fp81s21_F := fun u =>
    fp81s21_weightedGen_extension R Es E hP A hA hb hl (max u 0)
      (le_max_right u 0)
  refine ⟨T, ?_⟩
  change ∀ u, ‖T u‖ ≤ A ∧ ∀ f, fp81s21_Input p f →
    T u (E.encode f) = Es.encode (generatorW (r26t3_coeff R) (max u 0) f)
  intro u
  refine ⟨?_, ?_⟩
  · simpa [T] using fp81s21_weightedGen_extension_norm_le
      R Es E hP A hA hb hl (max u 0) (le_max_right u 0)
  · intro f hf
    exact fp81s21_weightedGen_extension_apply_input
      R Es E hP A hA hb hl (max u 0) (le_max_right u 0) f hf

#print axioms HRS.Fp81.S21.fp81s21_weightedGen_extension_apply_compact
#print axioms HRS.Fp81.S21.fp81s21_weightedGen_extension_apply_input
#print axioms HRS.Fp81.S21.fp81s21_b3_primal

end HRS.Fp81.S21
