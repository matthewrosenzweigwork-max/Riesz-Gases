import HRS.MS.Fp81S21GaussFeature
import HRS.MS.Fp81S21Absorption
import HRS.MS.Fp81S21MovingNoiseBounds

/-! Classical-adjoint estimates for the literal Gaussian features. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Filter Topology Set Classical
open scoped ENNReal NNReal BigOperators RealInnerProductSpace
namespace HRS.Fp81.S21
open HRS (Euc)
open HRS.Whole HRS.MS.R26T3 HRS.MS.S111X2

theorem fp81s21_feature_measure_domination
    {d : ℕ} {ρ σ : Euc d → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (hσ : Measurable σ) (hdom : ∀ x, ρ x ≤ K * σ x) :
    HRS.Whole.withDensityReal ρ ≤ ENNReal.ofReal K • HRS.Whole.withDensityReal σ := by
  refine Measure.le_iff'.2 fun A => ?_
  unfold HRS.Whole.withDensityReal
  rw [withDensity_apply']
  rw [Measure.smul_apply, smul_eq_mul]
  rw [withDensity_apply']
  calc
    ∫⁻ x in A, ENNReal.ofReal (ρ x) ≤
        ∫⁻ x in A, ENNReal.ofReal K * ENNReal.ofReal (σ x) := by
      apply lintegral_mono
      intro x
      calc
        ENNReal.ofReal (ρ x) ≤ ENNReal.ofReal (K * σ x) :=
          ENNReal.ofReal_le_ofReal (hdom x)
        _ = ENNReal.ofReal K * ENNReal.ofReal (σ x) := ENNReal.ofReal_mul hK
    _ = ENNReal.ofReal K * ∫⁻ x in A, ENNReal.ofReal (σ x) := by
      rw [lintegral_const_mul]
      exact ENNReal.measurable_ofReal.comp hσ

theorem fp81s21_feature_variance_domination
    {d : ℕ} {μ ν : Measure (Euc d)} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {K : ℝ} (hK : 0 ≤ K) (hμν : μ ≤ ENNReal.ofReal K • ν)
    {f : Euc d → ℝ} (hfμ : MemLp f 2 μ) (hfν : MemLp f 2 ν) :
    HRS.MS.S111X2.s111x2_centeredSquare μ f ≤
      K * HRS.MS.S111X2.s111x2_centeredSquare ν f := by
  let g : Euc d → ℝ := fun x => f x - HRS.Whole.pair ν f
  have hgm : MemLp g 2 μ := hfμ.sub (memLp_const _)
  have hgn : MemLp g 2 ν := hfν.sub (memLp_const _)
  have hvarμ : HRS.MS.S111X2.s111x2_centeredSquare μ f = ProbabilityTheory.variance f μ := by
    unfold HRS.MS.S111X2.s111x2_centeredSquare
    rw [ProbabilityTheory.variance_eq_integral hfμ.aemeasurable]
    rfl
  have hshift : ProbabilityTheory.variance f μ = ProbabilityTheory.variance g μ := by
    simpa [g, sub_eq_add_neg] using
      (ProbabilityTheory.variance_add_const hfμ.aestronglyMeasurable
        (-HRS.Whole.pair ν f)).symm
  have hvarle : ProbabilityTheory.variance g μ ≤ ∫ x, g x ^ 2 ∂μ :=
    ProbabilityTheory.variance_le_expectation_sq hgm.aestronglyMeasurable
  have hscaled : Integrable (fun x => g x ^ 2) (ENNReal.ofReal K • ν) :=
    hgn.integrable_sq.smul_measure ENNReal.ofReal_ne_top
  have hmeasure := integral_mono_measure hμν
    (Filter.Eventually.of_forall fun x => sq_nonneg (g x)) hscaled
  rw [integral_smul_measure, ENNReal.toReal_ofReal hK, smul_eq_mul] at hmeasure
  calc
    HRS.MS.S111X2.s111x2_centeredSquare μ f = ProbabilityTheory.variance f μ := hvarμ
    _ = ProbabilityTheory.variance g μ := hshift
    _ ≤ ∫ x, g x ^ 2 ∂μ := hvarle
    _ ≤ K * ∫ x, g x ^ 2 ∂ν := hmeasure
    _ = K * HRS.MS.S111X2.s111x2_centeredSquare ν f := by
      simp [g, HRS.MS.S111X2.s111x2_centeredSquare, HRS.Whole.projMean]

/-- The chosen propagator agrees with any supplied classical adjoint on its interval. -/
theorem fp81s21_feature_classical_eq
    (p : Parameters) {δ r : ℝ} (R : Trajectory p δ) (hr : 0 ≤ r)
    {g : Euc p.d → ℝ} {u : ℝ → Euc p.d → ℝ}
    (hu : IsClassicalAdjointW (r26t3_coeff R) r g u) :
    ∀ s ∈ Icc (0 : ℝ) r, propagatorW (r26t3_coeff R) s r g = u s := by
  exact HRS.MS.S104e.s104e_unique p.hd p.hs0 (by linarith [p.hs]) p.ha p.hβ
    δ p.c₁ p.C₁ R.thermal R.admissible R.resulting r hr ⟨hr, le_rfl⟩ hu

/-- Kernel membership and the thermal Dirichlet bound for arbitrary classical data. -/
theorem fp81s21_feature_classical_noise
    (p : Parameters) {δ r : ℝ} (R : Trajectory p δ)
    (hδ : 0 < δ) (hδh : δ ≤ 1 / 2) (hr : 0 ≤ r)
    {g : Euc p.d → ℝ} {u : ℝ → Euc p.d → ℝ}
    (hu : IsClassicalAdjointW (r26t3_coeff R) r g u) :
    MemLp (movingNoiseKernel R 0 r g) 2
        ((volume : Measure ℝ).prod (volume : Measure (Euc p.d))) ∧
    ‖movingNoiseFeature R 0 r g‖ ^ 2 ≤
      (2 * p.β⁻¹ * p.C₁) *
        ∫ s in Icc (0 : ℝ) r, ∫ x, ‖gradient (u s) x‖ ^ 2
          ∂(HRS.Whole.withDensityReal R.ρβ) := by
  let μ := (volume : Measure ℝ).prod (volume : Measure (Euc p.d))
  let V : ℝ × Euc p.d → Euc p.d := fun q =>
    if q.1 ∈ Icc (0 : ℝ) r then gradient (u q.1) q.2 else 0
  have hV : Measurable V := HRS.MS.R2Interp.s102_gradJoint_meas hu
  have heq := fp81s21_feature_classical_eq p R hr hu
  obtain ⟨-, hC, -, -⟩ := r26t3_reference_data p δ hδ hδh R
  have hβ : 0 ≤ 2 * p.β⁻¹ := mul_nonneg (by norm_num) (inv_nonneg.mpr p.hβ.le)
  have hρβ : Measurable R.ρβ := R.thermal.1.1.measurable
  have hρβ0 : ∀ x, 0 ≤ R.ρβ x := R.thermal.1.1.nonneg
  let κ : ℝ := 2 * p.β⁻¹ * p.C₁
  have hκ : 0 ≤ κ := mul_nonneg hβ hC.le
  let clip : ℝ → Icc (0 : ℝ) r := fun s =>
    ⟨max 0 (min s r), le_max_left _ _, max_le hr (min_le_right _ _)⟩
  have hclip : Continuous clip :=
    (continuous_const.max (continuous_id.min continuous_const)).subtype_mk _
  have hρ : Measurable (fun q : ℝ × Euc p.d => R.ρ (clip q.1) q.2) :=
    (fp81s21_moving_density_joint_meas (H := r) p R hδ hδh).comp
      ((hclip.comp continuous_fst).prodMk continuous_snd).measurable
  have hker : movingNoiseKernel R 0 r g = fun q =>
      (Real.sqrt (2 * p.β⁻¹) * Real.sqrt (R.ρ (clip q.1) q.2)) • V q := by
    funext q
    by_cases hq : q.1 ∈ Icc (0 : ℝ) r
    · simp only [movingNoiseKernel, V, if_pos hq, r26t3_U, heq q.1 hq]
      change _ = (Real.sqrt (2 * p.β⁻¹) *
        Real.sqrt (R.ρ (max 0 (min q.1 r)) q.2)) • gradient (u q.1) q.2
      rw [min_eq_left hq.2, max_eq_right hq.1]
    · simp only [movingNoiseKernel, V, if_neg hq, smul_zero]
  have hkm : Measurable (movingNoiseKernel R 0 r g) := by
    rw [hker]
    exact (measurable_const.mul (Real.continuous_sqrt.measurable.comp hρ)).smul hV
  let env : ℝ × Euc p.d → ℝ := fun q => κ * (R.ρβ q.2 * ‖V q‖ ^ 2)
  have hem : Measurable env := measurable_const.mul
    ((hρβ.comp measurable_snd).mul (hV.norm.pow_const 2))
  obtain ⟨M, hM, hMb⟩ := HRS.MS.S111X1.x1_fderiv_bdd hu
  let b : ℝ → ℝ := (Icc (0 : ℝ) r).indicator (fun _ => κ * M ^ 2)
  have hb : Integrable b := by
    exact (integrable_indicator_iff measurableSet_Icc).2
      (integrableOn_const measure_Icc_lt_top.ne)
  have hmajor : Integrable (fun q : ℝ × Euc p.d => b q.1 * R.ρβ q.2) μ :=
    hb.mul_prod (HRS.Whole.Q34.integrable_of_isProbDensity R.thermal.1.1)
  have he0 : ∀ q, 0 ≤ env q := fun q =>
    mul_nonneg hκ (mul_nonneg (hρβ0 _) (sq_nonneg _))
  have hei : Integrable env μ := by
    apply hmajor.mono' hem.aestronglyMeasurable
    filter_upwards with q
    rw [Real.norm_of_nonneg (he0 q)]
    by_cases hq : q.1 ∈ Icc (0 : ℝ) r
    · have hsq := pow_le_pow_left₀ (norm_nonneg _) (hMb q.1 hq q.2) 2
      simp only [env, V, if_pos hq, b, indicator_of_mem hq]
      calc
        κ * (R.ρβ q.2 * ‖gradient (u q.1) q.2‖ ^ 2) ≤
            κ * (R.ρβ q.2 * M ^ 2) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hsq (hρβ0 _)) hκ
        _ = _ := by ring
    · simp only [env, V, b, if_neg hq, indicator_of_notMem hq, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero, zero_mul, le_refl]
  have hbound : ∀ q, ‖movingNoiseKernel R 0 r g q‖ ^ 2 ≤ env q := by
    intro q
    by_cases hq : q.1 ∈ Icc (0 : ℝ) r
    · have hρ0 := ((R.resulting.global r).density q.1 hq).nonneg q.2
      simp only [movingNoiseKernel, if_pos hq, r26t3_U, heq q.1 hq,
        env, V, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
        Real.sq_sqrt hβ, Real.sq_sqrt hρ0]
      calc
        (2 * p.β⁻¹ * R.ρ q.1 q.2) * ‖gradient (u q.1) q.2‖ ^ 2 ≤
            (2 * p.β⁻¹ * (p.C₁ * R.ρβ q.2)) * ‖gradient (u q.1) q.2‖ ^ 2 :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (R.resulting.ratio q.1 hq.1 q.2).2 hβ)
            (sq_nonneg _)
        _ = _ := by dsimp [κ]; ring
    · simp only [movingNoiseKernel, env, V, if_neg hq, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero, le_refl]
  have hsq : Integrable (fun q => ‖movingNoiseKernel R 0 r g q‖ ^ 2) μ := by
    apply hei.mono' (hkm.norm.pow_const 2).aestronglyMeasurable
    filter_upwards with q
    simpa only [Real.norm_of_nonneg (sq_nonneg _)] using hbound q
  have hmem : MemLp (movingNoiseKernel R 0 r g) 2 μ :=
    (memLp_two_iff_integrable_sq_norm hkm.aestronglyMeasurable).2 hsq
  refine ⟨hmem, ?_⟩
  have hn : ‖movingNoiseFeature R 0 r g‖ ^ 2 =
      ∫ q, ‖movingNoiseKernel R 0 r g q‖ ^ 2 ∂μ := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    have hae : (movingNoiseFeature R 0 r g : ℝ × Euc p.d → Euc p.d)
        =ᵐ[μ] movingNoiseKernel R 0 r g := by
      rw [movingNoiseFeature, dif_pos hmem]
      exact hmem.coeFn_toLp
    filter_upwards [hae] with q hq
    rw [hq, real_inner_self_eq_norm_sq]
  have hrow : ∀ s, (∫ x, env (s, x)) =
      (Icc (0 : ℝ) r).indicator
        (fun s => κ * ∫ x, ‖gradient (u s) x‖ ^ 2 ∂(HRS.Whole.withDensityReal R.ρβ)) s := by
    intro s
    by_cases hs : s ∈ Icc (0 : ℝ) r
    · simp only [env, V, if_pos hs, indicator_of_mem hs, integral_const_mul]
      rw [HRS.MP.RdRem.mrr_integral_withDensityReal R.ρβ hρβ hρβ0]
    · simp only [env, V, Prod.fst, Prod.snd, if_neg hs, indicator_of_notMem hs, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero, integral_zero]
  calc
    ‖movingNoiseFeature R 0 r g‖ ^ 2 = _ := hn
    _ ≤ ∫ q, env q ∂μ := integral_mono hsq hei hbound
    _ = ∫ s, ∫ x, env (s, x) := integral_prod _ hei
    _ = ∫ s in Icc (0 : ℝ) r,
          κ * ∫ x, ‖gradient (u s) x‖ ^ 2 ∂(HRS.Whole.withDensityReal R.ρβ) := by
      simp_rw [hrow]
      exact integral_indicator measurableSet_Icc
    _ = _ := integral_const_mul _ _

#print axioms fp81s21_feature_measure_domination
#print axioms fp81s21_feature_variance_domination
#print axioms fp81s21_feature_classical_eq
#print axioms fp81s21_feature_classical_noise
end HRS.Fp81.S21
end
