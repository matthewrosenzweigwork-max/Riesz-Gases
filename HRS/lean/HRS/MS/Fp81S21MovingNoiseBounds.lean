import HRS.MS.Fp81S21MovingNoise
import HRS.MS.Fp81S21Uniform3
import HRS.MS.Fp81S21MovingInputs2
import HRS.MS.S21H2_S14aD5
import HRS.MS.S111X2Aux4
import HRS.MS.MovOscAux5

/-!
# HRS S2.1(iii), SOL39 packet 2: moving noise feature bounds

The consumer `gaussian_paths_of_linear_features` requires, for each side and
each time, an all-oscillator bound on the linear feature map in `oscNorm`,
square summability of its Hermite coordinate norms, and a square-summable
terminal-time increment estimate with one nonnegative constant independent of
the cutoff and both terminal times.  Packet 2 supplies the all-test operator
bound here; the coordinate estimates are in the following packet file.

The constructor's precise inputs (from
`ProClosureS111GaussianLaw.gaussian_paths_of_linear_features`) are:

* `hG`: for each of the two sides and every time in `[0,H]`, there is a
  nonnegative operator bound `B` valid for every `phi : oscSub d m`, namely
  `‖G i t phi‖ ≤ B * oscNorm m (phi : Euc d → ℝ)`;
* `hF`: at each side and time, the squared norms of all Hermite-coordinate
  features are summable;
* `hinc`: one nonnegative `L`, chosen before the side and times, bounds the
  sum of squared Hermite-coordinate increments by `L * |t-v|`, and each
  increment family is summable.

The raw moving feature accepts arbitrary functions, so its oscillator-test
bound below directly supplies the operator estimate used to package `hG`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory Filter Topology Set Classical
open scoped ENNReal NNReal BigOperators RealInnerProductSpace

namespace HRS.Fp81.S21

open HRS (Euc)
open HRS.Whole
open HRS.MS.R26T3

private theorem fp81s21_movingInitialCov_nonneg
    (p : Parameters) {δ : ℝ} (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2)
    (R : Trajectory p δ) (f : Euc p.d → ℝ)
    (hf : MemLp f 2 (r26t3_mu R 0)) :
    0 ≤ HRS.Whole.susceptibilityCov (rieszKernel p.d p.s)
      (r26t3_mu R 0) p.γ f f := by
  let μ₀ : Measure (Euc p.d) := r26t3_mu R 0
  have hμ₀ : IsProbabilityMeasure μ₀ := by
    change IsProbabilityMeasure (HRS.Whole.withDensityReal (R.ρ 0))
    exact HRS.Whole.Q34.isProbabilityMeasure_nu
      (R.resulting.global 0 |>.density 0 ⟨le_rfl, le_rfl⟩)
  letI : IsProbabilityMeasure μ₀ := hμ₀
  obtain ⟨Mg, K, hK⟩ := HRS.MS.R26T3.s21h2_krep_init hδ hδhalf R
  have hform := HRS.MS.S111X2.s111x2_responseForm
    (g := rieszKernel p.d p.s) hK p.hγ le_rfl
  have hMg : 0 ≤ Mg := hK.nonneg
  have hden : 0 < 1 + p.γ * Mg := by
    have hprod : 0 ≤ p.γ * Mg := mul_nonneg p.hγ hMg
    linarith
  have hη : 0 ≤ (1 + p.γ * Mg)⁻¹ := inv_nonneg.mpr hden.le
  have hvar : 0 ≤ HRS.MS.S111X2.s111x2_centeredSquare μ₀ f := by
    unfold HRS.MS.S111X2.s111x2_centeredSquare
    exact integral_nonneg fun x => sq_nonneg _
  have hcoercive := hform.coercive f hf
  change 0 ≤ HRS.Whole.susceptibilityCov (rieszKernel p.d p.s) μ₀ p.γ f f
  exact (mul_nonneg hη hvar).trans hcoercive.1

/-- Restricting the forcing interval cannot increase the feature norm. -/
private theorem fp81s21_movingNoiseFeature_norm_le_zero
    (p : Parameters) {δ H : ℝ} (R : Trajectory p δ)
    (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2) (hH : 0 < H)
    {u t : ℝ} (hu : u ∈ Icc (0 : ℝ) H) (ht : t ∈ Icc (0 : ℝ) H)
    {φ : Euc p.d → ℝ}
    (hφ : IsOscTest (wholeSpaceIndex p.d : ℝ) φ) :
    ‖movingNoiseFeature R u t φ‖ ≤ ‖movingNoiseFeature R 0 t φ‖ := by
  let μ : Measure (ℝ × Euc p.d) :=
    (volume : Measure ℝ).prod (volume : Measure (Euc p.d))
  let f := movingNoiseKernel R u t φ
  let g := movingNoiseKernel R 0 t φ
  have hmemF := (movingNoiseFeature_spec p R hδ hδhalf hH).1 u hu t ht φ hφ
  have hmemG := (movingNoiseFeature_spec p R hδ hδhalf hH).1 0
    ⟨le_rfl, hH.le⟩ t ht φ hφ
  have hpoint : ∀ q : ℝ × Euc p.d, ‖f q‖ ≤ ‖g q‖ := by
    intro q
    by_cases hq : q.1 ∈ Icc u t
    · have hq0 : q.1 ∈ Icc (0 : ℝ) t := ⟨hu.1.trans hq.1, hq.2⟩
      simp [f, g, movingNoiseKernel, hq, hq0]
    · by_cases hq0 : q.1 ∈ Icc (0 : ℝ) t
      · simp [f, g, movingNoiseKernel, hq, hq0]
      · simp [f, g, movingNoiseKernel, hq, hq0]
  have hLp : eLpNorm f 2 μ ≤ eLpNorm g 2 μ :=
    eLpNorm_mono_ae hmemF.aestronglyMeasurable
      (Filter.Eventually.of_forall hpoint)
  have hnormF : ‖movingNoiseFeature R u t φ‖ = (eLpNorm f 2 μ).toReal := by
    rw [movingNoiseFeature, dif_pos hmemF, Lp.norm_toLp]
  have hnormG : ‖movingNoiseFeature R 0 t φ‖ = (eLpNorm g 2 μ).toReal := by
    rw [movingNoiseFeature, dif_pos hmemG, Lp.norm_toLp]
  rw [hnormF, hnormG]
  exact ENNReal.toReal_mono hmemG.eLpNorm_ne_top hLp

private theorem fp81s21_oscNorm_l2_sq_le
    {d : ℕ} {m : ℝ} (hm : 0 ≤ m) {φ : Euc d → ℝ}
    (hφ : IsOscTest m φ) :
    ∫ x, φ x ^ 2 ≤ oscNorm m φ ^ 2 := by
  have hmono := HRS.MS.MovOsc.mo_mono (r := (0 : ℝ)) (r' := m)
    hm hφ.2
  have hI0 : 0 ≤ ∫ x, φ x ^ 2 := integral_nonneg fun x => sq_nonneg _
  have hnorm := HRS.Whole.oscNorm_zero φ hmono.1.1
  have hIeq : ∫ x, φ x ^ 2 = oscNorm 0 φ ^ 2 := by
    rw [hnorm, Real.sq_sqrt hI0]
  rw [hIeq]
  exact (sq_le_sq₀ (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)).2 hmono.2

private theorem fp81s21_moving_density_l2_bound
    (p : Parameters) {δ H : ℝ} (R : Trajectory p δ)
    (hH : 0 < H) {C₀ c₀ : ℝ} (hC₀ : 0 ≤ C₀) (hc₀ : 0 < c₀)
    (hupper : ∀ u ∈ Icc (0 : ℝ) H, ∀ x,
      R.ρ u x ≤ C₀ * Real.exp (-c₀ * ‖x‖ ^ 2))
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) H)
    {φ : Euc p.d → ℝ}
    (hφ : IsOscTest (wholeSpaceIndex p.d : ℝ) φ) :
    ∫ x, φ x ^ 2 ∂(r26t3_mu R t) ≤
      C₀ * oscNorm (wholeSpaceIndex p.d : ℝ) φ ^ 2 := by
  let ρ : Euc p.d → ℝ := R.ρ t
  have hρprob := (R.resulting.global H).density t ht
  have hρmeas : Measurable ρ := by simpa [ρ] using hρprob.measurable
  have hρnn : ∀ x, 0 ≤ ρ x := by simpa [ρ] using hρprob.nonneg
  have hρbound : ∀ x, ρ x ≤ C₀ := by
    intro x
    have hexp : Real.exp (-c₀ * ‖x‖ ^ 2) ≤ 1 := by
      apply Real.exp_le_one_iff.mpr
      nlinarith [sq_nonneg (‖x‖ : ℝ)]
    calc
      ρ x ≤ C₀ * Real.exp (-c₀ * ‖x‖ ^ 2) := by
        simpa [ρ] using hupper t ht x
      _ ≤ C₀ := by
        exact (mul_le_mul_of_nonneg_left hexp hC₀).trans_eq (mul_one C₀)
  have hmemL2 : MemLp φ 2 (volume : Measure (Euc p.d)) := hφ.2.1
  have hφsq : Integrable (fun x => φ x ^ 2) (volume : Measure (Euc p.d)) := by
    simpa [Real.norm_eq_abs, sq_abs] using hmemL2.integrable_sq
  have hmajor : Integrable (fun x => C₀ * φ x ^ 2) (volume : Measure (Euc p.d)) :=
    hφsq.const_mul C₀
  have htargetMeas : AEStronglyMeasurable
      (fun x => ρ x * φ x ^ 2) (volume : Measure (Euc p.d)) :=
    (hρmeas.mul (hφ.1.continuous.measurable.pow_const 2)).aestronglyMeasurable
  have htarget : Integrable (fun x => ρ x * φ x ^ 2)
      (volume : Measure (Euc p.d)) := by
    apply hmajor.mono' htargetMeas
    filter_upwards with x
    have hleft : 0 ≤ ρ x * φ x ^ 2 := mul_nonneg (hρnn x) (sq_nonneg _)
    change ‖ρ x * φ x ^ 2‖ ≤ C₀ * φ x ^ 2
    rw [Real.norm_of_nonneg hleft]
    exact mul_le_mul_of_nonneg_right (hρbound x) (sq_nonneg _)
  have hprod : ∫ x, ρ x * φ x ^ 2 ≤ ∫ x, C₀ * φ x ^ 2 :=
    integral_mono htarget hmajor fun x =>
      mul_le_mul_of_nonneg_right (hρbound x) (sq_nonneg _)
  have hvol : ∫ x, φ x ^ 2 ≤ oscNorm (wholeSpaceIndex p.d : ℝ) φ ^ 2 :=
    fp81s21_oscNorm_l2_sq_le (by positivity) hφ
  calc
    ∫ x, φ x ^ 2 ∂(r26t3_mu R t) = ∫ x, ρ x * φ x ^ 2 := by
      simpa [ρ, r26t3_mu] using
        HRS.MP.RdRem.mrr_integral_withDensityReal (R.ρ t) hρmeas hρnn
          (fun x => φ x ^ 2)
    _ ≤ ∫ x, C₀ * φ x ^ 2 := hprod
    _ = C₀ * ∫ x, φ x ^ 2 := by rw [integral_const_mul]
    _ ≤ C₀ * oscNorm (wholeSpaceIndex p.d : ℝ) φ ^ 2 :=
      mul_le_mul_of_nonneg_left hvol hC₀

private theorem fp81s21_movingNoise_full_sq_bound
    (p : Parameters) {δ H : ℝ} (R : Trajectory p δ)
    (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2) (hH : 0 < H)
    {Kcov C₀ c₀ : ℝ} (hKcov : 0 ≤ Kcov) (hC₀ : 0 ≤ C₀)
    (hc₀ : 0 < c₀)
    (hcov : ∀ r t : ℝ, 0 ≤ r → 0 ≤ t →
      ∀ ψ φ : Euc p.d → ℝ,
        IsOscTest (wholeSpaceIndex p.d : ℝ) ψ →
        IsOscTest (wholeSpaceIndex p.d : ℝ) φ →
        |HRS.MS.S21E.s21eCov p.d p.s p.a p.β p.γ R.ρ r t ψ φ| ≤
          Kcov * Real.sqrt (∫ x, φ x ^ 2 ∂(r26t3_mu R t)) *
            Real.sqrt (∫ x, ψ x ^ 2 ∂(r26t3_mu R r)))
    (hupper : ∀ u ∈ Icc (0 : ℝ) H, ∀ x,
      R.ρ u x ≤ C₀ * Real.exp (-c₀ * ‖x‖ ^ 2))
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) H)
    {φ : Euc p.d → ℝ}
    (hφ : IsOscTest (wholeSpaceIndex p.d : ℝ) φ) :
    ‖movingNoiseFeature R 0 t φ‖ ^ 2 ≤
      Kcov * C₀ * oscNorm (wholeSpaceIndex p.d : ℝ) φ ^ 2 := by
  let μ₀ : Measure (Euc p.d) := r26t3_mu R 0
  have hμ₀ : IsProbabilityMeasure μ₀ := by
    change IsProbabilityMeasure (HRS.Whole.withDensityReal (R.ρ 0))
    exact HRS.Whole.Q34.isProbabilityMeasure_nu
      ((R.resulting.global H).density 0 ⟨le_rfl, hH.le⟩)
  letI : IsProbabilityMeasure μ₀ := hμ₀
  have hclass := fp81s21_U_osc_test_classical p R hφ ht.1
  have hmemU : MemLp (r26t3_U R 0 t φ) 2 μ₀ := by
    exact HRS.MS.S111X1.x1_classical_memLp hclass ⟨le_rfl, ht.1⟩ μ₀
  have hinit := fp81s21_movingInitialCov_nonneg p hδ hδhalf R
    (r26t3_U R 0 t φ) hmemU
  have hρcoeff : (r26t3_coeff R).ρ = R.ρ := rfl
  have hgram := (movingNoiseFeature_spec p R hδ hδhalf hH).2
    0 ⟨le_rfl, hH.le⟩ t ht t ht φ φ hφ hφ
  have hnoiseeq :
      inner ℝ (movingNoiseFeature R 0 t φ) (movingNoiseFeature R 0 t φ) =
        noiseCovW (r26t3_coeff R) p.β⁻¹ t t φ φ := by
    simpa [HRS.Whole.noiseCovW, r26t3_U, hρcoeff] using hgram
  have hdecomp :
      HRS.MS.S21E.s21eCov p.d p.s p.a p.β p.γ R.ρ t t φ φ =
        HRS.Whole.susceptibilityCov (rieszKernel p.d p.s) μ₀ p.γ
            (r26t3_U R 0 t φ) (r26t3_U R 0 t φ) +
          noiseCovW (r26t3_coeff R) p.β⁻¹ t t φ φ := by
    rfl
  have hnoiseNonneg : 0 ≤ noiseCovW (r26t3_coeff R) p.β⁻¹ t t φ φ := by
    rw [← hnoiseeq]
    exact real_inner_self_nonneg
  have hnoiseLeCov :
      noiseCovW (r26t3_coeff R) p.β⁻¹ t t φ φ ≤
        HRS.MS.S21E.s21eCov p.d p.s p.a p.β p.γ R.ρ t t φ φ := by
    rw [hdecomp]
    linarith
  have hcovraw := hcov t t ht.1 ht.1 φ φ hφ hφ
  have hI0 : 0 ≤ ∫ x, φ x ^ 2 ∂(r26t3_mu R t) :=
    integral_nonneg fun x => sq_nonneg _
  have hroot :
      Real.sqrt (∫ x, φ x ^ 2 ∂(r26t3_mu R t)) *
        Real.sqrt (∫ x, φ x ^ 2 ∂(r26t3_mu R t)) =
          ∫ x, φ x ^ 2 ∂(r26t3_mu R t) := by
    calc
      _ = (Real.sqrt (∫ x, φ x ^ 2 ∂(r26t3_mu R t))) ^ 2 := by ring
      _ = _ := Real.sq_sqrt hI0
  have hcovUpper :
      HRS.MS.S21E.s21eCov p.d p.s p.a p.β p.γ R.ρ t t φ φ ≤
        Kcov * (∫ x, φ x ^ 2 ∂(r26t3_mu R t)) := by
    calc
      _ ≤ |HRS.MS.S21E.s21eCov p.d p.s p.a p.β p.γ R.ρ t t φ φ| := le_abs_self _
      _ ≤ Kcov * Real.sqrt (∫ x, φ x ^ 2 ∂(r26t3_mu R t)) *
            Real.sqrt (∫ x, φ x ^ 2 ∂(r26t3_mu R t)) := by
          simpa using hcovraw
      _ = _ := by
          calc
            _ = Kcov * (Real.sqrt (∫ x, φ x ^ 2 ∂(r26t3_mu R t)) *
                Real.sqrt (∫ x, φ x ^ 2 ∂(r26t3_mu R t))) := by ring
            _ = _ := by rw [hroot]
  have hμbound := fp81s21_moving_density_l2_bound p R hH hC₀ hc₀
    hupper ht hφ
  have hnoiseNorm :
      ‖movingNoiseFeature R 0 t φ‖ ^ 2 =
        noiseCovW (r26t3_coeff R) p.β⁻¹ t t φ φ := by
    rw [real_inner_self_eq_norm_sq] at hnoiseeq
    exact hnoiseeq
  calc
    ‖movingNoiseFeature R 0 t φ‖ ^ 2 =
        noiseCovW (r26t3_coeff R) p.β⁻¹ t t φ φ := hnoiseNorm
    _ ≤ HRS.MS.S21E.s21eCov p.d p.s p.a p.β p.γ R.ρ t t φ φ := hnoiseLeCov
    _ ≤ Kcov * (∫ x, φ x ^ 2 ∂(r26t3_mu R t)) := hcovUpper
    _ ≤ Kcov * (C₀ * oscNorm (wholeSpaceIndex p.d : ℝ) φ ^ 2) :=
      mul_le_mul_of_nonneg_left hμbound hKcov
    _ = Kcov * C₀ * oscNorm (wholeSpaceIndex p.d : ℝ) φ ^ 2 := by ring

/-- An all-test operator bound in the oscillator norm, uniform over both
terminal time and forcing cutoff on each finite horizon. -/
theorem fp81s21_movingNoiseFeature_operator_bound (p : Parameters) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 →
      ∀ R : Trajectory p δ,
      ∀ H : ℝ, 0 < H →
        ∃ B : ℝ, 0 ≤ B ∧
          ∀ u ∈ Icc (0 : ℝ) H,
          ∀ t ∈ Icc (0 : ℝ) H,
          ∀ φ : Euc p.d → ℝ,
            IsOscTest (wholeSpaceIndex p.d : ℝ) φ →
            ‖movingNoiseFeature R u t φ‖ ≤
              B * oscNorm (wholeSpaceIndex p.d : ℝ) φ := by
  obtain ⟨δcov, hδcov, hδcovHalf, hcovRadius⟩ :=
    fp81s21_uniform_covariance_domination p
  obtain ⟨δmove, Co, co, hδmove, hδmoveHalf, hco, hfields⟩ :=
    fp81s21_moving_trajectory_fields p
  let δ0 : ℝ := min δcov δmove
  have hδ0 : 0 < δ0 := lt_min hδcov hδmove
  have hδ0Half : δ0 ≤ 1 / 2 := le_trans (min_le_left _ _) hδcovHalf
  refine ⟨δ0, hδ0, hδ0Half, ?_⟩
  intro δ hδ hδle R H hH
  have hδcov' : δ ≤ δcov := hδle.trans (min_le_left _ _)
  have hδmove' : δ ≤ δmove := hδle.trans (min_le_right _ _)
  obtain ⟨Kcov, hKcov, hcov⟩ := hcovRadius δ hδ hδcov' R
  rcases hfields δ hδ hδmove' R H hH with
    ⟨-, -, -, -, -, -, -, hgaussian, -⟩
  obtain ⟨C₀, c₀, hc₀, hupper⟩ := hgaussian
  have hρ0pos :=
    (HRS.MS.R26T3.r26t3_reference_data p δ hδ (hδle.trans hδ0Half) R).2.2.1
      0 le_rfl
  have hC₀pos : 0 < C₀ := by
    have hzero := hupper 0 ⟨le_rfl, hH.le⟩ 0
    have hpos := hρ0pos.2 0
    simpa using hpos.trans_le hzero
  let B : ℝ := Real.sqrt (Kcov * C₀)
  have hB : 0 ≤ B := Real.sqrt_nonneg _
  refine ⟨B, hB, ?_⟩
  intro u hu t ht φ hφ
  have hcut := fp81s21_movingNoiseFeature_norm_le_zero p R hδ
    (hδle.trans hδ0Half) hH hu ht hφ
  have hfullSq := fp81s21_movingNoise_full_sq_bound p R hδ
    (hδle.trans hδ0Half) hH hKcov hC₀pos.le hc₀ hcov hupper ht hφ
  have htarget0 : 0 ≤ B * oscNorm (wholeSpaceIndex p.d : ℝ) φ :=
    mul_nonneg hB (Real.sqrt_nonneg _)
  have htargetSq :
      (B * oscNorm (wholeSpaceIndex p.d : ℝ) φ) ^ 2 =
        Kcov * C₀ * oscNorm (wholeSpaceIndex p.d : ℝ) φ ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (mul_nonneg hKcov hC₀pos.le)]
  have hfull :
      ‖movingNoiseFeature R 0 t φ‖ ≤
        B * oscNorm (wholeSpaceIndex p.d : ℝ) φ := by
    exact (sq_le_sq₀ (norm_nonneg _) htarget0).mp (by rw [htargetSq]; exact hfullSq)
  exact hcut.trans hfull

#print axioms fp81s21_movingInitialCov_nonneg
#print axioms fp81s21_movingNoiseFeature_norm_le_zero
#print axioms fp81s21_oscNorm_l2_sq_le
#print axioms fp81s21_moving_density_l2_bound
#print axioms fp81s21_movingNoise_full_sq_bound
#print axioms fp81s21_movingNoiseFeature_operator_bound

end HRS.Fp81.S21

end
