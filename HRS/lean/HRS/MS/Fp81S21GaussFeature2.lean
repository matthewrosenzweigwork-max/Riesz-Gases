import HRS.MS.Fp81S21GaussFeature
import HRS.MS.Fp81S21Uniform3
import HRS.MS.Fp81S21MovingInputs2

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory Set Classical
open scoped ENNReal NNReal BigOperators RealInnerProductSpace

namespace HRS.Fp81.S21

open HRS (Euc)
open HRS.Whole
open HRS.MS.R26T3
open HRS.MS.S111X2

private theorem fp81s21_gaussFeature_oscNorm_l2_sq_le
    {d : ℕ} {m : ℝ} (hm : 0 ≤ m) {φ : Euc d → ℝ}
    (hφ : IsOscTest m φ) :
    ∫ x, φ x ^ 2 ≤ oscNorm m φ ^ 2 := by
  have hmono := HRS.MS.MovOsc.mo_mono (r := (0 : ℝ)) (r' := m) hm hφ.2
  have hI0 : 0 ≤ ∫ x, φ x ^ 2 := integral_nonneg fun x => sq_nonneg _
  have hnorm := HRS.Whole.oscNorm_zero φ hmono.1.1
  have hIeq : ∫ x, φ x ^ 2 = oscNorm 0 φ ^ 2 := by
    rw [hnorm, Real.sq_sqrt hI0]
  rw [hIeq]
  exact (sq_le_sq₀ (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)).2 hmono.2

private theorem fp81s21_gaussFeature_density_l2_bound
    (p : Parameters) {δ H : ℝ} (R : Trajectory p δ)
    {C₀ c₀ : ℝ} (hC₀ : 0 ≤ C₀) (hc₀ : 0 < c₀)
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
  have hmajor : Integrable (fun x => C₀ * φ x ^ 2)
      (volume : Measure (Euc p.d)) := hφsq.const_mul C₀
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
    fp81s21_gaussFeature_oscNorm_l2_sq_le (by positivity) hφ
  calc
    ∫ x, φ x ^ 2 ∂(r26t3_mu R t) = ∫ x, ρ x * φ x ^ 2 := by
      simpa [ρ, r26t3_mu] using
        HRS.MP.RdRem.mrr_integral_withDensityReal (R.ρ t) hρmeas hρnn
          (fun x => φ x ^ 2)
    _ ≤ ∫ x, C₀ * φ x ^ 2 := hprod
    _ = C₀ * ∫ x, φ x ^ 2 := by rw [integral_const_mul]
    _ ≤ C₀ * oscNorm (wholeSpaceIndex p.d : ℝ) φ ^ 2 :=
      mul_le_mul_of_nonneg_left hvol hC₀

/-- The combined initial and noise feature has a uniform oscillator envelope
on every finite horizon.  The constant is selected after the trajectory and
horizon. -/
theorem fp81s21_combinedFeature_horizon_bound (p : Parameters) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ,
        ∀ (hμ₀ : IsProbabilityMeasure (r26t3_mu R 0)),
        ∀ H : ℝ, 0 < H →
          ∃ B : ℝ, 0 ≤ B ∧
            ∀ (Mg : ℝ)
              (K : Lp ℝ 2 (r26t3_mu R 0) →L[ℝ] Lp ℝ 2 (r26t3_mu R 0)),
            (hK : KRep (rieszKernel p.d p.s) (r26t3_mu R 0) K Mg) →
            ∀ t ∈ Icc (0 : ℝ) H,
            ∀ φ : Euc p.d → ℝ,
              IsOscTest (wholeSpaceIndex p.d : ℝ) φ →
              ‖@fp81s21_combinedFeature p δ R hμ₀ Mg K hK t φ‖ ≤
                B * oscNorm (wholeSpaceIndex p.d : ℝ) φ := by
  obtain ⟨δcov, hδcov, hδcovhalf, hcov⟩ :=
    fp81s21_uniform_covariance_domination p
  obtain ⟨δmove, -, -, hδmove, hδmovehalf, -, hfields⟩ :=
    fp81s21_moving_trajectory_fields p
  let δ0 : ℝ := min δcov δmove
  have hδ0 : 0 < δ0 := lt_min hδcov hδmove
  have hδ0half : δ0 ≤ 1 / 2 :=
    le_trans (min_le_left _ _) hδcovhalf
  refine ⟨δ0, hδ0, hδ0half, ?_⟩
  intro δ hδ hδδ0 R hμ₀ H hH
  have hδcov' : δ ≤ δcov := hδδ0.trans (min_le_left _ _)
  have hδmove' : δ ≤ δmove := hδδ0.trans (min_le_right _ _)
  have hδhalf : δ ≤ 1 / 2 := hδδ0.trans hδ0half
  obtain ⟨Kcov, hKcov, hcovR⟩ := hcov δ hδ hδcov' R
  rcases hfields δ hδ hδmove' R H hH with
    ⟨-, -, -, -, -, -, -, ⟨C₀, c₀, hc₀, hupper⟩, -⟩
  have hρ0 := (R.resulting.global H).density 0 ⟨le_rfl, hH.le⟩
  have hC₀ : 0 ≤ C₀ := by
    have hnn := hρ0.nonneg (0 : Euc p.d)
    have hup := hupper 0 ⟨le_rfl, hH.le⟩ (0 : Euc p.d)
    simpa using hnn.trans hup
  let B : ℝ := Real.sqrt (Kcov * C₀)
  have hB : 0 ≤ B := Real.sqrt_nonneg _
  refine ⟨B, hB, ?_⟩
  intro Mg K hK t ht φ hφ
  letI : IsProbabilityMeasure (r26t3_mu R 0) := hμ₀
  have hgram := fp81s21_combinedFeature_gram p hδ hδhalf R hK
    ht.1 ht.1 hφ hφ
  have hcovupper :
      HRS.MS.S21E.s21eCov p.d p.s p.a p.β p.γ R.ρ t t φ φ ≤
        Kcov * ∫ x, φ x ^ 2 ∂(r26t3_mu R t) := by
    have hraw := hcovR t t ht.1 ht.1 φ φ hφ hφ
    have hraw' :
        |HRS.MS.S21E.s21eCov p.d p.s p.a p.β p.γ R.ρ t t φ φ| ≤
          Kcov * Real.sqrt (∫ x, φ x ^ 2 ∂(r26t3_mu R t)) *
            Real.sqrt (∫ x, φ x ^ 2 ∂(r26t3_mu R t)) := by
      simpa only [r26t3_mu] using hraw
    have hI : 0 ≤ ∫ x, φ x ^ 2 ∂(r26t3_mu R t) :=
      integral_nonneg fun x => sq_nonneg _
    have hroot :
        Real.sqrt (∫ x, φ x ^ 2 ∂(r26t3_mu R t)) *
          Real.sqrt (∫ x, φ x ^ 2 ∂(r26t3_mu R t)) =
            ∫ x, φ x ^ 2 ∂(r26t3_mu R t) := by
      calc
        _ = (Real.sqrt (∫ x, φ x ^ 2 ∂(r26t3_mu R t))) ^ 2 := by ring
        _ = _ := Real.sq_sqrt hI
    calc
      _ ≤ |HRS.MS.S21E.s21eCov p.d p.s p.a p.β p.γ R.ρ t t φ φ| := le_abs_self _
      _ ≤ Kcov * Real.sqrt (∫ x, φ x ^ 2 ∂(r26t3_mu R t)) *
            Real.sqrt (∫ x, φ x ^ 2 ∂(r26t3_mu R t)) := hraw'
      _ = Kcov * (Real.sqrt (∫ x, φ x ^ 2 ∂(r26t3_mu R t)) *
            Real.sqrt (∫ x, φ x ^ 2 ∂(r26t3_mu R t))) := by ring
      _ = Kcov * ∫ x, φ x ^ 2 ∂(r26t3_mu R t) := by rw [hroot]
  have hden := fp81s21_gaussFeature_density_l2_bound p R
    hC₀ hc₀ hupper ht hφ
  have hcovBound :
      HRS.MS.S21E.s21eCov p.d p.s p.a p.β p.γ R.ρ t t φ φ ≤
        Kcov * C₀ * oscNorm (wholeSpaceIndex p.d : ℝ) φ ^ 2 := by
    calc
      _ ≤ Kcov * ∫ x, φ x ^ 2 ∂(r26t3_mu R t) := hcovupper
      _ ≤ Kcov * (C₀ * oscNorm (wholeSpaceIndex p.d : ℝ) φ ^ 2) :=
        mul_le_mul_of_nonneg_left hden hKcov
      _ = Kcov * C₀ * oscNorm (wholeSpaceIndex p.d : ℝ) φ ^ 2 := by ring
  have hnormSq :
      ‖fp81s21_combinedFeature p R hK t φ‖ ^ 2 =
        HRS.MS.S21E.s21eCov p.d p.s p.a p.β p.γ R.ρ t t φ φ := by
    have hself := real_inner_self_eq_norm_sq
        (fp81s21_combinedFeature p R hK t φ)
    rw [← hself, hgram]
  have htarget0 : 0 ≤ B * oscNorm (wholeSpaceIndex p.d : ℝ) φ :=
    mul_nonneg hB (Real.sqrt_nonneg _)
  have htargetSq :
      (B * oscNorm (wholeSpaceIndex p.d : ℝ) φ) ^ 2 =
        Kcov * C₀ * oscNorm (wholeSpaceIndex p.d : ℝ) φ ^ 2 := by
    dsimp [B]
    rw [mul_pow, Real.sq_sqrt (mul_nonneg hKcov hC₀)]
  apply (sq_le_sq₀ (norm_nonneg _) htarget0).mp
  rw [hnormSq]
  exact hcovBound.trans_eq htargetSq.symm

#print axioms fp81s21_combinedFeature_horizon_bound

end HRS.Fp81.S21

end
