import HRS.MS.Fp81S21GaussianSourceSpaceUncond
import HRS.MS.Fp81S21OscTestDense
import HRS.MS.ThmConsAux1
import HRS.MS.LogBnd

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.R26T3 HRS.MC.QRSpec.Wick

private theorem fp81s21_gaussianSourceSpace_thermal_gaussian_upper
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ) :
    ∃ C c : ℝ, 0 < c ∧ ∀ x,
      R.ρβ x ≤ C * Real.exp (-c * ‖x‖ ^ 2) := by
  have hsd : p.s < (p.d : ℝ) := by linarith [p.hs]
  have hρeq : R.ρβ = HRS.Whole.thermalDensity p.d p.s p.a p.β :=
    HRS.MS.Mov0.mv0_rho_eq p.hd p.hs0 hsd p.ha p.hβ R.thermal
  by_cases hs0 : p.s = 0
  · obtain ⟨_, _, C, hthermal⟩ :=
      HRS.MS.Thm.logThermal_bounds_proof p.hd p.a p.β p.ha p.hβ
    have hρeq0 : R.ρβ = HRS.Whole.thermalDensity p.d 0 p.a p.β := by
      simpa [hs0] using hρeq
    let A : ℝ := Real.exp (p.β * (p.a / 2 - 1 - Real.log (p.a / 2)) / 2)
    have hC : 0 ≤ C := by
      have hρ0 : 0 ≤ HRS.Whole.thermalDensity p.d 0 p.a p.β 0 := by
        rw [← hρeq0]
        exact R.thermal.2.1.nonneg 0
      have hupper0 : HRS.Whole.thermalDensity p.d 0 p.a p.β 0 ≤ C := by
        simpa using (hthermal 0).2
      exact hρ0.trans hupper0
    refine ⟨C * A, p.β * p.a / 4,
      div_pos (mul_pos p.hβ p.ha) (by norm_num), ?_⟩
    intro x
    have hxpos : 0 < (1 + ‖x‖ ^ 2 : ℝ) := by positivity
    have hpoly :
        (1 + ‖x‖ ^ 2) ^ (p.β / 2) * Real.exp (-p.β * p.a * ‖x‖ ^ 2 / 2) =
          HRS.MS.Thm.t67w p.a p.β x := by
      calc
        _ = Real.exp (p.β / 2 * Real.log (1 + ‖x‖ ^ 2)) *
              Real.exp (-p.β * p.a * ‖x‖ ^ 2 / 2) := by
                rw [Real.rpow_def_of_pos hxpos]
                rw [← Real.exp_add, ← Real.exp_add]
                congr 1
                ring
        _ = Real.exp (p.β / 2 * Real.log (1 + ‖x‖ ^ 2) +
              (-p.β * p.a * ‖x‖ ^ 2 / 2)) := by rw [← Real.exp_add]
        _ = HRS.MS.Thm.t67w p.a p.β x := by
              unfold HRS.MS.Thm.t67w HRS.MS.Thm.t67l HRS.Whole.confinement
              congr 1
              ring
    have hdecay := HRS.MS.Thm.t67w_le p.ha p.hβ x
    rw [hρeq0]
    calc
      HRS.Whole.thermalDensity p.d 0 p.a p.β x ≤
          C * ((1 + ‖x‖ ^ 2) ^ (p.β / 2) *
            Real.exp (-p.β * p.a * ‖x‖ ^ 2 / 2)) := by
              simpa [mul_assoc] using (hthermal x).2
      _ = C * HRS.MS.Thm.t67w p.a p.β x := by rw [hpoly]
      _ ≤ C * (A * Real.exp (-(p.β * p.a / 4) * ‖x‖ ^ 2)) :=
            mul_le_mul_of_nonneg_left hdecay hC
      _ = C * A * Real.exp (-(p.β * p.a / 4) * ‖x‖ ^ 2) := by ring
  · have hspos : 0 < p.s := lt_of_le_of_ne p.hs0 (Ne.symm hs0)
    have hd1 : 1 ≤ p.d := le_trans (by norm_num) p.hd
    obtain ⟨_, c₀, C, hc₀, _, hthermal⟩ :=
      HRS.MS.Thm.cb_thermal_two_sided hd1 hspos hsd p.ha p.hβ
    let A : ℝ := (p.β * p.a / (2 * Real.pi)) ^ ((p.d : ℝ) / 2)
    refine ⟨C * A, p.β * p.a / 2,
      div_pos (mul_pos p.hβ p.ha) (by norm_num), ?_⟩
    intro x
    rw [hρeq]
    have hcmp : HRS.Whole.gaussianComparison p.d p.a p.β x =
        A * Real.exp (-(p.β * p.a / 2) * ‖x‖ ^ 2) := by
      unfold HRS.Whole.gaussianComparison
      dsimp [A]
      congr 1
      congr 1
      ring
    calc
      HRS.Whole.thermalDensity p.d p.s p.a p.β x ≤
          C * HRS.Whole.gaussianComparison p.d p.a p.β x := (hthermal x).2
      _ = C * (A * Real.exp (-(p.β * p.a / 2) * ‖x‖ ^ 2)) := by rw [hcmp]
      _ = C * A * Real.exp (-(p.β * p.a / 2) * ‖x‖ ^ 2) := by ring

/-- Oscillator tests are dense in the thermal reference `L²` space. -/
theorem fp81s21_gaussianSourceSpace_oscTest_dense
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ) :
    Dense (Set.range (fp81s21_gaussianSourceSpace_oscTestLp p R)) := by
  obtain ⟨C₀, c, hc, hupper⟩ :=
    fp81s21_gaussianSourceSpace_thermal_gaussian_upper p R
  let C : ℝ≥0∞ := ENNReal.ofReal C₀
  have hC : C ≠ ∞ := ENNReal.ofReal_ne_top
  let μ : Measure (Euc p.d) := HRS.Whole.withDensityReal R.ρβ
  have hμprob : IsProbabilityMeasure μ :=
    HRS.Whole.Q34.isProbabilityMeasure_nu R.thermal.1.1
  letI : IsProbabilityMeasure μ := hμprob
  have hμ : μ ≤
      C • (volume : Measure (Euc p.d)) := by
    simpa [C, μ] using
      fp81s21_withDensityReal_le_smul_volume_of_gaussian_upper
        (fun x => R.thermal.1.1.nonneg x) hc hupper
  have hdense := fp81s21_oscTest_toLp_denseRange C hC hμ
  have heq : fp81s21_gaussianSourceSpace_oscTestLp p R =
      fp81s21_oscTest_toLp (HRS.Whole.withDensityReal R.ρβ) C hC hμ := by
    funext φ
    apply Lp.ext
    have h₁ := (fp81s21_gaussianSourceSpace_oscTest_memLp p R φ).coeFn_toLp
    have h₂ := (φ.2.2.1.of_measure_le_smul hC hμ).coeFn_toLp
    filter_upwards [h₁, h₂] with x hx₁ hx₂
    exact hx₁.trans hx₂.symm
  change DenseRange (fp81s21_gaussianSourceSpace_oscTestLp p R)
  rw [heq]
  exact hdense

/-- The unconditional retained-source conclusion, with oscillator-test density discharged
from the thermal Gaussian envelope. -/
theorem fp81s21_gaussianSourceSpace_unconditional_dense (p : Parameters) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → ∀ R : Trajectory p δ,
        ∀ hμ₀ : IsProbabilityMeasure (r26t3_mu R 0),
          ∀ D : fp81s21_gaussian_source_retained_data p R hμ₀,
            ∃ T : ℝ → (
              Lp ℝ 2 (HRS.Whole.withDensityReal R.ρβ) →L[ℝ]
                Lp ℝ 2 D.G0.P),
            ∃ ξ' : ℕ → D.G0.Ω → ℝ,
            ∃ 𝒢 : Submodule ℝ (D.G0.Ω → ℝ),
              QrpwG4 D.G0.P 𝒢 ∧
              (∀ i, ξ' i ∈ 𝒢) ∧
              (∀ u : ℝ, 0 ≤ u → ∀ f : Lp ℝ 2
                (HRS.Whole.withDensityReal R.ρβ),
                  (T u f : D.G0.Ω → ℝ) ∈ 𝒢) ∧
              (∀ u : ℝ, 0 ≤ u → ∀ φ : fp81s21_oscTest p.d,
                (fun ω => OscDual.eval (D.G0.Z u ω) φ.1) ∈ 𝒢) := by
  obtain ⟨δ₀, hδ₀, hδ₀half, hbase⟩ :=
    fp81s21_gaussianSourceSpace_unconditional p
  refine ⟨δ₀, hδ₀, hδ₀half, ?_⟩
  intro δ hδ hδle R hμ₀ D
  exact hbase δ hδ hδle R hμ₀ D
    (fp81s21_gaussianSourceSpace_oscTest_dense p R)

#print axioms fp81s21_gaussianSourceSpace_oscTest_dense
#print axioms fp81s21_gaussianSourceSpace_unconditional_dense

end HRS.Fp81.S21
end
