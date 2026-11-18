import HRS.MS.Fp81S21GaussianSourceSpace
import HRS.MS.Fp81S21WickFam7
import HRS.MS.Fp81S21GaussianSourceGlue

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.S111X1 HRS.MC.QRSpec.Wick

/-- Every oscillator test is square integrable for the thermal reference
measure. -/
theorem fp81s21_gaussianSourceSpace_oscTest_memLp
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    (φ : fp81s21_oscTest p.d) :
    MemLp φ.1 2 (HRS.Whole.withDensityReal R.ρβ) := by
  have hsd : p.s < (p.d : ℝ) := by linarith [p.hs]
  have hρeq : R.ρβ = HRS.Whole.thermalDensity p.d p.s p.a p.β :=
    HRS.MS.Mov0.mv0_rho_eq p.hd p.hs0 hsd p.ha p.hβ R.thermal
  have hρmeas : Measurable R.ρβ := by
    obtain ⟨-, ψ, hψ⟩ := HRS.MS.S21.s21_schwartz_thermal
      p.hd p.hs0 hsd p.ha p.hβ
    rw [hρeq, ← hψ]
    exact ψ.continuous.measurable
  obtain ⟨M, hM, hthermal⟩ :=
    HRS.Fp81.S21.sol13_uniform_thermal_sup_bound p
  exact HRS.MS.S111X1.x1_osc_memLp hρmeas
    (fun x => (HRS.Whole.u4_thermal_pos R.thermal x).le)
    (hthermal δ R) φ.2

/-- The canonical map from oscillator tests into the thermal reference L²
space. -/
noncomputable def fp81s21_gaussianSourceSpace_oscTestLp
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ) :
    fp81s21_oscTest p.d →
      Lp ℝ 2 (HRS.Whole.withDensityReal R.ρβ) :=
  fun φ => (fp81s21_gaussianSourceSpace_oscTest_memLp p R φ).toLp φ.1

/-- Assemble a single fourth-moment Gaussian space on the retained source.
The oscillator-test image density is explicit input; the Wick-family theorem
supplies the bounded continuous operator on the very same retained `G0`. -/
theorem fp81s21_gaussianSourceSpace_unconditional (p : Parameters) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → ∀ R : Trajectory p δ,
        ∀ hμ₀ : IsProbabilityMeasure (r26t3_mu R 0),
          ∀ D : fp81s21_gaussian_source_retained_data p R hμ₀,
            Dense (Set.range (fp81s21_gaussianSourceSpace_oscTestLp p R)) →
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
  obtain ⟨δ₀, hδ₀, hδ₀half, hwick⟩ :=
    fp81s21_wickFam_supplied_linear_continuous p
  refine ⟨δ₀, hδ₀, hδ₀half, ?_⟩
  intro δ hδ hδle R hμ₀ D hφdense
  obtain ⟨Kstar, hKstar, hTfamily⟩ := hwick δ hδ hδle R
  obtain ⟨T, hT, hTcontinuous⟩ := hTfamily D.G0
  let ξ' : ℕ → D.G0.Ω → ℝ :=
    fp81s21_gaussian_source_measurableXi D
  obtain ⟨hξmeas, hξstd, _, hEvalFirst⟩ :=
    fp81s21_gaussian_source_measurable_eval_firstChaos D
  have hEvalL : ∀ u : ℝ, 0 ≤ u → ∀ φ : fp81s21_oscTest p.d,
      (T u (fp81s21_gaussianSourceSpace_oscTestLp p R φ) :
        D.G0.Ω → ℝ) =ᵐ[D.G0.P]
          (fun ω => OscDual.eval (D.G0.Z u ω) φ.1) := by
    intro u hu φ
    obtain ⟨hL, hJoint, hagree, _, _, _⟩ := hT u hu
    exact hagree φ.1 φ.2
      (fp81s21_gaussianSourceSpace_oscTest_memLp p R φ)
  obtain ⟨𝒢, hG4, hcoords, hLmem, hEvalMem⟩ :=
    fp81s21_gaussianSourceSpace_conditional R D.G0 ξ' hξstd hξmeas
      (HRS.Whole.withDensityReal R.ρβ)
      (fp81s21_gaussianSourceSpace_oscTestLp p R) hφdense T
      hEvalFirst hEvalL
  exact ⟨T, ξ', 𝒢, hG4, hcoords, hLmem, hEvalMem⟩

#print axioms fp81s21_gaussianSourceSpace_oscTest_memLp
#print axioms fp81s21_gaussianSourceSpace_unconditional

end HRS.Fp81.S21
end
