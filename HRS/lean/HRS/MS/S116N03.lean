import HRS.MS.S113EndAux31
import HRS.MS.S113EndAux6
import HRS.MS.R2MtAux1

/-!
# S11.6 packet N03 (`R26-T8B.N03`): small attractive normalizers with the exponential weights exported

Prefix `s116_`, namespace `HRS.MS.S116`.  Wrapper of the native `s113x_X4_generic` (for `s = 0`) for a probability density with a Gaussian upper envelope:
`a_*, B` depend only on `d, C_g, c_g`; for `θ ∈ [-a_*, 0]` and `N ≥ 2` the weight `exp(-θ N F_N)` is `μ^{⊗N}`-integrable (from `K_{N,θ} > 0`),
`K_{N,θ} > 0` and `|log K_{N,θ}| ≤ B`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory

namespace HRS.MS.S116

open HRS HRS.Whole

theorem s116_negative_normalizers {d : ℕ} (hd : 1 ≤ d) (Cg cg : ℝ) (hcg : 0 < cg) :
    ∃ astar B : ℝ, 0 < astar ∧ 0 ≤ B ∧
      ∀ ρ : Euc d → ℝ, HRS.Whole.IsProbDensity ρ → HasR2GaussianUpper Cg cg ρ →
      ∀ N : ℕ, 2 ≤ N → ∀ θ ∈ Set.Icc (-astar) (0 : ℝ),
        Integrable (fun X : EucConfig d N => Real.exp (-θ * N *
          rieszModulatedEnergy d 0 X (HRS.Whole.withDensityReal ρ)))
          (Measure.pi fun _ : Fin N => HRS.Whole.withDensityReal ρ) ∧
        0 < HRS.Whole.gibbsNormalizer (rieszKernel d 0) N θ (HRS.Whole.withDensityReal ρ) ∧
        |Real.log (HRS.Whole.gibbsNormalizer (rieszKernel d 0) N θ (HRS.Whole.withDensityReal ρ))| ≤ B := by
  obtain ⟨astar, B, hastar, hB, hall⟩ := HRS.MS.S113BD.s113x_X4_generic (d := d) hd Cg cg hcg
  refine ⟨astar, B, hastar, hB, fun ρ hρ hG N hN θ hθ => ?_⟩
  obtain ⟨hK, hlog⟩ := hall ρ hρ.measurable (fun x => ⟨hρ.nonneg x, hG.2 x⟩) hρ.integral_one N hN θ hθ
  haveI : IsProbabilityMeasure (HRS.Whole.withDensityReal ρ) := HRS.MS.R2Mt.s92_isProb_mu hρ
  refine ⟨?_, hK, hlog⟩
  exact HRS.MS.S113BD.s113x_weight_integrable (G := fun x y : Euc d => rieszKernel d 0 (x - y)) (N := N) (b := θ) hK

end HRS.MS.S116

end
