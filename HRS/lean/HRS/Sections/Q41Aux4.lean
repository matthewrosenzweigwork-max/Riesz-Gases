import HRS.Sections.Sec3
import HRS.Energy.StaticLimitGauss
import HRS.Sections.Q41Aux3

/-!
# Packet Q41, helper 4: Proposition 5.18 (ii) for an arbitrary stationary Gaussian field

For `d ≥ 2`, smooth `V`, smooth positive thermal density `ρ_β` and *any* `E_m`-valued
`IsStationaryGaussianField` `Z` (any real `m`), almost surely `sup_{t ≥ 0} ‖Z_t‖_{E_m} = ∞`
(`q41_unbounded_of_field`).  The scalar coordinate `X_t = ⟨Z_t, φ⟩` of a smooth test function
`φ` (a real Fourier mode) has Gaussian finite-dimensional laws with the stationary kernel
`ρ(|t-u|)`, `ρ(0) > 0`, `ρ(∞) = 0` (`q41_kernel_data`), hence is a.s. unbounded
(`q41_ae_unbounded_of_kernel`), and `|⟨F, φ⟩| ≤ ‖F‖_{E_m} ‖φ‖_{H^m}`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal

namespace HRS.Q41

open HRS HRS.PDE

variable {d : ℕ}

theorem q41_unbounded_of_field (hd : 2 ≤ d) {s β : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (hβ : 0 < β)
    (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (ρβ : Torus d → ℝ)
    (hρβ : IsThermalDensity (periodicRiesz d s) V β ρβ) (hρS : Torus.IsSmooth ρβ)
    (hρpos : ∀ x, 0 < ρβ x) (m : ℝ) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Z : ℝ → Ω → NegSobolev d m)
    (hZ : IsStationaryGaussianField P s β hs0 hsd hβ V ρβ m Z) :
    ∀ᵐ ω ∂P, ∀ M : ℝ, ∃ t : ℝ, 0 ≤ t ∧ M < ‖Z t ω‖ := by
  obtain ⟨φ, hφS, ρ, h0, hdec, hker⟩ := q41_kernel_data hd hs0 hsd hβ V hV ρβ hρβ hρS hρpos
  set X : ℝ → Ω → ℝ := fun t ω => NegSobolev.eval (Z t ω) φ with hX
  have hXm : ∀ t, Measurable (X t) := by
    intro t
    have : (fun ω => NegSobolev.eval (Z t ω) φ) =
        fun ω => inner ℝ (Z t ω) (HRS.StaticLimitAux.avec m hφS) := by
      funext ω; exact HRS.StaticLimitAux.eval_eq_inner m hφS (Z t ω)
    show Measurable (fun ω => NegSobolev.eval (Z t ω) φ)
    rw [this]
    exact (hZ.meas t).inner measurable_const
  have hlaw : ∀ (p : ℕ) (τ : Fin p → ℝ), (∀ a, 0 ≤ τ a) →
      P.map (fun ω => (WithLp.toLp 2 (fun a => X (τ a) ω) : EuclideanSpace ℝ (Fin p))) =
        multivariateGaussian 0 (Matrix.of fun a b => ρ |τ a - τ b|) := by
    intro p τ hτ
    have h1 := hZ.gaussian p τ (fun _ => φ) hτ (fun _ => hφS)
    refine h1.trans ?_
    congr 1
    ext a b
    simp only [PDE.stationaryLagCov, Matrix.of_apply]
    by_cases hab : τ a ≤ τ b
    · rw [if_pos hab, abs_sub_comm, abs_of_nonneg (by linarith)]
      exact (hker (τ b - τ a) (by linarith)).1
    · push_neg at hab
      rw [if_neg (not_le.2 hab), abs_of_nonneg (by linarith)]
      exact (hker (τ a - τ b) (by linarith)).2
  have hun := q41_ae_unbounded_of_kernel P X hXm ρ h0 hdec hlaw
  have hsum := HRS.StaticLimitAux.summable_weighted_smooth m hφS
  set Cφ : ℝ := Real.sqrt (∑' k : NonzeroLattice d,
    Lattice.jp k.1 ^ (2 * m) * Torus.funRealCoeff φ k ^ 2) with hCφ
  have hCφ0 : 0 ≤ Cφ := Real.sqrt_nonneg _
  filter_upwards [hun] with ω hω M
  obtain ⟨t, ht, hM⟩ := hω (M * (Cφ + 1))
  refine ⟨t, ht, ?_⟩
  have hb : |X t ω| ≤ ‖Z t ω‖ * Cφ := NegSobolev.abs_eval_le (Z t ω) φ hsum
  have hn : 0 ≤ ‖Z t ω‖ := norm_nonneg _
  by_contra hcon
  push_neg at hcon
  have : ‖Z t ω‖ * (Cφ + 1) ≤ M * (Cφ + 1) := mul_le_mul_of_nonneg_right hcon (by linarith)
  nlinarith

end HRS.Q41
