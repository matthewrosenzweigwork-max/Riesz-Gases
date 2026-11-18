import HRS.MC.SEdgeB1
import HRS.MC.SEdgeB3
import HRS.MC.S7S7eAux2
import HRS.MC.S7S7dAux11

/-!
# Packet `s7_FC_D3` (time-zero `W_q` convergence), sub-statement L1: covariance bridge

`susceptibilityCov` (`∫ (φ - μ φ) R_μ ψ dμ`, `R_μ ψ` the `L²(μ)` solution of the response equation) equals
`∫ φ * responseRep ψ dμ` (the continuous representative) for smooth `φ, ψ`, hence the Gaussian covariance hypothesis
transfers to the `responseRep` form (`d3_hG`).
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.FCD3

open HRS HRS.Sec7 HRS.MC.SEdge

variable {d : ℕ} {s : ℝ}

/-- **L1a** covariance bridge: for smooth `φ, ψ`, `C_{β,μ}(φ,ψ) = μ(φ · R_{β,μ}ψ)` with the continuous representative. -/
theorem d3_cov_eq (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) {γ : ℝ} (hγ : 0 ≤ γ)
    {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ) {φ ψ : Torus d → ℝ}
    (hφ : Torus.IsSmooth φ) (hψ : Torus.IsSmooth ψ) :
    susceptibilityCov (periodicRiesz d s) (withDensityReal ρ) γ φ ψ =
      ∫ x, φ x * responseRep (periodicRiesz d s) (withDensityReal ρ) γ ψ x ∂(withDensityReal ρ) := by
  haveI : IsProbabilityMeasure (withDensityReal ρ) := HRS.MC.SEdge.B3.b3_prob hρ
  obtain ⟨r, -, hrS, -, hr_ae, hr_eq, hr_mean, -⟩ :=
    HRS.MC.SEdge.B1.sed_B1_regular_proof hd hs0 hs hγ hρ hψ
  have hcont : Continuous r := HRS.Q66.q66_cont_of_smooth hrS
  have hψL : MemLp ψ 2 (withDensityReal ρ) := HRS.MC.Sec7.S7d.s7d_memLp_smooth hρ hψ
  have hresp : ∀ x, responseRep (periodicRiesz d s) (withDensityReal ρ) γ ψ x = r x := fun x =>
    HRS.MC.Sec7.S7e.s7e_responseRep_eq_of_eq hd hs0 hs hγ hρ hψL hcont hr_mean hr_eq x
  have hsusc : susceptibilityCov (periodicRiesz d s) (withDensityReal ρ) γ φ ψ =
      ∫ x, (φ x - pair (withDensityReal ρ) φ) * r x ∂(withDensityReal ρ) := by
    unfold susceptibilityCov l2Inner
    refine integral_congr_ae ?_
    filter_upwards [hr_ae] with x hx
    rw [← hx]
    rfl
  have hint1 : Integrable (fun x => φ x * r x) (withDensityReal ρ) :=
    ((HRS.Q66.q66_cont_of_smooth hφ).mul hcont).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hint2 : Integrable (fun x => r x) (withDensityReal ρ) :=
    hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have key : ∫ x, (φ x - pair (withDensityReal ρ) φ) * r x ∂(withDensityReal ρ) =
      ∫ x, φ x * r x ∂(withDensityReal ρ) - pair (withDensityReal ρ) φ * ∫ x, r x ∂(withDensityReal ρ) := by
    rw [← integral_const_mul, ← integral_sub hint1 (hint2.const_mul _)]
    congr 1
    funext x
    ring
  rw [hsusc, key, hr_mean, mul_zero, sub_zero]
  simp only [hresp]

/-- **L1b** the susceptibility covariance hypothesis of the Gaussian limit implies the `responseRep` form. -/
theorem d3_hG (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) {γ : ℝ} (hγ : 0 ≤ γ)
    {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ) {m : ℝ} {ν : Measure (NegSobolev d m)}
    (h : IsCenteredGaussianWithCov m ν (susceptibilityCov (periodicRiesz d s) (withDensityReal ρ) γ)) :
    IsCenteredGaussianWithCov m ν (fun φ ψ =>
      ∫ x, φ x * responseRep (periodicRiesz d s) (withDensityReal ρ) γ ψ x ∂(withDensityReal ρ)) := by
  refine ⟨h.1, fun φ ψ hφ hψ => ?_⟩
  exact (h.2 φ ψ hφ hψ).trans (d3_cov_eq hd hs0 hs hγ hρ hφ hψ)

end HRS.MC.Sec7.FCD3
