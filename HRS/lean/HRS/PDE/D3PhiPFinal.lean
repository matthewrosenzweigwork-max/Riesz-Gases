import HRS.PDE.D3PhiPAux12

/-!
# D3PHIP: proofs of the packets of `HRS/PDE/TorusFPLpSpec.lean`

Relocated proofs (statements verbatim; each tied to the frozen specification by `type_of%`):
* `d3phi_identity_classical_proof` (packet A; helpers `D3PhiPAux1`-`Aux10`, prefix `d3pp_`);
* `d3phi_approx_Lp_proof` (packet C1; helpers `D3PhiPAux11`-`Aux12`).
Route (reviewer's shortcut, with the chain rule done pointwise in `x` and Fubini'd): `Y(r) = ∫ A(r,x) dP`,
`A = h^p e^{ψ}/Z̃ = exp(p ℓ + m)`, each `A(·,x)` is absolutely continuous (`p` AC, `ℓ, m` Lipschitz in time) with a.e.
derivative `D`; then `Y(t) - Y(0) = ∫_0^t ∫ D dP dr`, and `∫ D_r dP` is the right-hand side by two applications of the
weighted Green identity (`d3pp_green_fixed`, `d3pp_inner`).
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace HRS

variable {n : ℕ}

theorem d3phi_identity_classical_proof (hn : 1 ≤ n) {κ : ℝ} (hκ : 0 < κ) {U : Torus n → ℝ}
    (hU : Torus.IsSmooth U) {T : ℝ} (hT : 0 < T) {w : ℝ → Torus n → ℝ} (hw : D3Classical κ U T w)
    {ψ ψt : ℝ → Torus n → ℝ} (hψ : IsC12Test T ψ ψt) {p : ℝ → ℝ}
    (hpac : AbsolutelyContinuousOnInterval p 0 T) (hp1 : ∀ r ∈ Set.Icc 0 T, 1 < p r) :
    ∀ t ∈ Set.Icc 0 T,
      IntegrableOn (fun r => d3phi_dir κ U ψ w p r) (Set.Icc 0 t) ∧
      IntegrableOn (fun r => (p r - 1) * d3phi_Sh κ U ψ ψt w p r) (Set.Icc 0 t) ∧
      IntegrableOn (fun r => deriv p r * d3phi_Ylog κ U ψ w p r) (Set.Icc 0 t) ∧
      d3phi_Y κ U ψ w p t + ∫ r in Set.Icc 0 t, d3phi_dir κ U ψ w p r
        = d3phi_Y κ U ψ w p 0 + ∫ r in Set.Icc 0 t,
            ((p r - 1) * d3phi_Sh κ U ψ ψt w p r + deriv p r * d3phi_Ylog κ U ψ w p r) :=
  d3pp_identity hn hκ hU hT hw hψ hpac hp1

example := (@d3phi_identity_classical_proof : type_of% @HRS.d3phi_identity_classical)

theorem d3phi_approx_Lp_proof (q : Measure (Torus n)) [IsProbabilityMeasure q] {ρ : Torus n → ℝ}
    (hρc : Continuous ρ) (hρ : ∀ x, 0 < ρ x) {ν : Measure (Torus n)} [IsProbabilityMeasure ν]
    (hac : ν ≪ q) {p₀ : ℝ} (hp₀ : 1 < p₀)
    (hfin : eLpNorm (ν.rnDeriv q) (ENNReal.ofReal p₀) q < ⊤) :
    ∃ g : ℕ → Torus n → ℝ, (∀ k, Torus.IsSmooth (g k)) ∧ (∀ k x, 0 < g k x) ∧
      (∀ k, ∫ x, g k x * ρ x ∂q = 1) ∧
      (∀ φ : Torus n → ℝ, Continuous φ →
        Tendsto (fun k => ∫ x, g k x * ρ x * φ x ∂q) atTop (𝓝 (∫ x, φ x ∂ν))) ∧
      Tendsto (fun k => eLpNorm (fun x => ENNReal.ofReal (g k x * ρ x)) (ENNReal.ofReal p₀) q) atTop
        (𝓝 (eLpNorm (ν.rnDeriv q) (ENNReal.ofReal p₀) q)) :=
  d3pp_approx_Lp q hρc hρ hac hp₀ hfin

example := (@d3phi_approx_Lp_proof : type_of% @HRS.d3phi_approx_Lp)

end HRS
