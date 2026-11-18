import HRS.Energy.Coercivity
import HRS.Energy.Modulated
import HRS.Equilibrium.RepulsiveBridge

/-!
# MFE (Proposition 3.41 `mfe_uniform`): chain plan and helpers

TeX: M L3200-3240 (`M:B:prop:mfe-uniform`).  Final proof: `HRS/Energy/MFEFinal.lean` (`mfe_uniform_proof`,
statement verbatim, `type_of%` tie).

## Chain plan

Let `f^t = P.map (X t)`, `μ^t = withDensityReal (ρ t)`, `𝖤(t) = modulatedFreeEnergy d s D.invβ (f^t) (μ^t)`,
`o = oNΛ d s C₀ Λ N`, `c(r) = ∫ commQuantity d s (mfeTransport D (ρ r)) Z (μ^r) ∂f^r`.

1. (`MFEHyp ⇒ MovHyp`) bridge D `movT_hyp_of_mfeHyp_proof` (`MovFFinal`; uses `movT_isC12Test_of_weak_proof`).
2. (first sentence of the TeX proof, L3220-3224) `mov_mfe_ineq` (`MovSpec3`): for `t ∈ [0,T]`, `MFEFinite (f^t) (μ^t)`,
   `c` integrable on `[0,T]`, and `𝖤(t) ≤ 𝖤(0) - ½ ∫_0^t c`.
3. Constants: `commutator_estimate_of_packets` (`Commutator/Assembly`, the proved version of Prop 3.32) gives `(A₀, A)` and
   `energy_add_oN_nonneg` (`Commutator/Coerc0`, `F_N + o_N ≥ 0`) gives `B₀`; take `C₀ = max A₀ B₀`, `C = A/2`
   (`oNΛ_mono_C₀`; `K ≥ 0` by `HasTransportBound.nonneg`).
4. Pointwise on `[0,T]` (`ρ r ≤ Λ` from `IsRegularMF` and `‖ρ‖_∞ ≤ ‖ρ‖_{C^k}`): `f^r ≪ volume` and `f^r`-a.e. `Z` is
   collision-free (`mfe41_ac`: `klDiv ≠ ∞` ⇒ `f^r ≪ μ^{⊗N}`, the collision set is `μ^{⊗N}`-null, `μ^{⊗N} ≪ volume`);
   a.e. `|Comm| ≤ A K_r (F + o)` and `F + o ≥ 0`; integrate (`mfe41_int`, `f^r` is a probability measure):
   `|c(r)| ≤ A K_r (∫F f^r + o)` and `0 ≤ ∫F f^r + o ≤ 𝖤(r) + o` (the entropy part `invβ·H ≥ 0`).
5. Grönwall `movspec_gronwall_var` with `u = 𝖤 + o`, `G = -c/2`, `a = (A/2)K`: `u(t) ≤ u(0) exp(∫_0^t a)`;
   then `u(0) ≥ 0`, `K ≥ 0` give `exp(∫_0^t a) ≤ exp((A/2)∫_0^T K)`.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

namespace HRS

variable {d N : ℕ}

/-- Finite relative entropy with respect to `μ^{⊗N}` (`μ` a probability density) gives absolute continuity with
respect to Lebesgue measure and almost-sure absence of collisions. -/
theorem mfe41_ac (hd : 1 ≤ d) {ρ : Torus d → ℝ} (hρ : IsProbDensity ρ) {ν : Measure (Config d N)}
    (h : relEntropy ν (Measure.pi fun _ : Fin N => withDensityReal ρ) ≠ ⊤) :
    ν ≪ (volume : Measure (Config d N)) ∧ ∀ᵐ Z ∂ν, Z ∉ collisionSet d N := by
  have hac : ν ≪ Measure.pi fun _ : Fin N => withDensityReal ρ := by
    unfold relEntropy at h
    exact (InformationTheory.klDiv_ne_top_iff.mp h).1
  have hpv : (Measure.pi fun _ : Fin N => withDensityReal ρ) ≪ (volume : Measure (Config d N)) := by
    rw [pi_withDensityReal_eq ρ hρ.measurable]
    exact withDensity_absolutelyContinuous _ _
  exact ⟨hac.trans hpv, hac.ae_le (Repulsive.ae_notMem_collisionSet hd rfl hρ N)⟩

/-- Integration of the pointwise commutator bound against a probability measure. -/
theorem mfe41_int {α : Type*} [MeasurableSpace α] {ν : Measure α} [IsProbabilityMeasure ν]
    {F c : α → ℝ} {o B : ℝ} (hF : Integrable F ν) (hnn : ∀ᵐ z ∂ν, 0 ≤ F z + o)
    (hc : ∀ᵐ z ∂ν, |c z| ≤ B * (F z + o)) :
    0 ≤ ∫ z, F z ∂ν + o ∧ |∫ z, c z ∂ν| ≤ B * (∫ z, F z ∂ν + o) := by
  have hint : Integrable (fun z => F z + o) ν := hF.add (integrable_const o)
  have hI : ∫ z, (F z + o) ∂ν = ∫ z, F z ∂ν + o := by
    rw [integral_add hF (integrable_const o)]
    simp
  refine ⟨?_, ?_⟩
  · rw [← hI]
    exact integral_nonneg_of_ae hnn
  · have h1 := norm_integral_le_of_norm_le (hint.const_mul B)
      (hc.mono fun z hz => by rw [Real.norm_eq_abs]; exact hz)
    rw [integral_const_mul, hI] at h1
    simpa [Real.norm_eq_abs] using h1

end HRS

end
