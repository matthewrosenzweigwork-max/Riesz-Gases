import HRS.PDE.MovSpec2
import HRS.PDE.MovEAux3
import HRS.PDE.MovEAux5
import HRS.PDE.MovEAux6

/-!
# MOVE: relocated proofs of MovSpec2 packets (statements verbatim)

* `movT_lp_lsc_proof` (generic lower semicontinuity of the `L^p` norm of the density; duality over `C(α)`:
  `MovEAux1-3`).
* `movT_lp_init_limsup_proof` (initial `L^{p₀}` norms along the regularisation; `MovEAux4-5`).
* `movT_source_exp_scaled_uniform_proof_pos` (`MovEAux6`): the statement of `movT_source_exp_scaled_uniform` with the
  extra hypothesis `0 < T`.  It is FALSE for `T = 0`: `IsC12Test.time_deriv` is vacuous on `Ioo 0 0`, so `ρt 0` is an
  arbitrary continuous function while `c, C` are uniform in `ρt`; counterexample `ρ ≡ 1`, `V = 0` (so `u = 0`, `L ≡ ℓ = 1`),
  `ρt r = K cos(2π x₁)`: `S^M(X) = -κ_M K ∑ᵢ cos(2π x_{i,1}) + const` with `κ_M = 1 + β ĝ_M(e₁) ≥ 1/2` for large `M`,
  and `E_{Q^M} exp(c|S^M|) → ∞` as `K → ∞` (non-degenerate fluctuations of `∑ cos` for `N = 2`) while `C N δ_N` is fixed.
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS

variable {d N : ℕ}

theorem movT_lp_lsc_proof {α : Type*} [MetricSpace α] [CompactSpace α] [MeasurableSpace α] [BorelSpace α]
    {ν Q : Measure α} {νn Qn : ℕ → Measure α} [IsProbabilityMeasure ν] [IsProbabilityMeasure Q]
    [∀ n, IsProbabilityMeasure (νn n)] [∀ n, IsProbabilityMeasure (Qn n)]
    (hν : ∀ φ : α → ℝ, Continuous φ → Tendsto (fun n => ∫ x, φ x ∂(νn n)) atTop (𝓝 (∫ x, φ x ∂ν)))
    (hQ : ∀ φ : α → ℝ, Continuous φ → Tendsto (fun n => ∫ x, φ x ∂(Qn n)) atTop (𝓝 (∫ x, φ x ∂Q)))
    (hacn : ∀ᶠ n in atTop, νn n ≪ Qn n) {p : ℝ} (hp : 1 < p)
    (hlim : liminf (fun n => eLpNorm ((νn n).rnDeriv (Qn n)) (ENNReal.ofReal p) (Qn n)) atTop < ⊤) :
    ν ≪ Q ∧ eLpNorm (ν.rnDeriv Q) (ENNReal.ofReal p) Q ≤
      liminf (fun n => eLpNorm ((νn n).rnDeriv (Qn n)) (ENNReal.ofReal p) (Qn n)) atTop :=
  move_lp_lsc hν hQ hacn hp hlim

example := (@movT_lp_lsc_proof : type_of% @HRS.movT_lp_lsc)

theorem movT_lp_init_limsup_proof (hN : 2 ≤ N) {D : DynData d} {T : ℝ} {ρ : ℝ → Torus d → ℝ}
    (hT : 0 ≤ T) (h : MovTraj D T ρ) {M : ℕ → ℝ} (hM : Tendsto M atTop atTop) (hM0 : ∀ n, 0 ≤ M n)
    {ν : Measure (Config d N)} [IsProbabilityMeasure ν] {p₀ : ℝ} (hp₀ : 1 < p₀)
    (hac : ν ≪ movT_Q (periodicRiesz d D.s) D N ρ 0)
    (hfin : eLpNorm (ν.rnDeriv (movT_Q (periodicRiesz d D.s) D N ρ 0)) (ENNReal.ofReal p₀)
      (movT_Q (periodicRiesz d D.s) D N ρ 0) < ⊤) :
    (∀ n, ν ≪ movT_Q (b15c_gReg d D.s (M n)) D N ρ 0) ∧
      Tendsto (fun n => eLpNorm (ν.rnDeriv (movT_Q (b15c_gReg d D.s (M n)) D N ρ 0))
          (ENNReal.ofReal p₀) (movT_Q (b15c_gReg d D.s (M n)) D N ρ 0)) atTop
        (𝓝 (eLpNorm (ν.rnDeriv (movT_Q (periodicRiesz d D.s) D N ρ 0)) (ENNReal.ofReal p₀)
          (movT_Q (periodicRiesz d D.s) D N ρ 0))) :=
  move_lp_init_limsup hN hT h hM hM0 hp₀ hac hfin

example := (@movT_lp_init_limsup_proof : type_of% @HRS.movT_lp_init_limsup)

/-- `movT_source_exp_scaled_uniform` with the extra hypothesis `0 < T` (the statement is false for `T = 0`, see the header). -/
theorem movT_source_exp_scaled_uniform_proof_pos (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d)
    (βm βp : ℝ) (hβm : 0 < βm) (c₀ : ℝ) (hc₀ : 0 < c₀) (Λ₂ : ℝ) :
    ∃ c C : ℝ, 0 < c ∧ ∀ {D : DynData d} {T : ℝ} {ρ ρt : ℝ → Torus d → ℝ}, MovTraj D T ρ →
      IsC12Test T ρ ρt → 0 < T → D.s = s → D.invβ⁻¹ ∈ Set.Icc βm βp →
      (∀ r ∈ Set.Icc 0 T, ∀ x, c₀ ≤ ρ r x) → (∀ r ∈ Set.Icc 0 T, Torus.cbNorm 2 (ρ r) ≤ Λ₂) →
      ∀ {ℓ : ℝ} (L : ℝ → ℝ), 0 < ℓ →
        (∀ r ∈ Set.Icc 0 T, ℓ ≤ L r ∧ IsLipschitzVF (L r) (mfeTransport D (ρ r))) →
        ∀ N : ℕ, 2 ≤ N → MovSrcScaled D N ρ ρt T c (C * N * deltaN d s N) L :=
  move_source_exp_scaled_pos hd hs0 hsd βm βp hβm c₀ hc₀ Λ₂

end HRS

end
