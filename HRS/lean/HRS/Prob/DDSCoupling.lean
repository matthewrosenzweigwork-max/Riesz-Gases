import HRS.Prob.CLT
import HRS.Stochastic.DDSCore

/-!
# Lemma A.19 `M:B:lem:dds`: Dambis-Dubins-Schwarz coupling and the `W₂` bound

Source: HRS periodic main paper, lines 10520-10526. Both statements were moved unchanged from
`HRS.Prob.CLT`, because the coupling is proved in `HRS/Stochastic/DDSCore.lean`
(`dds_coupling_proof`), which `HRS.Prob.CLT` cannot import.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]

/-- Lemma A.19 `M:B:lem:dds` (lines 10520-10526), the bound `B:eq:dds-bound`: for a continuous
real martingale with `M_0 = 0` and `E[M]_t < ∞`, and every `v ≥ 0`,
`W_2(Law(M_t), N(0,v)) ≤ (E|[M]_t - v|)^{1/2}`. -/
theorem dds_wasserstein_bound (ℱ : Filtration ℝ mΩ) (t : ℝ) (ht : 0 ≤ t) (M A : ℝ → Ω → ℝ)
    (hM : IsContSqMartingale P ℱ t M) (hA : IsQuadraticVariation P ℱ t M A)
    (hint : Integrable (A t) P) (v : ℝ) (hv : 0 ≤ v) :
    wassersteinE 2 (law P (M t)) (gaussianLaw v) ≤
      ENNReal.ofReal (Real.sqrt (∫ ω, |A t ω - v| ∂P)) :=
  dds_wasserstein_bound_proof P ℱ t ht M A hM hA hint v hv

/-- Lemma A.19, the coupling statement: on an enlargement of the probability space there is a
standard Brownian motion `β` with `M_t = β_{[M]_t}` a.s., `β_v ∼ N(0,v)`, and
`E|β_{[M]_t} - β_v|² ≤ E|[M]_t - v|`.  The enlargement is represented by a probability space
`Ω'` carrying a copy `(M', A')` of `(M_t, [M]_t)` in law and a Brownian motion `β` (Mathlib's
`IsBrownianReal`, time index `ℝ≥0`).  The second-moment bound is stated with a `lintegral`
so that it asserts finiteness of `E|β_{[M]_t} - β_v|²` (a Bochner integral would be `0`, hence
vacuous, for a non-integrable difference; `docs/SPEC_AUDIT.md` B12). -/
theorem dds_coupling (ℱ : Filtration ℝ mΩ) (t : ℝ) (ht : 0 ≤ t) (M A : ℝ → Ω → ℝ)
    (hM : IsContSqMartingale P ℱ t M) (hA : IsQuadraticVariation P ℱ t M A)
    (hint : Integrable (A t) P) (v : ℝ) (hv : 0 ≤ v) :
    ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (P' : Measure Ω') (_ : IsProbabilityMeasure P')
      (M' A' : Ω' → ℝ) (β : ℝ≥0 → Ω' → ℝ),
      ProbabilityTheory.IsBrownianReal β P' ∧
      law P' (fun ω' => (M' ω', A' ω')) = law P (fun ω => (M t ω, A t ω)) ∧
      (∀ᵐ ω' ∂P', M' ω' = β (Real.toNNReal (A' ω')) ω') ∧
      law P' (β (Real.toNNReal v)) = gaussianLaw v ∧
      ∫⁻ ω', ‖β (Real.toNNReal (A' ω')) ω' - β (Real.toNNReal v) ω'‖ₑ ^ 2 ∂P' ≤
        ENNReal.ofReal (∫ ω, |A t ω - v| ∂P) :=
  dds_coupling_proof P ℱ t ht M A hM hA hint v hv

end HRS
