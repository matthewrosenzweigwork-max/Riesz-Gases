import HRS.MC.S7FCH4H
import HRS.MC.S7FCDA1

/-!
# S7FCH4I: H4 `s7_FC_H4_finite_rank_W` (proof)

The core `S7FCH4_core` with the FC-D conclusion `hD` supplied by the (sorry-free) proof
`HRS.MC.Sec7.S7FCDA.s7_FC_D_leading_path_clt_route_proof`.
-/
open MeasureTheory Filter Topology ProbabilityTheory
open HRS HRS.Sec7 HRS.MC.Sec7 HRS.MC.SEdge HRS.MC.QRSpec HRS.MC.Sec7.FCPlan
open scoped ENNReal NNReal BigOperators
noncomputable section
namespace HRS.MC.Sec7.S7FCH4
variable {d : ℕ}

/-- **H4**, proof of `s7_FC_H4_finite_rank_W`. -/
theorem s7_FC_H4_finite_rank_W_proof (R : Regime d) (r : ℝ) (hr : r = 2 * (d : ℝ) + 6) (T : ℝ) (hT : 0 < T)
    {Ω : ℕ → Type} [∀ N, MeasurableSpace (Ω N)] (P : ∀ N, Measure (Ω N))
    [∀ N, IsProbabilityMeasure (P N)] (X₀ : ∀ N, Ω N → Config d N)
    (W : ∀ N, ℝ≥0 → Ω N → (Fin N → Euc d)) (X : ∀ N, ℝ≥0 → Ω N → Config d N)
    (hreal : ∀ N, 1 ≤ N → PreparedRealization R.D (P N)
      (modulatedGibbs (periodicRiesz d R.D.s) N R.β₀ (withDensityReal R.ρ₀)) (X₀ N) (W N) (X N))
    {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (η : ℝ → Ω' → NegSobolev d r)
    (hη : IsGaussianLimitField R.D R.ρ (withDensityReal R.ρ₀) R.β₀ r P' η)
    (S : Finset (NonzeroLattice d)) (K : NonzeroLattice d → FRKernel d) (q : ℝ) (hq : 1 ≤ q) :
    Tendsto (fun N : ℕ => wassersteinE q
        (law (P N) (fun ω => (zetaWin r T 0 (P N) (X N) ω,
          toL2 r T (fun t => fcPartAt r S K (fun t => withDensityReal (R.ρ t)) (P N) (X N) (0 + t) ω))))
        (law P' (fun ω => (procWin r T 0 η ω, toL2 r T (fun t => fcGaussAt r S K P' η (0 + t) ω)))))
      atTop (𝓝 0) :=
  S7FCH4_core R r hr T hT P X₀ W X hreal P' η hη S K q hq
    (HRS.MC.Sec7.S7FCDA.s7_FC_D_leading_path_clt_route_proof R r hr T hT P X₀ W X hreal P' η hη).2

end HRS.MC.Sec7.S7FCH4
