import HRS.MS.S82P2Cent7
import HRS.MS.QsfCorr2

/-!
# S8.2 R05: weighted pair moments (frozen statement of the Pro skeleton `S82.R05`)
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.Phase2S82
open HRS HRS.Whole

/-- Canonical pair statistic and its exact gradient rows. -/
theorem weighted_pair_moments (d : ℕ) (hd : 2 ≤ d)
    (a beta M C0 C1 : ℝ) (ha : 0 < a) (hbeta : 0 < beta) (hM : 0 ≤ M)
    (q : Euc d → ℝ) (hq : ShortRangePole d q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ rho : Euc d → ℝ,
      IsThermalEquilibrium d (criticalS d) a beta rho →
      ∀ h : ℕ → Euc d → ℝ,
      WeakReferenceSetup d a beta rho q h C0 → PinComparison beta rho q h C1 →
      ∀ f : Euc d → ℝ, ∀ A : ℝ, 0 ≤ A →
      ∀ Q : Euc d → Euc d → ℝ, PairCorrector a beta rho M A f Q →
      ∀ N : ℕ, 2 ≤ N →
        MemLp (pairStatistic (N := N) Q) 2 (canonicalP d N a beta) ∧
        (∀ i, MemLp (fun X : EucConfig d N => configGrad (pairStatistic Q) X i) 2
          (canonicalP d N a beta)) ∧
        evariance (pairStatistic (N := N) Q) (canonicalP d N a beta) +
          (∫⁻ X, ∑ i, ‖configGrad (pairStatistic Q) X i‖ₑ ^ 2 ∂canonicalP d N a beta) ≤
            ENNReal.ofReal (C * A ^ 2 / N) := by
  have hs0 : 0 ≤ criticalS d := by unfold criticalS; positivity
  have hsd : criticalS d < d := by
    unfold criticalS
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  obtain ⟨Cth, cth, BU, hT⟩ := S45.s45_thermal_data hd hs0 hsd ha hbeta
  have hρ0 : HRS.Whole.IsProbDensity (HRS.Whole.thermalDensity d (criticalS d) a beta) := hT.prob
  have hρG : HRS.Whole.HasR2GaussianUpper (Cth + 1) cth
      (HRS.Whole.thermalDensity d (criticalS d) a beta) := by
    refine ⟨hT.hc, fun x => ?_⟩
    have h1 := (le_abs_self _).trans (hT.h0 x)
    have h2 : 0 ≤ Real.exp (-cth * ‖x‖ ^ 2) := (Real.exp_pos _).le
    nlinarith
  have hG : 0 < Cth + 1 := by linarith [hT.C0]
  obtain ⟨C, hC0, hC⟩ := HRS.MS.S82P2.s82p2_pair_moments_fixed (a := a) (C0 := C0) (C1 := C1)
    hd hM hbeta (Cth + 1) cth hG hT.hc hρ0 hρG
  refine ⟨C, hC0, ?_⟩
  intro rho hrho h hW hP f A hA Q hQ N hN
  have hrho_eq := critical_thermal_eq d hd a beta ha hbeta hrho
  subst hrho_eq
  exact hC q h hW hP A hA f Q hQ
    (Filter.Eventually.of_forall fun x => HRS.MS.S82P2.s82p2_gt_centered hd hM hA (Cth + 1) cth hG
      hT.hc hρ0 hρG hQ x) N hN

end HRS.MS.Phase2S82
