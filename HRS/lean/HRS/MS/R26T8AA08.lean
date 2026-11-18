import HRS.MS.S82WA05
import HRS.MS.R26T8AD00

/-!
# S8.2 T8A A08: `r26t8a_linear_correction` (Pro contract, verbatim)
`(2/N) ζ = (2/√N) · centre(N⁻¹ ∑ f(X_i))`; the marginal domination `w_marg_dom` and `w_zeta_L2` bound the average, centring
costs nothing in `L²` (`w_center_L2`).  `C = 2 C0`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.Phase2S82
open HRS HRS.Whole

theorem _root_.HRS.MS.R26T8A.r26t8a_linear_correction (d : ℕ) (hd : 2 ≤ d) (a beta M C0 C1 : ℝ) (ha : 0 < a)
    (hbeta : 0 < beta) (hM : 0 ≤ M) (q : Euc d → ℝ) (hq : ShortRangePole d q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ rho : Euc d → ℝ, IsThermalEquilibrium d (criticalS d) a beta rho →
      ∀ h : ℕ → Euc d → ℝ, WeakReferenceSetup d a beta rho q h C0 →
      PinComparison beta rho q h C1 →
      ∀ f : Euc d → ℝ, MemLp f 2 (HRS.Whole.withDensityReal rho) → ∀ N : ℕ, 2 ≤ N →
      eLpNorm (fun X : EucConfig d N => (2 / (N : ℝ)) * HRS.MS.R26T8A.r26t8a_zetaActual a beta f X) 2
        (canonicalP d N a beta) ≤
          ENNReal.ofReal (C * (N : ℝ) ^ (-(1 / 2 : ℝ))) * eLpNorm f 2 (HRS.Whole.withDensityReal rho) := by
  refine ⟨2 * Real.sqrt (C0 * C0), by positivity, ?_⟩
  intro rho hrho h hW hP f hf N hN
  haveI hμ : IsProbabilityMeasure (HRS.Whole.withDensityReal rho) := HRS.MS.S82W.w_mu_prob hd ha hbeta hrho
  haveI hPp : IsProbabilityMeasure (canonicalP d N a beta) := HRS.MS.S82U.u4_prob (N := N) hd ha hbeta
  have hN0 : 0 < N := by omega
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN0
  have hsq : 0 < Real.sqrt N := Real.sqrt_pos.2 hNpos
  have hss : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt hNpos.le
  set P := canonicalP d N a beta with hPdef
  set μ := HRS.Whole.withDensityReal rho with hμdef
  have hmarg : ∀ i : Fin N, P.map (fun X => X i) ≤ ENNReal.ofReal (C0 * C0) • μ := by
    intro i
    have := HRS.MS.S82W.w_marg_dom hW hbeta hN i
    rwa [smul_smul, ← ENNReal.ofReal_mul hW.positive.le] at this
  have hz1 := HRS.MS.S82W.w_zeta_L2 (a := a) (beta := beta) (N := N) hN0 (mul_self_nonneg C0) hmarg hf
  set Gz : EucConfig d N → ℝ := fun X => (1 / (N : ℝ)) * ∑ i, f (X i) with hGz
  have hGzm : MemLp Gz 2 P := lt_of_le_of_lt hz1 (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hf.eLpNorm_lt_top)
  have e : (fun X : EucConfig d N => (2 / (N : ℝ)) * zetaActual (N := N) a beta f X) =
      ((2 / (N : ℝ)) * Real.sqrt N) • centerUnder P Gz := by
    funext X
    simp only [zetaActual, Pi.smul_apply, smul_eq_mul]
    ring
  show eLpNorm (fun X : EucConfig d N => (2 / (N : ℝ)) * zetaActual (N := N) a beta f X) 2 P ≤ _
  rw [e, eLpNorm_const_smul, Real.enorm_eq_ofReal (by positivity)]
  have hc : (2 / (N : ℝ)) * Real.sqrt N = 2 * (N : ℝ) ^ (-(1 / 2 : ℝ)) := by
    rw [Real.rpow_neg hNpos.le, ← Real.sqrt_eq_rpow]
    field_simp
    nlinarith [hss]
  have hsqK : Real.sqrt (C0 * C0) = C0 := Real.sqrt_mul_self hW.positive.le
  calc ENNReal.ofReal ((2 / (N : ℝ)) * Real.sqrt N) * eLpNorm (centerUnder P Gz) 2 P
      ≤ ENNReal.ofReal ((2 / (N : ℝ)) * Real.sqrt N) *
          (ENNReal.ofReal (Real.sqrt (C0 * C0)) * eLpNorm f 2 μ) :=
        mul_le_mul' le_rfl ((HRS.MS.S82W.w_center_L2 hGzm.aestronglyMeasurable).trans hz1)
    _ = ENNReal.ofReal (2 * Real.sqrt (C0 * C0) * (N : ℝ) ^ (-(1 / 2 : ℝ))) * eLpNorm f 2 μ := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity), hc]
        congr 2; ring

end HRS.MS.Phase2S82
