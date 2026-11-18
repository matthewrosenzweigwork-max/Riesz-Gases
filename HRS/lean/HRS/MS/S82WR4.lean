import HRS.MS.S82WR3

/-!
# S8.2 A05 (S82W), part 11: the error statistic is in `L²` and its centered norm is `O(N^{-1/2})`
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace

namespace HRS.MS.S82W
open HRS HRS.Whole HRS.MS.Phase2S82

theorem w_err_center {d N : ℕ} (hN : 2 ≤ N) {a beta : ℝ} {rho : Euc d → ℝ} {Q : Euc d → Euc d → ℝ}
    {G : Euc d → Euc d → Euc d → ℝ} [IsProbabilityMeasure (canonicalP d N a beta)]
    (hd : 2 ≤ d)
    (hJ : MemLp (Phase2S82.pairStatistic (N := N)
      (pairJ (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) Q)) 2 (canonicalP d N a beta))
    (hBm : MemLp (fun X : EucConfig d N => (N : ℝ) ^ (-(5 / 2 : ℝ)) *
      Phase2S82.pairSum (repeatedB rho Q) X) 2 (canonicalP d N a beta))
    (hT : MemLp (fun X : EucConfig d N => (N : ℝ) ^ (-(5 / 2 : ℝ)) * Phase2S82.tripleSum G X) 2
      (canonicalP d N a beta))
    (hGeq : ∀ X : EucConfig d N, X ∉ eucCollisionSet d N →
      Phase2S82.tripleSum G X = Phase2S82.tripleSum (tripleG (critCoeff d a beta rho) rho Q) X)
    {C6 C7 CA B : ℝ} (hC6 : 0 ≤ C6) (hC7 : 0 ≤ C7) (hCA : 0 ≤ CA) (hB : 0 ≤ B)
    (hvJ : evariance (Phase2S82.pairStatistic (N := N)
      (pairJ (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) Q)) (canonicalP d N a beta) ≤
        ENNReal.ofReal (C6 * B ^ 2 * logN N / N))
    (hvB : evariance (fun X : EucConfig d N => (N : ℝ) ^ (-(5 / 2 : ℝ)) *
      Phase2S82.pairSum (repeatedB rho Q) X) (canonicalP d N a beta) ≤ ENNReal.ofReal (C6 * B ^ 2 / N))
    (hvT : evariance (fun X : EucConfig d N => (N : ℝ) ^ (-(5 / 2 : ℝ)) * Phase2S82.tripleSum G X)
      (canonicalP d N a beta) ≤ ENNReal.ofReal (C7 * (CA * B) ^ 2 * logN N ^ 2 / (N : ℝ) ^ 2)) :
    MemLp (errorStatistic (critCoeff d a beta rho) rho Q) 2 (canonicalP d N a beta) ∧
    eLpNorm (centerUnder (canonicalP d N a beta) (errorStatistic (critCoeff d a beta rho) rho Q)) 2
      (canonicalP d N a beta) ≤
      ENNReal.ofReal (((3 * Real.sqrt C6 + 2 * Real.sqrt C7 * CA) * B) / Real.sqrt N) := by
  set P := canonicalP d N a beta with hP
  have hN1 : 1 ≤ N := by omega
  have hpos : (0 : ℝ) < N := by exact_mod_cast hN1
  have hL0 : 0 ≤ logN N := by
    unfold logN
    rw [Real.log_mul (Real.exp_pos 1).ne' hpos.ne', Real.log_exp]
    have := Real.log_nonneg (by exact_mod_cast hN1 : (1 : ℝ) ≤ N)
    linarith
  set J := Phase2S82.pairStatistic (N := N) (pairJ (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) Q) with hJdef
  set W : EucConfig d N → ℝ := fun X => (N : ℝ) ^ (-(5 / 2 : ℝ)) * Phase2S82.pairSum (repeatedB rho Q) X with hW
  set T : EucConfig d N → ℝ := fun X => (N : ℝ) ^ (-(5 / 2 : ℝ)) * Phase2S82.tripleSum G X with hTdef
  set comb : EucConfig d N → ℝ := fun X => (-(2 / (N : ℝ))) * J X + T X - W X with hcomb
  have hae0 : ∀ᵐ X ∂P, X ∉ eucCollisionSet d N := by
    rw [ae_iff]; simpa using HRS.MS.S82U.u4_P_coll hd N a beta
  have hae : errorStatistic (critCoeff d a beta rho) rho Q =ᵐ[P] comb := by
    filter_upwards [hae0] with X hX
    simp only [errorStatistic, hcomb, hTdef, hW, hJdef, hGeq X hX]
    ring
  have hmem : MemLp comb 2 P := ((hJ.const_mul (-(2 / (N : ℝ)))).add hT).sub hBm
  refine ⟨hmem.ae_eq hae.symm, ?_⟩
  have hcen : centerUnder P (errorStatistic (critCoeff d a beta rho) rho Q) =ᵐ[P] centerUnder P comb := by
    have hint : ∫ Y, errorStatistic (critCoeff d a beta rho) rho Q Y ∂P = ∫ Y, comb Y ∂P := integral_congr_ae hae
    filter_upwards [hae] with X hX
    simp only [centerUnder, hX, hint]
  rw [eLpNorm_congr_ae hcen]
  have hcJ := w_center_sqrt hJ.aestronglyMeasurable (by positivity : 0 ≤ C6 * B ^ 2 * logN N / N) hvJ
  have hcT := w_center_sqrt hT.aestronglyMeasurable
    (by positivity : 0 ≤ C7 * (CA * B) ^ 2 * logN N ^ 2 / (N : ℝ) ^ 2) hvT
  have hcB := w_center_sqrt hBm.aestronglyMeasurable (by positivity : 0 ≤ C6 * B ^ 2 / N) hvB
  have := w_center_comb hJ hT hBm (-(2 / (N : ℝ))) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    hcJ hcT hcB
  refine this.trans (ENNReal.ofReal_le_ofReal ?_)
  have h2 : |-(2 / (N : ℝ))| = 2 / N := by rw [abs_neg, abs_of_nonneg (by positivity)]
  rw [h2]
  exact w_err_numbers hN hC6 hC7 hCA hB

end HRS.MS.S82W
