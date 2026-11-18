import HRS.Uniform.Q48bAux3
import HRS.Energy.StaticLimitBasic

/-!
# EQP7C P7.6: uniform projected-test bound

`eqevo_proj_test_unif` is `HRS.Uniform.Q48b.q48b_proj_test_bound` with the constant made uniform in
the probability density `ρ`: the constant `‖NegSobolev.ofMeasureDiff a (withDensityReal ρ) volume‖`
of the original statement is replaced by the bound `sqrt (8 ∑' jp^{-2a})` of
`HRS.norm_ofMeasureDiff_le` (valid for every probability density when `d < 2a`).
-/

noncomputable section

open MeasureTheory Filter Topology

namespace HRS.MD.EQEvoProjTest

open HRS HRS.PDE HRS.Uniform.Q48b

variable {d : ℕ}

/-- **P7.6.** Uniform (in the probability density `ρ`) bound for the `ρ`-mean projection of a test
function. -/
theorem eqevo_proj_test_unif (a : ℝ) (ha : (d : ℝ) < 2 * a) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (ρ : Torus d → ℝ), IsProbDensity ρ →
      ∀ (T : Finset (NonzeroLattice d)) (c : NonzeroLattice d → ℝ),
        sobolevNorm a (projMean (withDensityReal ρ) (q48bTest T c)) ≤
          K * Real.sqrt (∑ l ∈ T, q48bW l ^ (2 * a) * c l ^ 2) := by
  set B0 : ℝ := Real.sqrt (8 * ∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (-(2 * a))) with hB0
  refine ⟨Real.sqrt (B0 ^ 2 + 1), Real.sqrt_nonneg _, fun ρ hρ T c => ?_⟩
  haveI : IsProbabilityMeasure (withDensityReal ρ) := isProb_withDensityReal hρ
  have hBle : ‖NegSobolev.ofMeasureDiff a (withDensityReal ρ) (volume : Measure (Torus d))‖ ≤ B0 :=
    norm_ofMeasureDiff_le ha _ _
  set φ := q48bTest T c with hφ
  set N : ℝ := Real.sqrt (∑ l ∈ T, q48bW l ^ (2 * a) * c l ^ 2) with hN
  have hNn : 0 ≤ N := Real.sqrt_nonneg _
  set p : ℝ := pair (withDensityReal ρ) φ with hp
  have hpair0 : pair (volume : Measure (Torus d)) φ = 0 := by
    have := q48bTest_mean T c
    unfold Torus.mean at this
    exact this
  have hpB : |p| ≤ B0 * N := by
    have := abs_pair_sub_le a ha (withDensityReal ρ) volume φ (q48bTest_memSobolev T c a)
      (q48bTest_continuous T c)
    rw [hpair0, sub_zero, ← hp] at this
    rw [hφ, q48bTest_sobolevNorm] at this
    exact this.trans (mul_le_mul_of_nonneg_right hBle hNn)
  have hmean : Torus.mean (projMean (withDensityReal ρ) φ) = -p := by
    unfold Torus.mean projMean
    rw [integral_sub (q48b_integrable_cont (q48bTest_continuous T c)) (integrable_const _)]
    have := q48bTest_mean T c
    unfold Torus.mean at this
    simp [this, hp]
  have hcoef : ∀ k, Torus.funRealCoeff (projMean (withDensityReal ρ) φ) k = Torus.funRealCoeff φ k := by
    intro k
    have h := q48b_funRealCoeff_add_const (g := φ)
      ((q48bTest_continuous T c).memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)) (-p) k
    unfold projMean
    simpa [sub_eq_add_neg] using h
  have hsq : sobolevNorm a (projMean (withDensityReal ρ) φ) ^ 2 = p ^ 2 + N ^ 2 := by
    unfold sobolevNorm
    rw [Real.sq_sqrt, hmean]
    · have : ∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (2 * a) *
          Torus.funRealCoeff (projMean (withDensityReal ρ) φ) k ^ 2 = N ^ 2 := by
        simp_rw [hcoef]
        rw [hφ, q48bTest_tsum, hN, Real.sq_sqrt]
        exact Finset.sum_nonneg fun l _ => mul_nonneg (Real.rpow_nonneg (q48bW_pos l).le _) (sq_nonneg _)
      rw [this]; ring
    · exact add_nonneg (sq_nonneg _) (tsum_nonneg fun k =>
        mul_nonneg (Real.rpow_nonneg (Torus.jp_pos _).le _) (sq_nonneg _))
  have hle : sobolevNorm a (projMean (withDensityReal ρ) φ) ^ 2 ≤
      (Real.sqrt (B0 ^ 2 + 1) * N) ^ 2 := by
    have h1 : Real.sqrt (B0 ^ 2 + 1) ^ 2 = B0 ^ 2 + 1 := Real.sq_sqrt (by positivity)
    rw [hsq, mul_pow, h1]
    have : p ^ 2 ≤ (B0 * N) ^ 2 := by
      rw [← sq_abs p]; exact pow_le_pow_left₀ (abs_nonneg _) hpB 2
    nlinarith [this]
  have hnn : 0 ≤ Real.sqrt (B0 ^ 2 + 1) * N := by positivity
  have hsn : 0 ≤ sobolevNorm a (projMean (withDensityReal ρ) φ) := Real.sqrt_nonneg _
  exact le_of_sq_le_sq hle hnn |>.trans le_rfl

end HRS.MD.EQEvoProjTest
