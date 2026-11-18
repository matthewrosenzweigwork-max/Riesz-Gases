import HRS.Main.ThermAux4
import HRS.Equilibrium.ResponseVariance
import HRS.Equilibrium.MarginalDensity

/-!
# THERM helper 5: second moment of `η_N` as a sum over Fourier modes
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS

namespace Main

variable {d N : ℕ} {m : ℝ}

/-- The `k`-th unweighted real Fourier coordinate of `η_N = √N(μ_N - μ)`. -/
def therm_eta (μ : Measure (Torus d)) (k : NonzeroLattice d) (X : Config d N) : ℝ :=
  Real.sqrt N * ((N : ℝ)⁻¹ * ∑ i, Torus.realMode k (X i) - Torus.measureRealCoeff μ k)

theorem therm_coord_etaE (hm : (d : ℝ) < 2 * m) (μ : Measure (Torus d)) [IsProbabilityMeasure μ]
    (hN : 1 ≤ N) (X : Config d N) (k : NonzeroLattice d) :
    NegSobolev.coord (etaE m X μ) k = Lattice.jp k.1 ^ (-m) * therm_eta μ k X := by
  unfold etaE flucE therm_eta
  rw [therm_coord_smul, HRS.coord_ofMeasureDiff_empirical hm μ hN]
  ring

theorem therm_measurable_eta (μ : Measure (Torus d)) (k : NonzeroLattice d) :
    Measurable (therm_eta (N := N) μ k) := by
  unfold therm_eta
  refine measurable_const.mul (Measurable.sub (measurable_const.mul ?_) measurable_const)
  exact Finset.measurable_sum _ fun i _ =>
    (continuous_realMode' k).measurable.comp (measurable_pi_apply i)

/-- Mode-by-mode second moments control the second moment of the `E_m` norm. -/
theorem therm_lintegral_sq_etaE (hm : (d : ℝ) < 2 * m) (μ : Measure (Torus d))
    [IsProbabilityMeasure μ] (hN : 1 ≤ N) (Q : Measure (Config d N)) {A : ℝ} (hA : 0 ≤ A)
    (hk : ∀ k : NonzeroLattice d,
      ∫⁻ X, ENNReal.ofReal (therm_eta μ k X ^ 2) ∂Q ≤ ENNReal.ofReal A) :
    ∫⁻ X, ‖etaE m X μ‖ₑ ^ (2 : ℝ) ∂Q ≤
      ENNReal.ofReal (A * ∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (-(2 * m))) := by
  have hsum := summable_jp_rpow (d := d) m hm
  have e1 : ∀ X : Config d N, ‖etaE m X μ‖ₑ ^ (2 : ℝ) =
      ∑' k : NonzeroLattice d, ENNReal.ofReal (Lattice.jp k.1 ^ (-(2 * m)) * therm_eta μ k X ^ 2) := by
    intro X
    rw [← ofReal_norm_eq_enorm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num),
      Real.rpow_two, (NegSobolev.coord_sq (etaE m X μ)).2,
      ENNReal.ofReal_tsum_of_nonneg (fun k => sq_nonneg _) (NegSobolev.coord_sq (etaE m X μ)).1]
    refine tsum_congr fun k => ?_
    rw [therm_coord_etaE hm μ hN, mul_pow, Torus.jp_rpow_sq]
    congr 3
    ring
  have hjp : ∀ k : NonzeroLattice d, 0 ≤ Lattice.jp k.1 ^ (-(2 * m)) := fun k =>
    Real.rpow_nonneg (Torus.jp_pos k.1).le _
  have hmeas : ∀ k : NonzeroLattice d, Measurable fun X : Config d N =>
      ENNReal.ofReal (Lattice.jp k.1 ^ (-(2 * m)) * therm_eta μ k X ^ 2) := fun k =>
    ENNReal.measurable_ofReal.comp (measurable_const.mul ((therm_measurable_eta μ k).pow_const 2))
  simp_rw [e1]
  rw [lintegral_tsum (fun k => (hmeas k).aemeasurable)]
  have h2 : ∀ k : NonzeroLattice d,
      ∫⁻ X, ENNReal.ofReal (Lattice.jp k.1 ^ (-(2 * m)) * therm_eta μ k X ^ 2) ∂Q ≤
        ENNReal.ofReal (Lattice.jp k.1 ^ (-(2 * m)) * A) := fun k => by
    simp_rw [ENNReal.ofReal_mul (hjp k)]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact mul_le_mul_right (hk k) _
  have hsumA : Summable fun k : NonzeroLattice d => Lattice.jp k.1 ^ (-(2 * m)) * A :=
    hsum.mul_right A
  calc ∑' k : NonzeroLattice d,
        ∫⁻ X, ENNReal.ofReal (Lattice.jp k.1 ^ (-(2 * m)) * therm_eta μ k X ^ 2) ∂Q
      ≤ ∑' k : NonzeroLattice d, ENNReal.ofReal (Lattice.jp k.1 ^ (-(2 * m)) * A) :=
        ENNReal.tsum_le_tsum h2
    _ = ENNReal.ofReal (∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (-(2 * m)) * A) :=
        (ENNReal.ofReal_tsum_of_nonneg (fun k => mul_nonneg (hjp k) hA) hsumA).symm
    _ = _ := by rw [tsum_mul_right, mul_comm]

end Main

end HRS
