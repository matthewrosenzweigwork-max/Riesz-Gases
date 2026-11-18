import HRS.MS.CritForceAssemblyMaj
import HRS.MS.S82P2Mom
import HRS.MS.WrCal

/-!
# S8.2 observed-time layer, packet T8A.R03: calibration field bound for the deltaN uniform field

For a probability density perturbation `theta - 1` with `L2` norm at most `C HRS.MS.Phase2S82.deltaN N` and a bounded long-range kernel
`|k| ≤ K`, the centred field `-β ∫ k(x-y)(θ y - 1) + β ∫∫ k(z-y)(θ y - 1)` is at most `2 β K C HRS.MS.Phase2S82.deltaN N`.
The proof uses only the bounded kernel and the `L2 → L1` comparison on a probability space.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators ContDiff
namespace HRS.MS.R26T8A
open HRS

theorem r26t8a_calibration_field_bound {d : ℕ} (mu : Measure (Euc d))
    [IsProbabilityMeasure mu] (beta K C : ℝ) (hbeta : 0 ≤ beta) (hK : 0 ≤ K)
    (hC : 0 ≤ C) (k : Euc d → ℝ) (theta : Euc d → ℝ) (N : ℕ)
    (hk : Measurable k) (hkb : ∀ z, |k z| ≤ K) (ht : MemLp (fun x => theta x - 1) 2 mu)
    (htb : eLpNorm (fun x => theta x - 1) 2 mu ≤ ENNReal.ofReal (C * HRS.MS.Phase2S82.deltaN N))
    (hdelta : 0 ≤ HRS.MS.Phase2S82.deltaN N) :
    ∀ x, |(-beta * ∫ y, k (x - y) * (theta y - 1) ∂mu) +
      beta * ∫ z, ∫ y, k (z - y) * (theta y - 1) ∂mu ∂mu| ≤
        2 * beta * K * C * HRS.MS.Phase2S82.deltaN N := by
  have hgL1 : Integrable (fun x => theta x - 1) mu := ht.integrable one_le_two
  -- the L1 norm of the perturbation
  have hL1 : ∫ y, ‖theta y - 1‖ ∂mu ≤ C * HRS.MS.Phase2S82.deltaN N := by
    have h12 : eLpNorm (fun x => theta x - 1) 1 mu ≤ eLpNorm (fun x => theta x - 1) 2 mu :=
      eLpNorm_le_eLpNorm_of_exponent_le one_le_two
    have he : eLpNorm (fun x => theta x - 1) 1 mu = ∫⁻ y, ‖theta y - 1‖ₑ ∂mu := by
      first
        | exact eLpNorm_one_eq_lintegral_enorm
        | exact eLpNorm_one_eq_lintegral_enorm hgL1.aestronglyMeasurable
    rw [integral_norm_eq_lintegral_enorm hgL1.aestronglyMeasurable, ← he]
    exact ENNReal.toReal_le_of_le_ofReal (mul_nonneg hC hdelta) (h12.trans htb)
  -- pointwise bound on the inner integral
  have hI : ∀ z, ‖∫ y, k (z - y) * (theta y - 1) ∂mu‖ ≤ K * (C * HRS.MS.Phase2S82.deltaN N) := by
    intro z
    refine (norm_integral_le_integral_norm _).trans ?_
    calc ∫ y, ‖k (z - y) * (theta y - 1)‖ ∂mu
        ≤ ∫ y, K * ‖theta y - 1‖ ∂mu := by
          refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun y => norm_nonneg _)
            (hgL1.norm.const_mul K) (Filter.Eventually.of_forall fun y => ?_)
          dsimp only
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_right (by simpa using hkb (z - y)) (norm_nonneg _)
      _ = K * ∫ y, ‖theta y - 1‖ ∂mu := integral_const_mul K _
      _ ≤ K * (C * HRS.MS.Phase2S82.deltaN N) := mul_le_mul_of_nonneg_left hL1 hK
  intro x
  have hA : ‖-beta * ∫ y, k (x - y) * (theta y - 1) ∂mu‖ ≤ beta * (K * (C * HRS.MS.Phase2S82.deltaN N)) := by
    rw [norm_mul, norm_neg, Real.norm_eq_abs, abs_of_nonneg hbeta]
    exact mul_le_mul_of_nonneg_left (hI x) hbeta
  have hB : ‖beta * ∫ z, ∫ y, k (z - y) * (theta y - 1) ∂mu ∂mu‖ ≤ beta * (K * (C * HRS.MS.Phase2S82.deltaN N)) := by
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg hbeta]
    refine mul_le_mul_of_nonneg_left ?_ hbeta
    refine (norm_integral_le_of_norm_le_const (C := K * (C * HRS.MS.Phase2S82.deltaN N)) ?_).trans ?_
    · exact Filter.Eventually.of_forall fun z => hI z
    · simp
  calc |(-beta * ∫ y, k (x - y) * (theta y - 1) ∂mu) + beta * ∫ z, ∫ y, k (z - y) * (theta y - 1) ∂mu ∂mu|
      = ‖(-beta * ∫ y, k (x - y) * (theta y - 1) ∂mu) + beta * ∫ z, ∫ y, k (z - y) * (theta y - 1) ∂mu ∂mu‖ :=
        (Real.norm_eq_abs _).symm
    _ ≤ ‖-beta * ∫ y, k (x - y) * (theta y - 1) ∂mu‖ + ‖beta * ∫ z, ∫ y, k (z - y) * (theta y - 1) ∂mu ∂mu‖ :=
        norm_add_le _ _
    _ ≤ beta * (K * (C * HRS.MS.Phase2S82.deltaN N)) + beta * (K * (C * HRS.MS.Phase2S82.deltaN N)) := add_le_add hA hB
    _ = 2 * beta * K * C * HRS.MS.Phase2S82.deltaN N := by ring

end HRS.MS.R26T8A

end
