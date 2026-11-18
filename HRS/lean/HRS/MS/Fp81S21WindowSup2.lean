import HRS.MS.Fp81S21WindowSup

/-!
# HRS S2.1(iii), SOL40 packet 9d: pathwise shifted-window majorant

The imported moving-orbit source defines
`s102_zf P X ζ u f` as `Real.sqrt N * (pair (empirical (X u.toNNReal ζ)) f -
pair (meanEmpirical (P.map (X u.toNNReal))) f`.  The source definition of
`r2QuadField s μ P X u ζ f` is `N` times pair energy against the commutator
kernel, minus its `P`-expectation.  Thus the latter is the positive centered
field; the negative `Real.sqrt N⁻¹` is outside it in
`fp81s21_moving_orbit_zeta`.

This file proves only the deterministic upper-integral majorant used before
any probabilistic integration.  It makes no assertion about measurability of
a path supremum.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace HRS.Fp81.S21

/-- A path given by an interval integral is bounded pointwise by its initial
value plus the upper integral of the absolute derivative on the whole window.
The conclusion is an upper-integral statement, so no measurability of the
supremum is needed. -/
theorem fp81s21_window_pathwise_lintegral_bound
    (b H c : ℝ) (g : ℝ → ℝ) (hH : 0 ≤ H)
    (hg : IntervalIntegrable g volume b (b + H)) :
    (⨆ t : Set.Icc b (b + H),
      ENNReal.ofReal |c + ∫ s in b..(t : ℝ), g s ∂volume|) ≤
      ENNReal.ofReal |c| +
        ∫⁻ s in Set.Icc b (b + H), ENNReal.ofReal |g s| ∂volume := by
  have hEnd : b ≤ b + H := by linarith
  have hgabs : IntervalIntegrable (fun s => |g s|) volume b (b + H) := by
    exact hg.norm
  have hgIcc : IntegrableOn (fun s => |g s|) (Icc b (b + H)) volume := by
    exact (intervalIntegrable_iff_integrableOn_Icc_of_le hEnd).1 hgabs
  have htotal :
      ENNReal.ofReal (∫ s in b..(b + H), |g s| ∂volume) =
        ∫⁻ s in Set.Icc b (b + H), ENNReal.ofReal |g s| ∂volume := by
    have hIcc := ofReal_integral_eq_lintegral_ofReal hgIcc
      (Filter.Eventually.of_forall fun s => abs_nonneg (g s))
    have hIccEq :
        (∫ s in Set.Icc b (b + H), |g s| ∂volume) =
          ∫ s in b..(b + H), |g s| ∂volume := by
      rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hEnd]
    rw [hIccEq] at hIcc
    exact hIcc
  refine iSup_le fun t => ?_
  have hbt : b ≤ (t : ℝ) ∧ (t : ℝ) ≤ b + H := t.2
  have hgt : IntervalIntegrable g volume b (t : ℝ) := by
    apply (intervalIntegrable_iff_integrableOn_Icc_of_le hbt.1).2
    exact ((intervalIntegrable_iff_integrableOn_Icc_of_le hEnd).1 hg).mono_set
      (Icc_subset_Icc le_rfl hbt.2)
  have hAbs := intervalIntegral.abs_integral_le_integral_abs
    (f := g) (μ := volume) (a := b) (b := (t : ℝ)) hbt.1
  have hMono := intervalIntegral.integral_mono_interval le_rfl hbt.1 hbt.2
    (Filter.Eventually.of_forall fun s => abs_nonneg (g s)) hgabs
  have hDeriv :
      |∫ s in b..(t : ℝ), g s ∂volume| ≤
        ∫ s in b..(b + H), |g s| ∂volume := hAbs.trans hMono
  have hPath :
      |c + ∫ s in b..(t : ℝ), g s ∂volume| ≤
        |c| + ∫ s in b..(b + H), |g s| ∂volume := by
    exact (abs_add_le c _).trans (add_le_add_right hDeriv |c|)
  have htotalNonneg : 0 ≤ ∫ s in b..(b + H), |g s| ∂volume :=
    intervalIntegral.integral_nonneg hEnd (fun s hs => abs_nonneg (g s))
  calc
    ENNReal.ofReal |c + ∫ s in b..(t : ℝ), g s ∂volume|
        ≤ ENNReal.ofReal (|c| + ∫ s in b..(b + H), |g s| ∂volume) :=
          ENNReal.ofReal_le_ofReal hPath
    _ = ENNReal.ofReal |c| +
          ENNReal.ofReal (∫ s in b..(b + H), |g s| ∂volume) :=
          ENNReal.ofReal_add (abs_nonneg c) htotalNonneg
    _ = ENNReal.ofReal |c| +
          ∫⁻ s in Set.Icc b (b + H), ENNReal.ofReal |g s| ∂volume := by rw [htotal]

#print axioms fp81s21_window_pathwise_lintegral_bound

end HRS.Fp81.S21

end
