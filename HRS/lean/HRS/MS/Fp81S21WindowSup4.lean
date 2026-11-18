import HRS.MS.Fp81S21WindowSup3

/-!
# HRS S2.1(iii), SOL40 packet 9d: abstract shifted-window supremum

The compiled source identities are as recorded in `Fp81S21WindowSup.lean`:
the centered linear field is `s102_zf`, the positive centered quadratic field
is `r2QuadField`, and the moving orbit puts `−(√N)⁻¹` outside that quadratic
field. The observation-window orbit envelope in
`fp81s21_window_Bpos` already includes the oscillator amplitude.

This file combines the deterministic pathwise upper-integral estimate with
the direct scalar ENNReal L⁶ Minkowski theorem. The path supremum remains an
upper integral and is not asserted to be measurable.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace HRS.Fp81.S21

/-- L⁶ upper-integral bound for a real path represented by its initial value
plus an interval integral. Only the initial value and derivative need to be
measurable; no measurability of the path supremum is required. -/
theorem fp81s21_window_lintegral_sup_bound
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (b H : ℝ) (c : Ω → ℝ) (g : ℝ → Ω → ℝ)
    (hc : Measurable c)
    (hg : Measurable (Function.uncurry g))
    (hH : 0 ≤ H)
    (hgi : ∀ ω, IntervalIntegrable (fun s => g s ω) volume b (b + H)) :
    (∫⁻ ω, (⨆ t : Icc b (b + H),
      ENNReal.ofReal |c ω + ∫ s in b..(t : ℝ), g s ω ∂volume|) ^ (6 : ℝ) ∂P) ^
        (1 / 6 : ℝ) ≤
      (∫⁻ ω, (ENNReal.ofReal |c ω|) ^ (6 : ℝ) ∂P) ^ (1 / 6 : ℝ) +
        ∫⁻ s in Icc b (b + H),
          (∫⁻ ω, (ENNReal.ofReal |g s ω|) ^ (6 : ℝ) ∂P) ^ (1 / 6 : ℝ) ∂volume := by
  classical
  let C : Ω → ℝ≥0∞ := fun ω => ENNReal.ofReal |c ω|
  let K : Ω → ℝ≥0∞ := fun ω =>
    ∫⁻ s in Icc b (b + H), ENNReal.ofReal |g s ω| ∂volume
  let S : Ω → ℝ≥0∞ := fun ω => ⨆ t : Icc b (b + H),
    ENNReal.ofReal |c ω + ∫ s in b..(t : ℝ), g s ω ∂volume|
  have hCmeas : Measurable C := by
    exact ENNReal.measurable_ofReal.comp (measurable_abs.comp hc)
  have hgAbsJoint : Measurable fun z : Ω × ℝ =>
      ENNReal.ofReal |g z.2 z.1| := by
    exact ENNReal.measurable_ofReal.comp
      (measurable_abs.comp (hg.comp measurable_swap))
  have hKmeas : Measurable K := by
    dsimp [K]
    exact hgAbsJoint.lintegral_prod_right'
  have hPath (ω : Ω) : S ω ≤ C ω + K ω := by
    simpa [S, C, K] using
      fp81s21_window_pathwise_lintegral_bound b H (c ω)
        (fun s => g s ω) hH (hgi ω)
  have hPathPow (ω : Ω) : S ω ^ (6 : ℝ) ≤ (C ω + K ω) ^ (6 : ℝ) :=
    ENNReal.rpow_le_rpow (hPath ω) (by norm_num)
  have hIntegral :
      (∫⁻ ω, S ω ^ (6 : ℝ) ∂P) ≤
        ∫⁻ ω, (C ω + K ω) ^ (6 : ℝ) ∂P := by
    exact lintegral_mono hPathPow
  have hTriangle :
      (∫⁻ ω, (C ω + K ω) ^ (6 : ℝ) ∂P) ^ (1 / 6 : ℝ) ≤
        (∫⁻ ω, C ω ^ (6 : ℝ) ∂P) ^ (1 / 6 : ℝ) +
          (∫⁻ ω, K ω ^ (6 : ℝ) ∂P) ^ (1 / 6 : ℝ) :=
    ENNReal.lintegral_Lp_add_le hCmeas.aemeasurable hKmeas.aemeasurable
      (by norm_num : 1 ≤ (6 : ℝ))
  let gE : ℝ → Ω → ℝ≥0∞ := fun s ω => ENNReal.ofReal |g s ω|
  have hgEJoint : Measurable (Function.uncurry gE) := by
    exact ENNReal.measurable_ofReal.comp
      (measurable_abs.comp hg)
  have hB2 :
      (∫⁻ ω, K ω ^ (6 : ℝ) ∂P) ^ (1 / 6 : ℝ) ≤
        ∫⁻ s in Icc b (b + H),
          (∫⁻ ω, (ENNReal.ofReal |g s ω|) ^ (6 : ℝ) ∂P) ^ (1 / 6 : ℝ) ∂volume := by
    simpa [K, gE, ENNReal.rpow_natCast] using
      (fp81s21_lintegral_minkowski_six P
        (volume.restrict (Icc b (b + H))) gE hgEJoint)
  calc
    (∫⁻ ω, S ω ^ (6 : ℝ) ∂P) ^ (1 / 6 : ℝ) ≤
        (∫⁻ ω, (C ω + K ω) ^ (6 : ℝ) ∂P) ^ (1 / 6 : ℝ) :=
          ENNReal.rpow_le_rpow hIntegral (by norm_num)
    _ ≤ (∫⁻ ω, C ω ^ (6 : ℝ) ∂P) ^ (1 / 6 : ℝ) +
          (∫⁻ ω, K ω ^ (6 : ℝ) ∂P) ^ (1 / 6 : ℝ) := hTriangle
    _ ≤ (∫⁻ ω, C ω ^ (6 : ℝ) ∂P) ^ (1 / 6 : ℝ) +
          ∫⁻ s in Icc b (b + H),
            (∫⁻ ω, (ENNReal.ofReal |g s ω|) ^ (6 : ℝ) ∂P) ^ (1 / 6 : ℝ) ∂volume :=
      add_le_add le_rfl hB2

#print axioms fp81s21_window_lintegral_sup_bound

end HRS.Fp81.S21

end
