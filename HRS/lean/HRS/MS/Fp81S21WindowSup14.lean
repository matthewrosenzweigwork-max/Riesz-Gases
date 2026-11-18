import HRS.MS.Fp81S21WindowSup13

/-!
# HRS S2.1(iii), SOL40 packet 9d: abstract derivative-to-supremum adapter

The source definitions used for the intended drift application are
`r2QuadField s μ P X v ω f = N * (pairEnergy (commutatorKernel d s
  (fun x => gradient f x)) (X v ω) μ - E_P pairEnergy(...))` and
`D(t) = ∫_b^t r2QuadField ... v ω (U^{v,t} φ) dv`.  The moving terminal-time
derivative would be `q(s,ω) + ∫_b^s k(v,s,ω) dv`.  This file proves the
remaining scalar path-supremum step conditional on a uniform sixth-moment
bound for that derivative.  It makes no claim that the moving quadratic
functional has yet been shown to satisfy the required FTC or measurability
conditions.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace HRS.Fp81.S21

/-- A uniform L⁶ bound for a path derivative gives the shifted-window
supremum bound for its time integral.  The supremum stays inside the upper
integral, so no path-supremum measurability is assumed. -/
theorem fp81s21_window_integral_sup_sixth_of_derivative_bound
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (b H K : ℝ) (hH : 0 ≤ H) (hK : 0 ≤ K)
    (g : ℝ → Ω → ℝ)
    (hg : Measurable (Function.uncurry g))
    (hgi : ∀ ω, IntervalIntegrable (fun s => g s ω) volume b (b + H))
    (hMoment : ∀ s ∈ Icc b (b + H),
      (∫⁻ ω, (ENNReal.ofReal |g s ω|) ^ (6 : ℝ) ∂P) ^ (1 / 6 : ℝ) ≤
        ENNReal.ofReal K) :
    (∫⁻ ω, (⨆ t : Icc b (b + H),
      ENNReal.ofReal |∫ s in b..(t : ℝ), g s ω ∂volume|) ^ (6 : ℝ) ∂P) ^
        (1 / 6 : ℝ) ≤ ENNReal.ofReal (H * K) := by
  classical
  have hAbstract := fp81s21_window_lintegral_sup_bound
    P b H (fun _ : Ω => (0 : ℝ)) g measurable_const hg hH hgi
  have hIntegral :
      ∫⁻ s in Icc b (b + H),
        (∫⁻ ω, (ENNReal.ofReal |g s ω|) ^ (6 : ℝ) ∂P) ^
          (1 / 6 : ℝ) ∂volume ≤ ENNReal.ofReal (H * K) := by
    calc
      _ ≤ ∫⁻ s in Icc b (b + H), ENNReal.ofReal K ∂volume := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
        exact hMoment s hs
      _ = ENNReal.ofReal (H * K) := by
        rw [lintegral_const]
        have hVol : volume (Icc b (b + H)) = ENNReal.ofReal H := by
          rw [Real.volume_Icc]
          simp [hH]
        rw [Measure.restrict_apply_univ, hVol]
        rw [← ENNReal.ofReal_mul hK]
        congr 1
        ring
  calc
    _ ≤ (∫⁻ ω, (ENNReal.ofReal |(0 : ℝ)|) ^ (6 : ℝ) ∂P) ^ (1 / 6 : ℝ) +
        ∫⁻ s in Icc b (b + H),
          (∫⁻ ω, (ENNReal.ofReal |g s ω|) ^ (6 : ℝ) ∂P) ^
            (1 / 6 : ℝ) ∂volume := by
          simpa using hAbstract
    _ = ∫⁻ s in Icc b (b + H),
          (∫⁻ ω, (ENNReal.ofReal |g s ω|) ^ (6 : ℝ) ∂P) ^
            (1 / 6 : ℝ) ∂volume := by simp
    _ ≤ ENNReal.ofReal (H * K) := hIntegral

#print axioms fp81s21_window_integral_sup_sixth_of_derivative_bound

end HRS.Fp81.S21

end
