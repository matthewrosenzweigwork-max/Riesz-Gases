import HRS.MS.Fp81S21WindowSup52

/-! Window-square sixth-root estimate for a frozen-source drift. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal
namespace HRS.Fp81.S21

/-- The measurable baseline and two-time derivative fields give the
`H + H²` sixth-root estimate for any drift obeying the frozen-source FTC. -/
theorem fp81s21_window_frozen_drift_sup_of_slices
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (b H K : ℝ) (hH : 0 ≤ H) (hK : 0 ≤ K)
    (A : ℝ → ℝ → Ω → ℝ) (q : ℝ → Ω → ℝ) (k : ℝ × ℝ → Ω → ℝ)
    (hq : Measurable (Function.uncurry q)) (hk : Measurable (Function.uncurry k))
    (hRep : ∀ᵐ ω ∂P, ∀ v t, b ≤ v → v ≤ t → t ≤ b + H →
      A v t ω = q v ω + ∫ u in (0 : ℝ)..(t - v), k (v, v + u) ω)
    (hqBound : ∀ v, (∫⁻ ω, ENNReal.ofReal |q v ω| ^ (6 : ℝ) ∂P) ^
      (1 / 6 : ℝ) ≤ ENNReal.ofReal K)
    (hkBound : ∀ z, (∫⁻ ω, ENNReal.ofReal |k z ω| ^ (6 : ℝ) ∂P) ^
      (1 / 6 : ℝ) ≤ ENNReal.ofReal K) :
    (∫⁻ ω, (⨆ t : Icc b (b + H),
      ENNReal.ofReal |∫ v in b..(t : ℝ), A v t ω|) ^ (6 : ℝ) ∂P) ^
        (1 / 6 : ℝ) ≤ ENNReal.ofReal (K * (H + H ^ 2)) := by
  let ν : Measure ℝ := volume.restrict (Icc b (b + H))
  let qa : ℝ → Ω → ℝ≥0∞ := fun v ω => ENNReal.ofReal |q v ω|
  let ka : (ℝ × ℝ) → Ω → ℝ≥0∞ := fun z ω => ENNReal.ofReal |k z ω|
  have hqa : Measurable (Function.uncurry qa) :=
    ENNReal.measurable_ofReal.comp (measurable_abs.comp hq)
  have hka : Measurable (Function.uncurry ka) :=
    ENNReal.measurable_ofReal.comp (measurable_abs.comp hk)
  let Z : Ω → ℝ≥0∞ := fun ω => ⨆ t : Icc b (b + H),
    ENNReal.ofReal |∫ v in b..(t : ℝ), A v t ω|
  have hDom : ∀ᵐ ω ∂P, Z ω ≤ (∫⁻ v, qa v ω ∂ν) +
      ∫⁻ z, ka z ω ∂(ν.prod ν) := by
    filter_upwards [hRep] with ω hω
    have hqm : Measurable (fun v => q v ω) :=
      hq.comp (measurable_id.prodMk measurable_const)
    have hkm : Measurable (Function.uncurry (fun v s => k (v, s) ω)) := by
      exact hk.comp (measurable_id.prodMk measurable_const)
    exact fp81s21_window_frozen_drift_majorant b (b + H) (by linarith)
      (fun v t => A v t ω) (fun v => q v ω) (fun v s => k (v, s) ω) hqm hkm hω
  have hSix := fp81s21_two_lintegral_majorant_six_ae P ν (ν.prod ν)
    qa ka hqa hka (ENNReal.ofReal K) hqBound hkBound Z hDom
  have hVol : ν Set.univ = ENNReal.ofReal H := by
    rw [Measure.restrict_apply_univ, Real.volume_Icc]
    simp [hH]
  have hVol2 : (ν.prod ν) Set.univ = ENNReal.ofReal (H ^ 2) := by
    rw [← Set.univ_prod_univ, Measure.prod_prod, hVol]
    rw [← ENNReal.ofReal_mul hH]
    congr 1
    ring
  calc
    _ ≤ ν Set.univ * ENNReal.ofReal K + (ν.prod ν) Set.univ * ENNReal.ofReal K := hSix
    _ = ENNReal.ofReal (K * (H + H ^ 2)) := by
      rw [hVol, hVol2, ← ENNReal.ofReal_mul hH, ← ENNReal.ofReal_mul (sq_nonneg H),
        ← ENNReal.ofReal_add (mul_nonneg hH hK) (mul_nonneg (sq_nonneg H) hK)]
      congr 1
      ring

#print axioms fp81s21_window_frozen_drift_sup_of_slices
end HRS.Fp81.S21
end
