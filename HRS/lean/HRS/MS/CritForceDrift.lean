import HRS.MS.CritForceSobolev

/-!
# S8.2 (core X, step "deterministic integrals controlled by their endpoint bounds")

`s82_drift_L2`: if `Φ_r ≥ 0` has `E Φ_r² ≤ σ²` for every `r ∈ [lo,hi]` (stationarity gives this for
every moment-type statistic along the stationary process) then
`E (∫_{lo}^{hi} Φ_r dr)² ≤ (hi-lo)² σ²`.  Cauchy-Schwarz in time plus Tonelli; no measurability of
any supremum is used.  `s82_drift_sup_L2` states the consequence for the observed-time supremum of an
integral dominated by `κ Φ`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.S82BD

open HRS HRS.Whole

/-- Cauchy-Schwarz on `[lo,hi]` in `ℝ≥0∞`. -/
lemma s82_cs_Icc (lo hi : ℝ) (h : ℝ → ℝ≥0∞)
    (hm : AEMeasurable h (volume.restrict (Set.Icc lo hi))) :
    (∫⁻ u in Set.Icc lo hi, h u) ^ 2 ≤
      ENNReal.ofReal (hi - lo) * ∫⁻ u in Set.Icc lo hi, (h u) ^ 2 := by
  have hHC : (2 : ℝ).HolderConjugate 2 := Real.HolderConjugate.two_two
  have key := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume.restrict (Set.Icc lo hi)) hHC
    (f := fun _ => (1 : ℝ≥0∞)) (g := h) aemeasurable_const hm
  have e1 : (∫⁻ u in Set.Icc lo hi, (((fun _ => (1 : ℝ≥0∞)) * h : ℝ → ℝ≥0∞) u)) =
      ∫⁻ u in Set.Icc lo hi, h u := by simp
  have e2 : (∫⁻ u in Set.Icc lo hi, (1 : ℝ≥0∞) ^ (2 : ℝ)) = ENNReal.ofReal (hi - lo) := by
    simp
  rw [e1, e2] at key
  calc (∫⁻ u in Set.Icc lo hi, h u) ^ 2
      ≤ ((ENNReal.ofReal (hi - lo)) ^ (1 / 2 : ℝ) *
          (∫⁻ a in Set.Icc lo hi, h a ^ (2 : ℝ)) ^ (1 / 2 : ℝ)) ^ 2 := by
        refine pow_le_pow_left' ?_ 2
        simpa using key
    _ = ENNReal.ofReal (hi - lo) * ∫⁻ u in Set.Icc lo hi, (h u) ^ 2 := by
        rw [mul_pow, s82_sqrt_sq, s82_sqrt_sq]
        simp only [ENNReal.rpow_two]

theorem s82_drift_L2 {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (lo hi : ℝ) (Φ : ℝ → Ω → ℝ≥0∞)
    (hΦm : AEMeasurable (fun p : Ω × ℝ => Φ p.2 p.1) (P.prod (volume.restrict (Set.Icc lo hi))))
    (σ : ℝ) (hσ : ∀ r ∈ Set.Icc lo hi, ∫⁻ ζ, (Φ r ζ) ^ 2 ∂P ≤ ENNReal.ofReal σ ^ 2) :
    ∫⁻ ζ, (∫⁻ r in Set.Icc lo hi, Φ r ζ) ^ 2 ∂P ≤
      ENNReal.ofReal (hi - lo) ^ 2 * ENNReal.ofReal σ ^ 2 := by
  have hae : ∀ᵐ ζ ∂P, AEMeasurable (fun r => Φ r ζ) (volume.restrict (Set.Icc lo hi)) :=
    by
    obtain ⟨g, hg, hfg⟩ := hΦm
    filter_upwards [Measure.ae_ae_of_ae_prod hfg] with ζ hζ
    exact ⟨fun r => g (ζ, r), hg.comp measurable_prodMk_left, hζ⟩
  have hsq : AEMeasurable (fun p : Ω × ℝ => (Φ p.2 p.1) ^ 2)
      (P.prod (volume.restrict (Set.Icc lo hi))) := hΦm.pow_const 2
  calc ∫⁻ ζ, (∫⁻ r in Set.Icc lo hi, Φ r ζ) ^ 2 ∂P
      ≤ ∫⁻ ζ, (ENNReal.ofReal (hi - lo) * ∫⁻ r in Set.Icc lo hi, (Φ r ζ) ^ 2) ∂P := by
        refine lintegral_mono_ae (hae.mono fun ζ hζ => ?_)
        exact s82_cs_Icc lo hi _ hζ
    _ = ENNReal.ofReal (hi - lo) * ∫⁻ ζ, (∫⁻ r in Set.Icc lo hi, (Φ r ζ) ^ 2) ∂P := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ = ENNReal.ofReal (hi - lo) * ∫⁻ r in Set.Icc lo hi, (∫⁻ ζ, (Φ r ζ) ^ 2 ∂P) := by
        rw [lintegral_lintegral_swap (f := fun ζ r => (Φ r ζ) ^ 2) hsq]
    _ ≤ ENNReal.ofReal (hi - lo) * ∫⁻ r in Set.Icc lo hi, ENNReal.ofReal σ ^ 2 := by
        exact mul_le_mul' le_rfl (setLIntegral_mono' measurableSet_Icc fun r hr => hσ r hr)
    _ = ENNReal.ofReal (hi - lo) ^ 2 * ENNReal.ofReal σ ^ 2 := by
        rw [setLIntegral_const, Real.volume_Icc]
        ring

/-- The observed-time supremum of an integral dominated (uniformly in the observed time) by
`∫_{lo}^{hi} Φ_r dr`. -/
theorem s82_drift_sup_L2 {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (lo hi T : ℝ) (Φ : ℝ → Ω → ℝ≥0∞) (I : ℝ → Ω → ℝ)
    (hΦm : AEMeasurable (fun p : Ω × ℝ => Φ p.2 p.1) (P.prod (volume.restrict (Set.Icc lo hi))))
    (σ : ℝ) (hσ : ∀ r ∈ Set.Icc lo hi, ∫⁻ ζ, (Φ r ζ) ^ 2 ∂P ≤ ENNReal.ofReal σ ^ 2)
    (hdom : ∀ᵐ ζ ∂P, ∀ t : Set.Icc (0 : ℝ) T,
      ENNReal.ofReal |I t ζ| ≤ ∫⁻ r in Set.Icc lo hi, Φ r ζ) :
    ∫⁻ ζ, (⨆ t : Set.Icc (0 : ℝ) T, ENNReal.ofReal |I t ζ|) ^ 2 ∂P ≤
      ENNReal.ofReal (hi - lo) ^ 2 * ENNReal.ofReal σ ^ 2 := by
  refine le_trans (lintegral_mono_ae (hdom.mono fun ζ hζ => ?_)) (s82_drift_L2 P lo hi Φ hΦm σ hσ)
  exact pow_le_pow_left' (iSup_le hζ) 2

end HRS.MS.S82BD
