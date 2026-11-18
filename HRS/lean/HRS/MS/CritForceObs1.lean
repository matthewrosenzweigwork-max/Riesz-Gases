import HRS.MS.CritForceSobolev

/-!
# S8.2 NormalForm packet O01: anchored observed-time supremum

For a process `Y` with `Y_t = Y_0 + ∫_0^t G` almost surely, `E sup_{t ≤ T} |Y_t|² ≤ 2 E|Y_0|² + 2T E∫_0^T |G|²`,
and the supremum is almost everywhere measurable (continuity in `t` reduces it to a countable
dense set of times).  Statement of Pro packet S82.O01 (`S8.2-Observed.lean`), with the
definition `scalarSupSq` renamed `s82n_scalarSupSq`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.S82N

open HRS HRS.Whole HRS.MS.S82BD

/-- `E sup_{t ∈ [0,T]} ‖Y t‖²` (lower integral). -/
def s82n_scalarSupSq {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) (T : ℝ) (Y : ℝ → Omega → ℝ) : ℝ≥0∞ :=
  ∫⁻ w, (⨆ t : Set.Icc (0 : ℝ) T, ‖Y t w‖ₑ) ^ 2 ∂P

lemma s82n_iSup_enorm_eq {Omega : Type*} (T : ℝ) (Y : ℝ → Omega → ℝ) (w : Omega) :
    (⨆ t : Set.Icc (0 : ℝ) T, ‖Y t w‖ₑ) = ⨆ t : Set.Icc (0 : ℝ) T, ENNReal.ofReal |Y t w| := by
  refine iSup_congr fun t => ?_
  rw [Real.enorm_eq_ofReal_abs]

/-- The primitive is continuous on the subtype `[0,T]`. -/
lemma s82n_primitive_continuous (T : ℝ) (g : ℝ → ℝ) (hg : IntegrableOn g (Set.Icc 0 T)) (c : ℝ) :
    Continuous (fun t : Set.Icc (0 : ℝ) T => ‖c + ∫ u in Set.Icc 0 (t : ℝ), g u‖ₑ) := by
  have hT : (0 : ℝ) ≤ T ∨ T < 0 := le_or_gt 0 T
  have hcont : ContinuousOn (fun t : ℝ => ∫ u in (0 : ℝ)..t, g u) (Set.Icc 0 T) := by
    rcases hT with hT | hT
    · have := intervalIntegral.continuousOn_primitive_interval (a := 0) (b := T) (μ := volume)
        (f := g) (by rwa [Set.uIcc_of_le hT])
      simpa [Set.uIcc_of_le hT] using this
    · simp [Set.Icc_eq_empty_of_lt hT]
  have h1 : Continuous (fun t : Set.Icc (0 : ℝ) T => ∫ u in (0 : ℝ)..(t : ℝ), g u) :=
    hcont.comp_continuous continuous_subtype_val fun t => t.2
  have h2 : (fun t : Set.Icc (0 : ℝ) T => c + ∫ u in Set.Icc 0 (t : ℝ), g u) =
      fun t : Set.Icc (0 : ℝ) T => c + ∫ u in (0 : ℝ)..(t : ℝ), g u := by
    funext t
    rw [s82_Icc_integral_eq g t.2.1]
  have h3 : Continuous (fun t : Set.Icc (0 : ℝ) T => c + ∫ u in Set.Icc 0 (t : ℝ), g u) := by
    rw [h2]; exact continuous_const.add h1
  exact h3.enorm

/-- Sample-wise: the supremum of an a.s. primitive is the supremum over a dense countable set. -/
theorem s82n_anchored_observed_sup
    {Omega : Type*} [MeasurableSpace Omega] (P : Measure Omega) [IsProbabilityMeasure P]
    (T : ℝ) (hT : 0 < T) (Y G : ℝ → Omega → ℝ)
    (hY0 : MemLp (Y 0) 2 P)
    (hG : MemLp (fun p : ℝ × Omega => G p.1 p.2) 2
      ((volume.restrict (Set.Icc 0 T)).prod P))
    (hFTC : ∀ᵐ w ∂P, IntegrableOn (fun t => G t w) (Set.Icc 0 T) ∧
      ∀ t ∈ Set.Icc 0 T, Y t w = Y 0 w + ∫ r in Set.Icc 0 t, G r w) :
    AEMeasurable (fun w => ⨆ t : Set.Icc (0 : ℝ) T, ‖Y t w‖ₑ) P ∧
      s82n_scalarSupSq P T Y ≤
        2 * (∫⁻ w, ‖Y 0 w‖ₑ ^ 2 ∂P) +
        ENNReal.ofReal (2 * T) *
          ∫⁻ p, ‖G p.1 p.2‖ₑ ^ 2 ∂((volume.restrict (Set.Icc 0 T)).prod P) := by
  set ν : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) T) with hν
  have : IsFiniteMeasure ν := by rw [hν]; infer_instance
  have hGm : AEStronglyMeasurable (fun p : ℝ × Omega => G p.1 p.2) (ν.prod P) :=
    hG.aestronglyMeasurable
  have hY0m : AEMeasurable (Y 0) P := hY0.aestronglyMeasurable.aemeasurable
  -- measurability
  have hmeas : AEMeasurable (fun w => ⨆ t : Set.Icc (0 : ℝ) T, ‖Y t w‖ₑ) P := by
    obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense (Set.Icc (0 : ℝ) T)
    -- each fixed time slice is a.e. measurable
    have hslice : ∀ t : Set.Icc (0 : ℝ) T, AEMeasurable (fun w => Y t w) P := by
      intro t
      have hGt : AEStronglyMeasurable
          (fun p : ℝ × Omega => ({p : ℝ × Omega | p.1 ∈ Set.Icc 0 (t : ℝ)}).indicator
            (fun p => G p.1 p.2) p) (ν.prod P) :=
        hGm.indicator (measurableSet_Icc.preimage measurable_fst)
      have hint : AEStronglyMeasurable
          (fun w => ∫ r, ({p : ℝ × Omega | p.1 ∈ Set.Icc 0 (t : ℝ)}).indicator
            (fun p => G p.1 p.2) (r, w) ∂ν) P :=
        hGt.prod_swap.integral_prod_right'
      have heq : ∀ w, (∫ r, ({p : ℝ × Omega | p.1 ∈ Set.Icc 0 (t : ℝ)}).indicator
            (fun p => G p.1 p.2) (r, w) ∂ν) = ∫ r in Set.Icc 0 (t : ℝ), G r w := by
        intro w
        have : (fun r => ({p : ℝ × Omega | p.1 ∈ Set.Icc 0 (t : ℝ)}).indicator
            (fun p => G p.1 p.2) (r, w)) =
            (Set.Icc (0 : ℝ) t).indicator (fun r => G r w) := by
          funext r
          by_cases hr : r ∈ Set.Icc (0 : ℝ) t
          · rw [Set.indicator_of_mem (show ((r, w) : ℝ × Omega) ∈
              {p : ℝ × Omega | p.1 ∈ Set.Icc 0 (t : ℝ)} from hr), Set.indicator_of_mem hr]
          · rw [Set.indicator_of_notMem (show ((r, w) : ℝ × Omega) ∉
              {p : ℝ × Omega | p.1 ∈ Set.Icc 0 (t : ℝ)} from hr), Set.indicator_of_notMem hr]
        rw [this, integral_indicator measurableSet_Icc, hν, Measure.restrict_restrict measurableSet_Icc,
          Set.inter_eq_left.mpr (Set.Icc_subset_Icc_right t.2.2)]
      have hmeasZ : AEMeasurable (fun w => Y 0 w + ∫ r in Set.Icc 0 (t : ℝ), G r w) P := by
        refine hY0m.add ?_
        have := hint.aemeasurable
        simpa only [heq] using this
      refine hmeasZ.congr ?_
      filter_upwards [hFTC] with w hw
      exact (hw.2 t t.2).symm
    have : Countable D := hDc.to_subtype
    have hsupD : AEMeasurable (fun w => ⨆ t : D, ‖Y (t : Set.Icc (0 : ℝ) T) w‖ₑ) P :=
      AEMeasurable.iSup fun t => (hslice t).enorm
    refine hsupD.congr ?_
    filter_upwards [hFTC] with w hw
    have hcont := s82n_primitive_continuous T (fun r => G r w) hw.1 (Y 0 w)
    have hZ := hDd.ciSup' hcont
    calc (⨆ t : D, ‖Y (t : Set.Icc (0 : ℝ) T) w‖ₑ)
        = ⨆ t : D, ‖Y 0 w + ∫ u in Set.Icc 0 ((t : Set.Icc (0 : ℝ) T) : ℝ), G u w‖ₑ :=
          iSup_congr fun t => by rw [hw.2 _ t.1.2]
      _ = ⨆ t : Set.Icc (0 : ℝ) T, ‖Y 0 w + ∫ u in Set.Icc 0 (t : ℝ), G u w‖ₑ := hZ
      _ = ⨆ t : Set.Icc (0 : ℝ) T, ‖Y t w‖ₑ :=
          iSup_congr fun t => by rw [hw.2 _ t.2]
  refine ⟨hmeas, ?_⟩
  -- the estimate
  have hGm2 : AEMeasurable (fun p : ℝ × Omega => ‖G p.1 p.2‖ₑ ^ 2) (ν.prod P) :=
    (hGm.aemeasurable.enorm).pow_const 2
  have hpt : ∀ᵐ w ∂P, (⨆ t : Set.Icc (0 : ℝ) T, ‖Y t w‖ₑ) ^ 2 ≤
      2 * ‖Y 0 w‖ₑ ^ 2 + ENNReal.ofReal (2 * T) * ∫⁻ r, ‖G r w‖ₑ ^ 2 ∂ν := by
    filter_upwards [hFTC] with w hw
    have h := s82_sob_sq_pointwise T hT.le (fun t => Y t w) (fun u => G u w) hw.1 hw.2
      (s := 0) ⟨le_rfl, hT.le⟩
    rw [s82n_iSup_enorm_eq]
    have e1 : ENNReal.ofReal (Y 0 w ^ 2) = ‖Y 0 w‖ₑ ^ 2 := by
      rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
    have e2 : ∀ r, ENNReal.ofReal (G r w ^ 2) = ‖G r w‖ₑ ^ 2 := fun r => by
      rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
    simp only [e1, e2] at h
    refine h.trans (le_of_eq ?_)
    rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
    simp only [hν]
    rw [ENNReal.ofReal_ofNat]
    ring
  unfold s82n_scalarSupSq
  calc ∫⁻ w, (⨆ t : Set.Icc (0 : ℝ) T, ‖Y t w‖ₑ) ^ 2 ∂P
      ≤ ∫⁻ w, (2 * ‖Y 0 w‖ₑ ^ 2 + ENNReal.ofReal (2 * T) * ∫⁻ r, ‖G r w‖ₑ ^ 2 ∂ν) ∂P :=
        lintegral_mono_ae hpt
    _ = 2 * (∫⁻ w, ‖Y 0 w‖ₑ ^ 2 ∂P) +
          ENNReal.ofReal (2 * T) * ∫⁻ w, ∫⁻ r, ‖G r w‖ₑ ^ 2 ∂ν ∂P := by
        have hA : AEMeasurable (fun w => ‖Y 0 w‖ₑ ^ 2) P := hY0m.enorm.pow_const 2
        have hB : AEMeasurable (fun w => ∫⁻ r, ‖G r w‖ₑ ^ 2 ∂ν) P := by
          have := hGm2.prod_swap.lintegral_prod_right'
          exact this
        rw [lintegral_add_left' (hA.const_mul _), lintegral_const_mul'' _ hA,
          lintegral_const_mul'' _ hB]
    _ = _ := by
        congr 2
        rw [lintegral_prod_symm _ hGm2]

end HRS.MS.S82N
