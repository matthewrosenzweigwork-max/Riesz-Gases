import HRS.Commutator.Torus.TSAMPAux26

/-!
# T-SAMP helpers, part 27: a kernel with a power profile lies in `L^q`
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform

namespace HRS.Commutator.TorusNote

open HRS

variable {d : ℕ}

theorem tsamp_memLp_profile (hd : 1 ≤ d) {q : ℝ} (hq1 : 1 < q) {a γ C Cm : ℝ}
    (haq : -(d : ℝ) < a * q) (hC : 0 ≤ C) (hCm : 0 ≤ Cm)
    {η : ℝ} (hη : 0 < η) {k : Torus d → ℝ} (hkm : Measurable k)
    (hnear : ∀ x : Torus d, x ≠ 0 → KernelGrad.tdist x 0 ≤ η →
      |k x| ≤ C * η ^ (γ - d - a) * KernelGrad.tdist x 0 ^ a)
    (hfar : ∀ x : Torus d, η ≤ KernelGrad.tdist x 0 →
      |k x| ≤ Cm * η ^ (γ - d + ((d + 1 : ℕ) : ℝ)) * KernelGrad.tdist x 0 ^ (-((d + 1 : ℕ) : ℝ))) :
    MemLp k (ENNReal.ofReal q) volume := by
  have hq0 : 0 < q := by linarith
  set M : ℕ := d + 1 with hM
  have htd : Measurable fun z : Torus d => KernelGrad.tdist z 0 := tsamp_measurable_tdist 0
  set kn : Torus d → ℝ≥0∞ := fun z =>
    if 0 < KernelGrad.tdist z 0 ∧ KernelGrad.tdist z 0 < η then ENNReal.ofReal |k z| else 0 with hkn
  set kf : Torus d → ℝ≥0∞ := fun z => if η ≤ KernelGrad.tdist z 0 then ENNReal.ofReal |k z| else 0 with hkf
  have hknm : Measurable kn :=
    Measurable.ite ((measurableSet_lt measurable_const htd).inter (measurableSet_lt htd measurable_const))
      (ENNReal.measurable_ofReal.comp hkm.abs) measurable_const
  have hkfm : Measurable kf :=
    Measurable.ite (measurableSet_le measurable_const htd)
      (ENNReal.measurable_ofReal.comp hkm.abs) measurable_const
  have hsplit : ∀ z : Torus d, z ≠ 0 → ENNReal.ofReal |k z| ≤ kn z + kf z := by
    intro z hz
    have hpos : 0 < KernelGrad.tdist z 0 := text_tdist_pos hz
    by_cases h : KernelGrad.tdist z 0 < η
    · simp only [hkn, hkf, if_pos (And.intro hpos h), if_neg (not_le.2 h), add_zero, le_refl]
    · simp only [hkn, hkf, if_neg (fun hh : 0 < KernelGrad.tdist z 0 ∧ KernelGrad.tdist z 0 < η => h hh.2),
        if_pos (not_lt.1 h), zero_add, le_refl]
  set c : ℝ := C * η ^ (γ - d - a) with hc
  have hc0 : 0 ≤ c := by positivity
  have hNq : ∫⁻ z, kn z ^ q ≤ ENNReal.ofReal (c ^ q * η ^ (a * q) * η ^ d * tsampIa d (a * q)) := by
    refine le_trans (lintegral_mono fun z => ?_) (tsamp_near_lintegral hd hη hq0 haq hc0)
    refine ENNReal.rpow_le_rpow ?_ hq0.le
    simp only [hkn]
    by_cases h : 0 < KernelGrad.tdist z 0 ∧ KernelGrad.tdist z 0 < η
    · rw [if_pos h, if_pos h.2]
      have hz : z ≠ 0 := by
        intro hz0; rw [hz0] at h
        simp [CoercAux.tdist_self] at h
      exact ENNReal.ofReal_le_ofReal (hnear z hz h.2.le)
    · rw [if_neg h]; exact zero_le
  set B0 : ℝ := Cm * η ^ (γ - d + (M : ℝ)) * η ^ (-(M : ℝ)) with hB0
  have hB00 : 0 ≤ B0 := by positivity
  have hkfb : ∀ z, kf z ≤ ENNReal.ofReal B0 := by
    intro z
    simp only [hkf]
    by_cases h : η ≤ KernelGrad.tdist z 0
    · rw [if_pos h]
      refine ENNReal.ofReal_le_ofReal ((hfar z h).trans ?_)
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      exact Real.rpow_le_rpow_of_nonpos hη h (by
        have : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
        linarith)
    · rw [if_neg h]; exact zero_le
  have hfinq : ∫⁻ z : Torus d, kf z ^ q ≤ ENNReal.ofReal B0 ^ q := by
    calc ∫⁻ z : Torus d, kf z ^ q ≤ ∫⁻ z : Torus d, ENNReal.ofReal B0 ^ q :=
          lintegral_mono fun z => ENNReal.rpow_le_rpow (hkfb z) hq0.le
      _ = ENNReal.ofReal B0 ^ q := by simp
  have hint : ∫⁻ z : Torus d, ‖k z‖ₑ ^ q < ⊤ := by
    have h1 : ∫⁻ z : Torus d, ‖k z‖ₑ ^ q ≤ ∫⁻ z : Torus d, 2 ^ (q - 1) * (kn z ^ q + kf z ^ q) := by
      refine lintegral_mono_ae ?_
      filter_upwards [text_ae_ne hd (0 : Torus d)] with z hz
      have hz' : z ≠ 0 := hz
      calc ‖k z‖ₑ ^ q = ENNReal.ofReal |k z| ^ q := by rw [Real.enorm_eq_ofReal_abs]
        _ ≤ (kn z + kf z) ^ q := ENNReal.rpow_le_rpow (hsplit z hz') hq0.le
        _ ≤ 2 ^ (q - 1) * (kn z ^ q + kf z ^ q) :=
            ENNReal.rpow_add_le_mul_rpow_add_rpow _ _ hq1.le
    refine lt_of_le_of_lt h1 ?_
    rw [lintegral_const_mul' _ _ (by simp), lintegral_add_left (hknm.pow_const q)]
    refine ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg (by linarith) (by simp)) (ENNReal.add_lt_top.2 ⟨?_, ?_⟩)
    · exact lt_of_le_of_lt hNq ENNReal.ofReal_lt_top
    · exact lt_of_le_of_lt hfinq (ENNReal.rpow_lt_top_of_nonneg hq0.le ENNReal.ofReal_ne_top)
  rw [memLp_iff, eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_pos.2 hq0).ne'
    ENNReal.ofReal_ne_top hkm.aestronglyMeasurable, ENNReal.toReal_ofReal hq0.le]
  exact ENNReal.rpow_lt_top_of_nonneg (by positivity) hint.ne

end HRS.Commutator.TorusNote
