import HRS.MS.ShiftFldAux13
import HRS.MS.UniqN3aC

/-!
# S79P: Fubini for the Riesz convolution against a compactly supported test function
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.S79G

open HRS.Whole HRS.MS.UniqT3
open HRS (Euc)

variable {d : ℕ}

theorem s79g_rieszKernel_nonneg {s : ℝ} (hs : 0 < s) (x : Euc d) : 0 ≤ rieszKernel d s x := by
  unfold rieszKernel
  rw [if_neg hs.ne']
  exact Real.rpow_nonneg (norm_nonneg _) _

theorem s79g_rieszKernel_even (s : ℝ) (x : Euc d) : rieszKernel d s (-x) = rieszKernel d s x := by
  unfold rieszKernel
  simp [norm_neg]

/-- Fubini: `∫ φ(x) ∫ g(x-y) h(y) dy dx = ∫ h(y) (g*φ)(y) dy`, with `∫ (1+‖y‖)|h| < ∞`. -/
theorem s79g_fubini {s : ℝ} (hs : 0 < s) (hsd : s < d) {φ h : Euc d → ℝ} (hφ : Continuous φ)
    (hφc : HasCompactSupport φ) (hh : Continuous h)
    (hhi : Integrable (fun y => (1 + ‖y‖) * |h y|)) :
    Integrable (fun p : Euc d × Euc d => φ p.1 * (rieszKernel d s (p.1 - p.2) * h p.2))
      (volume.prod volume) ∧
    Integrable (fun x => φ x * ∫ y, rieszKernel d s (x - y) * h y) ∧
    ∫ x, φ x * ∫ y, rieszKernel d s (x - y) * h y =
      ∫ y, h y * HRS.Whole.convFun (rieszKernel d s) φ y := by
  have hs0 : 0 ≤ s := hs.le
  obtain ⟨R1, hR1⟩ := hφc.isCompact.isBounded.subset_closedBall (0 : Euc d)
  set R0 : ℝ := max R1 0 with hR0
  have hR0n : 0 ≤ R0 := le_max_right _ _
  have hsupp : ∀ t, φ t ≠ 0 → t ∈ closedBall (0 : Euc d) R0 := by
    intro t ht
    have : t ∈ tsupport φ := subset_tsupport _ ht
    have := hR1 this
    exact closedBall_subset_closedBall (le_max_left _ _) this
  obtain ⟨M, hM⟩ := hφc.exists_bound_of_continuous hφ
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  obtain ⟨K, hK0, hK⟩ := HRS.MS.UniqN3a.conv_bound_unif (d := d) hs0 hsd R0 hR0n
  have hg := fun t => s79g_rieszKernel_nonneg (d := d) hs t
  -- the absolute value of φ
  have hK1 := hK (fun t => |φ t|) M hφ.abs
    (fun t ht => hsupp t (fun h0 => ht (by simp [h0])))
    (fun t => by simpa [Real.norm_eq_abs] using hM t)
  have hmeas : AEStronglyMeasurable (fun p : Euc d × Euc d =>
      φ p.1 * (rieszKernel d s (p.1 - p.2) * h p.2)) (volume.prod volume) := by
    refine (hφ.measurable.comp measurable_fst).aestronglyMeasurable.mul ?_
    exact (((g_meas s).comp (measurable_fst.sub measurable_snd)).mul
      (hh.measurable.comp measurable_snd)).aestronglyMeasurable
  -- inner integrals
  have hinner : ∀ y, Integrable (fun x => φ x * (rieszKernel d s (x - y) * h y)) := by
    intro y
    have := (hK φ M hφ hsupp (fun t => by simpa [Real.norm_eq_abs] using hM t) y).1
    have h2 := this.mul_const (h y)
    refine h2.congr (Filter.Eventually.of_forall fun x => ?_)
    simp only
    rw [show x - y = -(y - x) by abel, s79g_rieszKernel_even]
    ring
  have hnorm : ∀ y, ∫ x, ‖φ x * (rieszKernel d s (x - y) * h y)‖ =
      |h y| * HRS.Whole.convFun (rieszKernel d s) (fun t => |φ t|) y := by
    intro y
    unfold HRS.Whole.convFun
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only
    rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (hg _), show x - y = -(y - x) by abel, s79g_rieszKernel_even]
    ring
  have hprod : Integrable (fun p : Euc d × Euc d =>
      φ p.1 * (rieszKernel d s (p.1 - p.2) * h p.2)) (volume.prod volume) := by
    rw [integrable_prod_iff' hmeas]
    refine ⟨Filter.Eventually.of_forall fun y => hinner y, ?_⟩
    have hdom : Integrable (fun y => (M * K) * ((1 + ‖y‖) * |h y|)) := hhi.const_mul _
    refine hdom.mono' ?_ (Filter.Eventually.of_forall fun y => ?_)
    · exact hmeas.norm.prod_swap.integral_prod_right'
    · rw [hnorm y, Real.norm_eq_abs]
      have hc := (hK1 y).2
      have h0 : 0 ≤ |h y| * HRS.Whole.convFun (rieszKernel d s) (fun t => |φ t|) y := by
        rw [← hnorm y]; exact integral_nonneg fun x => norm_nonneg _
      rw [abs_of_nonneg h0]
      calc |h y| * HRS.Whole.convFun (rieszKernel d s) (fun t => |φ t|) y
          ≤ |h y| * |HRS.Whole.convFun (rieszKernel d s) (fun t => |φ t|) y| :=
            mul_le_mul_of_nonneg_left (le_abs_self _) (abs_nonneg _)
        _ ≤ |h y| * (M * K * (1 + ‖y‖)) := mul_le_mul_of_nonneg_left hc (abs_nonneg _)
        _ = _ := by ring
  have hL : ∀ x, ∫ y, φ x * (rieszKernel d s (x - y) * h y) =
      φ x * ∫ y, rieszKernel d s (x - y) * h y := fun x => integral_const_mul _ _
  have hR : ∀ y, ∫ x, φ x * (rieszKernel d s (x - y) * h y) =
      h y * HRS.Whole.convFun (rieszKernel d s) φ y := by
    intro y
    unfold HRS.Whole.convFun
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only
    rw [show x - y = -(y - x) by abel, s79g_rieszKernel_even]
    ring
  refine ⟨hprod, ?_, ?_⟩
  · have := hprod.integral_prod_left
    exact this.congr (Filter.Eventually.of_forall fun x => by simp only; exact hL x)
  · have hsw := integral_integral_swap (μ := volume) (ν := volume)
      (f := fun x y => φ x * (rieszKernel d s (x - y) * h y)) hprod
    simp only [hL, hR] at hsw
    exact hsw

end HRS.MS.S79G
