import HRS.MS.SA12V3S

/-!
# S.A.12 C2 (SA12V3 worker), part T: weak convergence of the mollified datum, `∫ (G_ε * φ) ψ → ∫ φ ψ`
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff Pointwise

namespace HRS.MH.AdjointRd.Phase2SA12V3

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MH.AdjointRd
  HRS.MH.AdjointRd.Phase2SA12Construction

variable {d : ℕ}

theorem sa12v3_mollify_weak {η : Euc d → ℝ} (hη : IsMollifier η) {φ : Euc d → ℝ}
    (hφ : LocallyIntegrable φ volume) {ψ : Euc d → ℝ} (hψc : Continuous ψ) (R : ℝ)
    (hψs : ∀ y : Euc d, R < ‖y‖ → ψ y = 0) (δ : ℝ) (hδ : 0 < δ) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ε ≤ 1 →
      |(∫ x, mollify η ε φ x * ψ x) - ∫ x, φ x * ψ x| ≤ δ := by
  have hR0 : (0 : ℝ) ≤ max R 0 := le_max_right _ _
  set R' : ℝ := max R 0 with hR'
  have hψs' : ∀ y : Euc d, R' < ‖y‖ → ψ y = 0 := fun y hy => hψs y (lt_of_le_of_lt (le_max_left _ _) hy)
  have hψcs : HasCompactSupport ψ := HasCompactSupport.intro (isCompact_closedBall (0 : Euc d) R') (fun y hy => by
    apply hψs'; rw [Metric.mem_closedBall, dist_zero_right, not_le] at hy; exact hy)
  -- the local mass of φ
  set Mφ : ℝ := ∫ x in Metric.closedBall (0 : Euc d) (R' + 1), |φ x| with hMφ
  have hMφ0 : 0 ≤ Mφ := setIntegral_nonneg Metric.isClosed_closedBall.measurableSet (fun _ _ => abs_nonneg _)
  have hφi : IntegrableOn φ (Metric.closedBall (0 : Euc d) (R' + 1)) volume :=
    hφ.integrableOn_isCompact (isCompact_closedBall _ _)
  -- uniform continuity of ψ
  have hUC : UniformContinuousOn ψ (Metric.closedBall (0 : Euc d) (R' + 2)) :=
    (isCompact_closedBall _ _).uniformContinuousOn_of_continuous hψc.continuousOn
  obtain ⟨ε₁, hε₁, hψmod⟩ := Metric.uniformContinuousOn_iff.1 hUC (δ / (Mφ + 1)) (by positivity)
  refine ⟨min (ε₁ / 2) 1, lt_min (by linarith) one_pos, fun ε hε hεle hε1 => ?_⟩
  have hεε : ε < ε₁ := by have := (hεle.trans (min_le_left _ _)); linarith
  -- bounds
  obtain ⟨Bψ, hBψ⟩ := hψc.bounded_above_of_compact_support hψcs
  set G := sa12v3_G η ε with hG
  have hG0 : ∀ y, 0 ≤ G y := sa12v3_G_nonneg hη hε
  have hGint : Integrable G volume := sa12v3_G_integrable hη hε
  have hG1 : ∫ y, G y = 1 := sa12v3_G_integral hη hε
  have hGsupp : ∀ y : Euc d, ε < ‖y‖ → G y = 0 := by
    intro y hy
    simp only [hG, sa12v3_G]
    have : η (ε⁻¹ • y) = 0 := by
      by_contra hne
      have h1 : ε⁻¹ • y ∈ Metric.closedBall (0 : Euc d) 1 :=
        hη.2.2.1 (subset_tsupport _ (Function.mem_support.2 hne))
      rw [Metric.mem_closedBall, dist_zero_right, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hε,
        inv_mul_le_iff₀ hε, mul_one] at h1
      linarith
    rw [this, mul_zero]
  obtain ⟨BG, hBG⟩ := (sa12v3_G_cont hη ε).bounded_above_of_compact_support
    (HasCompactSupport.intro (isCompact_closedBall (0 : Euc d) ε) (fun y hy => hGsupp y (by
      rw [Metric.mem_closedBall, dist_zero_right, not_le] at hy; exact hy)))
  -- the product integrand
  set Φ : Euc d × Euc d → ℝ := fun p => ψ p.1 * (G p.2 * φ (p.1 - p.2)) with hΦ
  have hΦi : Integrable Φ ((volume : Measure (Euc d)).prod volume) := by
    set φ0 : Euc d → ℝ := (Metric.closedBall (0 : Euc d) (R' + 1)).indicator φ with hφ0
    have hφ0i : Integrable φ0 volume := (integrable_indicator_iff Metric.isClosed_closedBall.measurableSet).2 hφi
    set E : Euc d → ℝ := (Metric.closedBall (0 : Euc d) ε).indicator (fun _ => (1 : ℝ)) with hE
    have hEi : Integrable E volume :=
      (integrable_indicator_iff Metric.isClosed_closedBall.measurableSet).2
        (integrableOn_const measure_closedBall_lt_top.ne)
    have h1 : Integrable (fun p : Euc d × Euc d => ‖φ0 p.1‖ * E p.2) ((volume : Measure (Euc d)).prod volume) :=
      hφ0i.norm.mul_prod hEi
    have h2 := (measurePreserving_sub_prod (volume : Measure (Euc d)) (volume : Measure (Euc d))).integrable_comp_of_integrable h1
    have hmeas : AEStronglyMeasurable Φ ((volume : Measure (Euc d)).prod volume) := by
      have h3 : AEStronglyMeasurable (fun p : Euc d × Euc d => φ p.1) ((volume : Measure (Euc d)).prod volume) :=
        hφ.aestronglyMeasurable.comp_fst
      have h4 := h3.comp_measurePreserving (measurePreserving_sub_prod (volume : Measure (Euc d)) (volume : Measure (Euc d)))
      exact (hψc.comp continuous_fst).aestronglyMeasurable.mul
        (((sa12v3_G_cont hη ε).comp continuous_snd).aestronglyMeasurable.mul h4)
    have hBψ0 : 0 ≤ Bψ := by have := hBψ 0; simp only [Real.norm_eq_abs] at this; exact (abs_nonneg _).trans this
    have hBG0 : 0 ≤ BG := by have := hBG 0; simp only [Real.norm_eq_abs] at this; exact (abs_nonneg _).trans this
    refine Integrable.mono' (h2.const_mul (Bψ * BG)) hmeas (Eventually.of_forall fun p => ?_)
    simp only [Function.comp, hΦ, norm_mul, Real.norm_eq_abs, hφ0, hE, norm_indicator_eq_indicator_norm]
    have hRn : ∀ p : Euc d × Euc d, 0 ≤ Bψ * BG * ((Metric.closedBall (0 : Euc d) (R' + 1)).indicator
        (fun a => |φ a|) (p.1 - p.2) * (Metric.closedBall (0 : Euc d) ε).indicator (fun x => (1 : ℝ)) p.2) :=
      fun p => mul_nonneg (mul_nonneg hBψ0 hBG0) (mul_nonneg (Set.indicator_nonneg (fun _ _ => abs_nonneg _) _)
        (Set.indicator_nonneg (fun _ _ => zero_le_one) _))
    by_cases hp : ψ p.1 = 0
    · rw [hp, abs_zero, zero_mul]
      exact hRn p
    · have h1 : ‖p.1‖ ≤ R' := by
        by_contra h; exact hp (hψs' _ (not_le.1 h))
      by_cases hq : G p.2 = 0
      · rw [hq, abs_zero, zero_mul, mul_zero]
        exact hRn p
      · have h2 : ‖p.2‖ ≤ ε := by
          by_contra h; exact hq (hGsupp _ (not_le.1 h))
        have h3 : p.1 - p.2 ∈ Metric.closedBall (0 : Euc d) (R' + 1) := by
          rw [Metric.mem_closedBall, dist_zero_right]
          calc ‖p.1 - p.2‖ ≤ ‖p.1‖ + ‖p.2‖ := norm_sub_le _ _
            _ ≤ R' + 1 := by linarith
        have h4 : p.2 ∈ Metric.closedBall (0 : Euc d) ε := by
          rw [Metric.mem_closedBall, dist_zero_right]; exact h2
        rw [Set.indicator_of_mem h3, Set.indicator_of_mem h4, mul_one]
        have hb1 : |ψ p.1| ≤ Bψ := by simpa [Real.norm_eq_abs] using hBψ p.1
        have hb2 : |G p.2| ≤ BG := by simpa [Real.norm_eq_abs] using hBG p.2
        calc |ψ p.1| * (|G p.2| * |φ (p.1 - p.2)|) = (|ψ p.1| * |G p.2|) * |φ (p.1 - p.2)| := by ring
          _ ≤ (Bψ * BG) * |φ (p.1 - p.2)| :=
              mul_le_mul_of_nonneg_right (mul_le_mul hb1 hb2 (abs_nonneg _) ((abs_nonneg _).trans hb1)) (abs_nonneg _)
  set δ' : ℝ := δ / (Mφ + 1) with hδ'
  have hδ'0 : 0 < δ' := by positivity
  have hδ'M : δ' * Mφ ≤ δ := by
    have : δ' * (Mφ + 1) = δ := div_mul_cancel₀ _ (by positivity)
    nlinarith
  have hmol : ∀ x, mollify η ε φ x = ∫ y, G y * φ (x - y) := fun x => by
    unfold mollify
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only [hG, sa12v3_G]
  set T : Euc d → ℝ := fun y => ∫ x, ψ (x + y) * φ x with hT
  set S : ℝ := ∫ x, φ x * ψ x with hS
  have e1 : (∫ x, mollify η ε φ x * ψ x) = ∫ x, ∫ y, ψ x * (G y * φ (x - y)) := by
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    show mollify η ε φ x * ψ x = ∫ y, ψ x * (G y * φ (x - y))
    rw [hmol, mul_comm, integral_const_mul]
  have e2 : (∫ x, ∫ y, ψ x * (G y * φ (x - y))) = ∫ y, ∫ x, ψ x * (G y * φ (x - y)) :=
    integral_integral_swap (f := fun x y => ψ x * (G y * φ (x - y))) hΦi
  have e3 : ∀ y, ∫ x, ψ x * (G y * φ (x - y)) = G y * T y := by
    intro y
    have h1 : ∀ x, ψ x * (G y * φ (x - y)) = G y * (ψ x * φ (x - y)) := fun x => by ring
    simp_rw [h1]
    rw [integral_const_mul]
    congr 1
    have := integral_add_right_eq_self (μ := (volume : Measure (Euc d))) (fun x => ψ x * φ (x - y)) y
    simp only [add_sub_cancel_right] at this
    exact this.symm
  simp_rw [e3] at e2
  have hGT : Integrable (fun y => G y * T y) volume := by
    have := hΦi.integral_prod_right
    refine this.congr (Eventually.of_forall fun y => ?_)
    simp only
    exact e3 y
  have hGS : Integrable (fun y => G y * S) volume := hGint.mul_const S
  have hsub : (∫ x, mollify η ε φ x * ψ x) - S = ∫ y, G y * (T y - S) := by
    have e4 : S = ∫ y, G y * S := by rw [integral_mul_const, hG1, one_mul]
    have : ∫ y, G y * (T y - S) = (∫ y, G y * T y) - ∫ y, G y * S := by
      rw [← integral_sub hGT hGS]
      exact integral_congr_ae (Eventually.of_forall fun y => by ring)
    rw [this, ← e4, e1, e2]
  rw [hsub]
  -- the pointwise bound
  have hTS : ∀ y : Euc d, ‖y‖ ≤ ε → |T y - S| ≤ δ' * Mφ := by
    intro y hy
    have hyε : ‖y‖ < ε₁ := lt_of_le_of_lt hy hεε
    have hy1 : ‖y‖ ≤ 1 := hy.trans hε1
    have i1 : Integrable (fun x => ψ (x + y) * φ x) volume := by
      have := hφ.integrable_smul_right_of_hasCompactSupport (g := fun x => ψ (x + y))
        (hψc.comp (continuous_id.add continuous_const)) (hψcs.comp_homeomorph (Homeomorph.addRight y))
      simpa [mul_comm] using this
    have i2 : Integrable (fun x => ψ x * φ x) volume := by
      have := hφ.integrable_smul_right_of_hasCompactSupport hψc hψcs
      simpa [mul_comm] using this
    have e5 : T y - S = ∫ x, (ψ (x + y) - ψ x) * φ x := by
      rw [hT, hS]
      simp only
      rw [← integral_sub i1 (by simpa [mul_comm] using i2)]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      ring
    rw [e5]
    set g : Euc d → ℝ := (Metric.closedBall (0 : Euc d) (R' + 1)).indicator (fun x => δ' * |φ x|) with hg
    have hgi : Integrable g volume :=
      (integrable_indicator_iff Metric.isClosed_closedBall.measurableSet).2 (hφi.norm.const_mul δ')
    have := norm_integral_le_of_norm_le (f := fun x => (ψ (x + y) - ψ x) * φ x) hgi (Eventually.of_forall fun x => ?_)
    · rw [Real.norm_eq_abs] at this
      refine this.trans (le_of_eq ?_)
      rw [hg, integral_indicator Metric.isClosed_closedBall.measurableSet, integral_const_mul, hMφ]
    · by_cases hx : x ∈ Metric.closedBall (0 : Euc d) (R' + 1)
      · rw [hg, Set.indicator_of_mem hx, Real.norm_eq_abs, abs_mul]
        refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
        have hxn : ‖x‖ ≤ R' + 1 := by simpa using hx
        have hm1 : x + y ∈ Metric.closedBall (0 : Euc d) (R' + 2) := by
          rw [Metric.mem_closedBall, dist_zero_right]
          calc ‖x + y‖ ≤ ‖x‖ + ‖y‖ := norm_add_le _ _
            _ ≤ R' + 2 := by linarith
        have hm2 : x ∈ Metric.closedBall (0 : Euc d) (R' + 2) := by
          rw [Metric.mem_closedBall, dist_zero_right]; linarith
        have := hψmod _ hm1 _ hm2 (by rw [dist_eq_norm, add_sub_cancel_left]; simpa using hyε)
        rw [Real.dist_eq] at this
        exact this.le
      · rw [hg, Set.indicator_of_notMem hx]
        have hxn : R' + 1 < ‖x‖ := by
          rw [Metric.mem_closedBall, dist_zero_right, not_le] at hx; exact hx
        have h1 : ψ x = 0 := hψs' _ (by linarith)
        have h2 : ψ (x + y) = 0 := hψs' _ (by
          have := norm_sub_norm_le x (-y)
          rw [sub_neg_eq_add, norm_neg] at this
          linarith)
        simp [h1, h2]
  -- integrate
  have hfin : ‖∫ y, G y * (T y - S)‖ ≤ ∫ y, G y * (δ' * Mφ) := by
    refine norm_integral_le_of_norm_le (hGint.mul_const _) (Eventually.of_forall fun y => ?_)
    by_cases hy : ‖y‖ ≤ ε
    · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hG0 y)]
      exact mul_le_mul_of_nonneg_left (hTS y hy) (hG0 y)
    · rw [hGsupp y (not_le.1 hy)]; simp
  rw [integral_mul_const, hG1, one_mul] at hfin
  rw [← Real.norm_eq_abs]
  exact hfin.trans hδ'M

end HRS.MH.AdjointRd.Phase2SA12V3
