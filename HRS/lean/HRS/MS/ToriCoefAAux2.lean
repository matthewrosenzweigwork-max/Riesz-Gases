import HRS.MS.ToriCoefAAux1

/-!
# MS-TORI-COEFA, helper file 2: the weight `⟨y⟩^{-(d+3)}`, the tail, and the `V`-bounds.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.ToriCoefA

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas

variable {d : ℕ}

/-- The decay weight `⟨y⟩^{-(d+3)}`. -/
def tca_g (y : Euc d) : ℝ := jbracket y ^ (-((d : ℝ) + 3))

theorem tca_g_nonneg (y : Euc d) : 0 ≤ tca_g y :=
  Real.rpow_nonneg (tca_jbracket_pos y).le _

theorem tca_g_mul (y : Euc d) : jbracket y ^ ((d : ℝ) + 3) * tca_g y = 1 := by
  unfold tca_g
  rw [Real.rpow_neg (tca_jbracket_pos y).le]
  exact mul_inv_cancel₀ (Real.rpow_pos_of_pos (tca_jbracket_pos y) _).ne'

theorem tca_g_integrable : Integrable (fun y : Euc d => tca_g y) := by
  have h := integrable_rpow_neg_one_add_norm_sq (μ := (volume : Measure (Euc d)))
    (r := (d : ℝ) + 3) (by simp [finrank_euclideanSpace])
  refine h.congr (Filter.Eventually.of_forall fun y => ?_)
  show (1 + ‖y‖ ^ 2) ^ (-((d : ℝ) + 3) / 2) = tca_g y
  unfold tca_g jbracket
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity)]
  congr 1
  ring

/-- Pointwise weighted bound to a bound by the weight. -/
theorem tca_abs_le_weight (ρ : Euc d → ℝ) (W : ℝ)
    (h : ∀ y, jbracket y ^ ((d : ℝ) + 3) * |ρ y| ≤ W) (y : Euc d) :
    |ρ y| ≤ W * tca_g y := by
  calc |ρ y| = (jbracket y ^ ((d : ℝ) + 3) * tca_g y) * |ρ y| := by rw [tca_g_mul, one_mul]
    _ = (jbracket y ^ ((d : ℝ) + 3) * |ρ y|) * tca_g y := by ring
    _ ≤ W * tca_g y := mul_le_mul_of_nonneg_right (h y) (tca_g_nonneg y)

/-- The tail of the weight integral tends to zero. -/
theorem tca_tail (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∫ y in {y : Euc d | (N : ℝ) ≤ ‖y‖}, tca_g y ≤ ε := by
  have hT : Tendsto (fun N : ℕ => ∫ y in {y : Euc d | (N : ℝ) ≤ ‖y‖}, tca_g y) atTop
      (𝓝 (∫ y in ⋂ N : ℕ, {y : Euc d | (N : ℝ) ≤ ‖y‖}, tca_g y)) := by
    apply tendsto_setIntegral_of_antitone
    · intro N
      exact measurableSet_le measurable_const continuous_norm.measurable
    · intro a b hab y hy
      show (a : ℝ) ≤ ‖y‖
      have hy' : (b : ℝ) ≤ ‖y‖ := hy
      exact le_trans (by exact_mod_cast hab) hy'
    · exact ⟨0, tca_g_integrable.integrableOn⟩
  have hempty : (⋂ N : ℕ, {y : Euc d | (N : ℝ) ≤ ‖y‖}) = ∅ := by
    ext y
    simp only [mem_iInter, mem_setOf_eq, mem_empty_iff_false, iff_false, not_forall, not_le]
    obtain ⟨N, hN⟩ := exists_nat_gt ‖y‖
    exact ⟨N, hN⟩
  rw [hempty] at hT
  simp only [Measure.restrict_empty, integral_zero_measure] at hT
  have := (tendsto_order.1 hT).2 ε hε
  obtain ⟨N, hN⟩ := this.exists
  exact ⟨N, hN.le⟩

/-! ### The `V`-bounds -/

/-- Mean value bound on `fderiv V` from the second derivative. -/
theorem tca_fderiv_lip (V : Euc d → ℝ) (hV1 : ContDiff ℝ ∞ V) (ΛV : ℝ)
    (hV2 : ∀ x : Euc d, ‖iteratedFDeriv ℝ 2 V x‖ ≤ ΛV) (z : Euc d) :
    ‖fderiv ℝ V z - fderiv ℝ V 0‖ ≤ ΛV * ‖z - 0‖ := by
  have hdiff : ∀ x : Euc d, DifferentiableAt ℝ (fderiv ℝ V) x := fun x =>
    ((hV1.fderiv_right (m := ∞) (by simp)).differentiable (by simp)) x
  have hnorm : ∀ x : Euc d, ‖fderiv ℝ (fderiv ℝ V) x‖ ≤ ΛV := by
    intro x
    rw [← norm_iteratedFDeriv_one, norm_iteratedFDeriv_fderiv]
    exact hV2 x
  exact Convex.norm_image_sub_le_of_norm_fderiv_le (fun x _ => hdiff x) (fun x _ => hnorm x)
    convex_univ (mem_univ _) (mem_univ _)

theorem tca_fderiv_bound (V : Euc d → ℝ) (hV1 : ContDiff ℝ ∞ V) (ΛV G₀ : ℝ)
    (hΛ0 : 0 ≤ ΛV) (hV2 : ∀ x : Euc d, ‖iteratedFDeriv ℝ 2 V x‖ ≤ ΛV)
    (hV3 : ‖gradient V 0‖ ≤ G₀) (z : Euc d) :
    ‖fderiv ℝ V z‖ ≤ G₀ + ΛV * ‖z‖ := by
  have h0 : ‖fderiv ℝ V 0‖ ≤ G₀ := by
    have : ‖gradient V 0‖ = ‖fderiv ℝ V 0‖ := by
      unfold gradient
      exact LinearIsometryEquiv.norm_map _ _
    linarith
  have h1 := tca_fderiv_lip V hV1 ΛV hV2 z
  rw [sub_zero] at h1
  have h2 : fderiv ℝ V z = (fderiv ℝ V z - fderiv ℝ V 0) + fderiv ℝ V 0 := by abel
  calc ‖fderiv ℝ V z‖ = ‖(fderiv ℝ V z - fderiv ℝ V 0) + fderiv ℝ V 0‖ := by rw [← h2]
    _ ≤ ‖fderiv ℝ V z - fderiv ℝ V 0‖ + ‖fderiv ℝ V 0‖ := norm_add_le _ _
    _ ≤ ΛV * ‖z‖ + G₀ := by linarith
    _ = G₀ + ΛV * ‖z‖ := by ring

theorem tca_val_bound (V : Euc d → ℝ) (hV1 : ContDiff ℝ ∞ V) (ΛV G₀ V₀ : ℝ)
    (hΛ0 : 0 ≤ ΛV) (hV2 : ∀ x : Euc d, ‖iteratedFDeriv ℝ 2 V x‖ ≤ ΛV)
    (hV3 : ‖gradient V 0‖ ≤ G₀) (hV0 : |V 0| ≤ V₀) (y : Euc d) :
    |V y| ≤ V₀ + (G₀ + ΛV * ‖y‖) * ‖y‖ := by
  have hG : ∀ x ∈ Metric.closedBall (0 : Euc d) ‖y‖,
      ‖fderiv ℝ V x‖ ≤ G₀ + ΛV * ‖y‖ := by
    intro x hx
    rw [Metric.mem_closedBall, dist_zero_right] at hx
    have := tca_fderiv_bound V hV1 ΛV G₀ hΛ0 hV2 hV3 x
    nlinarith
  have hd : ∀ x ∈ Metric.closedBall (0 : Euc d) ‖y‖, DifferentiableAt ℝ V x := fun x _ =>
    (hV1.differentiable (by simp)) x
  have h0m : (0 : Euc d) ∈ Metric.closedBall (0 : Euc d) ‖y‖ :=
    Metric.mem_closedBall_self (norm_nonneg _)
  have hym : y ∈ Metric.closedBall (0 : Euc d) ‖y‖ := by
    rw [Metric.mem_closedBall, dist_zero_right]
  have hm := Convex.norm_image_sub_le_of_norm_fderiv_le hd hG (convex_closedBall _ _) h0m hym
  have h1 : |V y| ≤ |V 0| + ‖V y - V 0‖ := by
    have := abs_add_le (V 0) (V y - V 0)
    rw [show V 0 + (V y - V 0) = V y by ring] at this
    rw [← Real.norm_eq_abs] at this
    exact this
  rw [sub_zero] at hm
  linarith

end HRS.MS.ToriCoefA
