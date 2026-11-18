import HRS.MS.SA12K1

/-!
# S.A.12 C1, kernel form of the mollification and its derivatives

`kconv f κ (x) = ∫ f(y) κ(x - y) dy` for a continuous scalar `f` and a compactly supported smooth kernel
`κ`: `D^i (kconv f η) = kconv f (D^i η)` for every `i`; the translation form `sa12k_moll η f` equals
`kconv f η`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12Construction

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MH.AdjointRd

variable {d : ℕ}

/-- `∫ f(y) κ(x-y) dy`. -/
def sa12k_kconv {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (f : Euc d → ℝ) (κ : Euc d → V)
    (x : Euc d) : V :=
  ∫ y, f y • κ (x - y)

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

theorem sa12k_kconv_integrable {f : Euc d → ℝ} (hf : Continuous f) {κ : Euc d → V}
    (hκ : Continuous κ) (hc : HasCompactSupport κ) (x : Euc d) :
    Integrable (fun y => f y • κ (x - y)) := by
  refine Continuous.integrable_of_hasCompactSupport ?_ ?_
  · exact hf.smul (hκ.comp (continuous_const.sub continuous_id))
  · have h : HasCompactSupport (fun y : Euc d => κ (x - y)) :=
      hc.comp_homeomorph (Homeomorph.subLeft x)
    exact h.smul_left

theorem sa12k_kconv_hasFDerivAt {f : Euc d → ℝ} (hf : Continuous f) {κ : Euc d → V}
    (hκ : ContDiff ℝ 1 κ) (hc : HasCompactSupport κ) (x₀ : Euc d) :
    HasFDerivAt (sa12k_kconv f κ) (sa12k_kconv f (fderiv ℝ κ) x₀) x₀ := by
  have hfd : Differentiable ℝ κ := hκ.differentiable one_ne_zero
  have hfc : Continuous (fderiv ℝ κ) := hκ.continuous_fderiv one_ne_zero
  have hcd : HasCompactSupport (fderiv ℝ κ) := hc.fderiv ℝ
  obtain ⟨R₀, hR₀⟩ := hcd.isCompact.isBounded.subset_closedBall (0 : Euc d)
  obtain ⟨B, hB⟩ : ∃ B : ℝ, ∀ z, ‖fderiv ℝ κ z‖ ≤ B := by
    obtain ⟨B, hB⟩ := hcd.exists_bound_of_continuous hfc
    exact ⟨B, hB⟩
  have hK : IsCompact (Metric.closedBall x₀ (1 + R₀)) := isCompact_closedBall _ _
  have hint : Integrable (fun y => (Metric.closedBall x₀ (1 + R₀)).indicator
      (fun y => |f y| * B) y) := by
    rw [integrable_indicator_iff hK.measurableSet]
    exact (hf.abs.mul continuous_const).continuousOn.integrableOn_compact hK
  have h := hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℝ) (μ := (volume : Measure (Euc d)))
    (s := Metric.ball x₀ 1) (x₀ := x₀)
    (F := fun (x : Euc d) (y : Euc d) => f y • κ (x - y))
    (F' := fun (x : Euc d) (y : Euc d) => f y • fderiv ℝ κ (x - y))
    (bound := fun y => (Metric.closedBall x₀ (1 + R₀)).indicator (fun y => |f y| * B) y)
    (Metric.ball_mem_nhds x₀ one_pos)
    (Filter.Eventually.of_forall fun y =>
      (sa12k_kconv_integrable hf hκ.continuous hc y).aestronglyMeasurable)
    (sa12k_kconv_integrable hf hκ.continuous hc x₀)
    (sa12k_kconv_integrable hf hfc hcd x₀).aestronglyMeasurable
    (Filter.Eventually.of_forall fun y x hx => by
      show ‖f y • fderiv ℝ κ (x - y)‖ ≤ _
      by_cases hy : y ∈ Metric.closedBall x₀ (1 + R₀)
      · rw [Set.indicator_of_mem hy, norm_smul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left (hB _) (abs_nonneg _)
      · rw [Set.indicator_of_notMem hy]
        have : fderiv ℝ κ (x - y) = 0 := by
          by_contra hne
          apply hy
          have hmem : x - y ∈ tsupport (fderiv ℝ κ) := subset_tsupport _ hne
          have h1 := hR₀ hmem
          rw [Metric.mem_closedBall, dist_zero_right] at h1
          rw [Metric.mem_closedBall, dist_eq_norm]
          rw [Metric.mem_ball, dist_eq_norm] at hx
          calc ‖y - x₀‖ = ‖(x - x₀) - (x - y)‖ := by congr 1; abel
            _ ≤ ‖x - x₀‖ + ‖x - y‖ := norm_sub_le _ _
            _ ≤ 1 + R₀ := by linarith
        rw [this]; simp)
    hint
    (Filter.Eventually.of_forall fun y x _ => by
      have h1 : HasFDerivAt (fun x : Euc d => κ (x - y)) (fderiv ℝ κ (x - y)) x := by
        have h2 := (hfd (x - y)).hasFDerivAt.comp x ((hasFDerivAt_id x).sub_const y)
        exact h2
      exact h1.const_smul (f y))
  exact h

theorem sa12k_kconv_iter {f : Euc d → ℝ} (hf : Continuous f) {η : Euc d → ℝ}
    (hη : ContDiff ℝ ∞ η) (hc : HasCompactSupport η) :
    ∀ i : ℕ, iteratedFDeriv ℝ i (sa12k_kconv f η) = sa12k_kconv f (iteratedFDeriv ℝ i η) := by
  intro i
  induction i with
  | zero =>
    funext x
    rw [iteratedFDeriv_zero_eq_comp]
    simp only [Function.comp_apply]
    unfold sa12k_kconv
    have key : (continuousMultilinearCurryFin0 ℝ (Euc d) ℝ).symm (∫ y, f y • η (x - y)) =
        ∫ y, (continuousMultilinearCurryFin0 ℝ (Euc d) ℝ).symm (f y • η (x - y)) :=
      (ContinuousLinearEquiv.integral_comp_comm (μ := (volume : Measure (Euc d)))
        (continuousMultilinearCurryFin0 ℝ (Euc d) ℝ).symm.toContinuousLinearEquiv
        (fun y => f y • η (x - y))).symm
    rw [key]
    congr 1
  | succ i ih =>
    funext x
    have hκ1 : ContDiff ℝ 1 (iteratedFDeriv ℝ i η) := by
      have := hη.iteratedFDeriv_right (i := i) (m := 1) (by exact_mod_cast le_top)
      simpa using this
    have hκc : HasCompactSupport (iteratedFDeriv ℝ i η) := hc.iteratedFDeriv i
    have e1 : ∀ g : Euc d → ℝ, iteratedFDeriv ℝ (i + 1) g x =
        (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (i + 1) => Euc d) ℝ).symm
          (fderiv ℝ (iteratedFDeriv ℝ i g) x) := fun g => by
      rw [iteratedFDeriv_succ_eq_comp_left]; rfl
    rw [e1, ih]
    have hd := (sa12k_kconv_hasFDerivAt hf hκ1 hκc x).fderiv
    rw [hd]
    unfold sa12k_kconv
    have key : (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (i + 1) => Euc d) ℝ).symm
        (∫ y, f y • fderiv ℝ (iteratedFDeriv ℝ i η) (x - y)) =
        ∫ y, (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (i + 1) => Euc d) ℝ).symm
          (f y • fderiv ℝ (iteratedFDeriv ℝ i η) (x - y)) :=
      (ContinuousLinearEquiv.integral_comp_comm (𝕜 := ℝ) (μ := (volume : Measure (Euc d)))
        (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (i + 1) => Euc d) ℝ).symm.toContinuousLinearEquiv
        (fun y => f y • fderiv ℝ (iteratedFDeriv ℝ i η) (x - y))).symm
    rw [key]
    congr 1

/-- The translation form equals the kernel form. -/
theorem sa12k_moll_eq_kconv (η f : Euc d → ℝ) : sa12k_moll η f = sa12k_kconv f η := by
  funext x
  unfold sa12k_moll sa12k_kconv
  have := integral_sub_left_eq_self (μ := (volume : Measure (Euc d))) (fun y => η (x - y) • f y) x
  simp only [sub_sub_cancel] at this
  rw [this]
  congr 1
  funext y
  rw [smul_eq_mul, smul_eq_mul, mul_comm]

end HRS.MH.AdjointRd.Phase2SA12Construction
