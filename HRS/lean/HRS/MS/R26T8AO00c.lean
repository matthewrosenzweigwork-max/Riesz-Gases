import HRS.MS.R26T8AO00b

/-!
# S8.2 observed-time layer, packet T8A.O00 (helper c): pointwise bound of the commutator kernel

For `f` with `‖∇f‖ ≤ A` and `‖∂²f‖ ≤ A`, the commutator kernel `⟨∇f x - ∇f y, ∇K(x-y)⟩` is bounded by
`A s (1_{|x-y|<1} |x-y|^(-s) + 2)`, and the singular part `1_{|z|<1} |z|^(-s)` is integrable when `s < d`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators ContDiff
namespace HRS.MS.R26T8A
open HRS HRS.Whole

theorem r26t8a_o00c_pt {d : ℕ} {s : ℝ} (hs : 0 < s) (f : Euc d → ℝ) (hf : ContDiff ℝ ∞ f) (A : ℝ)
    (hA : 0 ≤ A) (h1 : ∀ y, ‖iteratedFDeriv ℝ 1 f y‖ ≤ A) (h2 : ∀ y, ‖iteratedFDeriv ℝ 2 f y‖ ≤ A)
    (x y : Euc d) :
    ‖commutatorKernel d s (gradient f) x y‖ ≤
      A * s * ((Metric.ball (0 : Euc d) 1).indicator (fun z => ‖z‖ ^ (-s)) (x - y) + 2) := by
  have hind : 0 ≤ (Metric.ball (0 : Euc d) 1).indicator (fun z => ‖z‖ ^ (-s)) (x - y) :=
    indicator_nonneg (fun z _ => Real.rpow_nonneg (norm_nonneg _) _) _
  have hAs : 0 ≤ A * s := mul_nonneg hA hs.le
  unfold commutatorKernel
  by_cases hz : x - y = 0
  · have hxy : x = y := sub_eq_zero.1 hz
    subst hxy
    simp only [sub_self, inner_zero_left, norm_zero] at hind ⊢
    exact mul_nonneg hAs (by linarith)
  have hKn : ‖rieszKernelGrad d s (x - y)‖ = s * ‖x - y‖ ^ (-s - 1) :=
    r26t8a_o00a_kernel_grad_norm d hs (x - y) hz
  have hnorm : ∀ w : Euc d, ‖gradient f w‖ ≤ A := by
    intro w
    have e : ‖gradient f w‖ = ‖fderiv ℝ f w‖ := by
      unfold gradient
      exact LinearIsometryEquiv.norm_map _ _
    rw [e, ← norm_iteratedFDeriv_one (𝕜 := ℝ) (f := f) (x := w)]
    exact h1 w
  have hdiff1 : ‖gradient f x - gradient f y‖ ≤ A * ‖x - y‖ :=
    r26t8a_o00b_grad_lip f hf A h2 x y
  have hdiff2 : ‖gradient f x - gradient f y‖ ≤ 2 * A := by
    have := norm_sub_le (gradient f x) (gradient f y)
    linarith [hnorm x, hnorm y]
  have hI := norm_inner_le_norm (𝕜 := ℝ) (gradient f x - gradient f y) (rieszKernelGrad d s (x - y))
  have hzn : 0 < ‖x - y‖ := norm_pos_iff.2 hz
  have hsplit : ‖x - y‖ * ‖x - y‖ ^ (-s - 1) = ‖x - y‖ ^ (-s) := by
    have h := Real.rpow_add hzn (-s - 1) 1
    rw [show (-s - 1) + 1 = -s by ring, Real.rpow_one] at h
    rw [h]
    ring
  by_cases hball : ‖x - y‖ < 1
  · have hmem : x - y ∈ Metric.ball (0 : Euc d) 1 := by
      rw [mem_ball_zero_iff]; exact hball
    rw [indicator_of_mem hmem]
    calc ‖commutatorKernel d s (gradient f) x y‖
        = ‖inner ℝ (gradient f x - gradient f y) (rieszKernelGrad d s (x - y))‖ := rfl
      _ ≤ ‖gradient f x - gradient f y‖ * ‖rieszKernelGrad d s (x - y)‖ := hI
      _ ≤ (A * ‖x - y‖) * (s * ‖x - y‖ ^ (-s - 1)) :=
          mul_le_mul hdiff1 (le_of_eq hKn) (norm_nonneg _) (by positivity)
      _ = A * s * ‖x - y‖ ^ (-s) := by rw [← hsplit]; ring
      _ ≤ A * s * (‖x - y‖ ^ (-s) + 2) := mul_le_mul_of_nonneg_left (by linarith) hAs
  · have hmem : x - y ∉ Metric.ball (0 : Euc d) 1 := by
      rw [mem_ball_zero_iff]; exact hball
    rw [indicator_of_notMem hmem, zero_add]
    have hle1 : ‖x - y‖ ^ (-s - 1) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (not_lt.1 hball) (by linarith)
    calc ‖commutatorKernel d s (gradient f) x y‖
        = ‖inner ℝ (gradient f x - gradient f y) (rieszKernelGrad d s (x - y))‖ := rfl
      _ ≤ ‖gradient f x - gradient f y‖ * ‖rieszKernelGrad d s (x - y)‖ := hI
      _ ≤ (2 * A) * (s * ‖x - y‖ ^ (-s - 1)) :=
          mul_le_mul hdiff2 (le_of_eq hKn) (norm_nonneg _) (by positivity)
      _ ≤ (2 * A) * (s * 1) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact mul_le_mul_of_nonneg_left hle1 hs.le
      _ = A * s * 2 := by ring

end HRS.MS.R26T8A

end
