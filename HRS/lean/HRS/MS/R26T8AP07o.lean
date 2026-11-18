import HRS.MS.R26T8AP07n

/-!
# S8.2 local Newton layer, packet T8A.P07 (part o): a local smooth-series lemma
`r26t8a_p07_contDiffOn_tsum`: a series of `C^m` functions whose iterated derivatives of order `<= m` are bounded on a ball by summable
sequences has a `C^m` sum on that ball (Mathlib's `contDiff_tsum` needs global bounds).
-/

set_option autoImplicit false
noncomputable section
open Filter Topology Metric
open scoped ContDiff

namespace HRS.MS.R26T8A

theorem r26t8a_p07_contDiffOn_tsum {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (x0 : E) (r : ℝ) :
    ∀ (m : ℕ) {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] (f : ℕ → E → F),
      (∀ n, ContDiff ℝ (m : WithTop ℕ∞) (f n)) →
      (∀ i ≤ m, ∃ u : ℕ → ℝ, Summable u ∧ ∀ n, ∀ y ∈ ball x0 r, ‖iteratedFDeriv ℝ i (f n) y‖ ≤ u n) →
      ContDiffOn ℝ (m : WithTop ℕ∞) (fun y => ∑' n, f n y) (ball x0 r) := by
  intro m
  induction m with
  | zero =>
    intro F _ _ _ f hf hb
    obtain ⟨u, hu, hbu⟩ := hb 0 le_rfl
    rw [Nat.cast_zero, contDiffOn_zero]
    refine continuousOn_tsum (fun n => (hf n).continuous.continuousOn) hu (fun n y hy => ?_)
    have := hbu n y hy
    rwa [norm_iteratedFDeriv_zero] at this
  | succ m ih =>
    intro F _ _ _ f hf hb
    have hs : IsOpen (ball x0 r) := isOpen_ball
    by_cases hr : 0 < r
    · have hf1 : ∀ n, ContDiff ℝ ((m + 1 : ℕ) : WithTop ℕ∞) (f n) := hf
      have hg : ∀ n, ContDiff ℝ (m : WithTop ℕ∞) (fderiv ℝ (f n)) := fun n =>
        (hf1 n).fderiv_right (by push_cast; exact le_rfl)
      have hbg : ∀ i ≤ m, ∃ u : ℕ → ℝ, Summable u ∧
          ∀ n, ∀ y ∈ ball x0 r, ‖iteratedFDeriv ℝ i (fderiv ℝ (f n)) y‖ ≤ u n := by
        intro i hi
        obtain ⟨u, hu, hbu⟩ := hb (i + 1) (by omega)
        exact ⟨u, hu, fun n y hy => by rw [norm_iteratedFDeriv_fderiv]; exact hbu n y hy⟩
      have hih := ih (fun n => fderiv ℝ (f n)) hg hbg
      obtain ⟨u0, hu0, hbu0⟩ := hb 0 (by omega)
      obtain ⟨u1, hu1, hbu1⟩ := hbg 0 (by omega)
      have hder : ∀ y ∈ ball x0 r, HasFDerivAt (fun y => ∑' n, f n y) (∑' n, fderiv ℝ (f n) y) y := by
        intro y hy
        refine hasFDerivAt_tsum_of_isPreconnected (f := f) (f' := fun n y => fderiv ℝ (f n) y) hu1 hs
          (convex_ball x0 r).isPreconnected
          (fun n x _ => ((hf1 n).differentiable (by simp)).differentiableAt.hasFDerivAt)
          (fun n x hx => by
            have := hbu1 n x hx
            rwa [norm_iteratedFDeriv_zero] at this)
          (mem_ball_self hr)
          (Summable.of_norm_bounded hu0 (fun n => by
            have := hbu0 n x0 (mem_ball_self hr)
            rwa [norm_iteratedFDeriv_zero] at this)) hy
      have hfd : ∀ y ∈ ball x0 r, fderiv ℝ (fun y => ∑' n, f n y) y = ∑' n, fderiv ℝ (f n) y :=
        fun y hy => (hder y hy).fderiv
      rw [Nat.cast_succ, contDiffOn_succ_iff_fderiv_of_isOpen hs]
      refine ⟨fun y hy => (hder y hy).differentiableAt.differentiableWithinAt, fun h => by simp at h, ?_⟩
      exact hih.congr fun y hy => hfd y hy
    · rw [ball_eq_empty.2 (not_lt.1 hr)]
      exact contDiffOn_empty

end HRS.MS.R26T8A
