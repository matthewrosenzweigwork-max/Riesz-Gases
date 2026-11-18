import HRS.MS.Fp81S21BV011

/-! Variation domination by an increasing scalar interval control. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Set
open scoped ENNReal
namespace HRS.Fp81.S21

variable {E : Type*} [NormedAddCommGroup E]
variable {H : ℝ} (hH : 0 ≤ H)

/-- A monotone scalar control bounds the variation of a path when it bounds every
increment. Integral controls are included by taking the cumulative integral. -/
theorem fp81s21_variation_le_control (hH : 0 ≤ H) (f : ℝ → E) (g : ℝ → ℝ)
    (hg : MonotoneOn g (Icc 0 H))
    (hinc : ∀ s ∈ Icc (0 : ℝ) H, ∀ t ∈ Icc (0 : ℝ) H, s ≤ t →
      ‖f t - f s‖ ≤ g t - g s) :
    eVariationOn f (Icc 0 H) ≤ ENNReal.ofReal (g H - g 0) := by
  have hcompare : eVariationOn f (Icc 0 H) ≤ eVariationOn g (Icc 0 H) := by
    unfold eVariationOn
    apply iSup_le
    rintro ⟨n, u, hu, hus⟩
    calc
      _ ≤ ∑ i ∈ Finset.range n, edist (g (u (i + 1))) (g (u i)) := by
        apply Finset.sum_le_sum
        intro i hi
        rw [edist_dist, dist_eq_norm, edist_dist, Real.dist_eq,
          abs_of_nonneg (sub_nonneg.mpr (hg (hus i) (hus (i + 1)) (hu (Nat.le_succ i))))]
        exact ENNReal.ofReal_le_ofReal (hinc (u i) (hus i) (u (i + 1)) (hus (i + 1)) (hu (Nat.le_succ i)))
      _ ≤ eVariationOn g (Icc 0 H) := eVariationOn.sum_le hu hus
  have hscalar : eVariationOn g (Icc 0 H) = ENNReal.ofReal (g H - g 0) := by
    simpa only [inter_self] using hg.eVariationOn_eq (show (0 : ℝ) ∈ Icc 0 H from ⟨le_rfl, hH⟩)
      (show H ∈ Icc 0 H from ⟨hH, le_rfl⟩)
  exact hcompare.trans_eq hscalar

#print axioms fp81s21_variation_le_control
end HRS.Fp81.S21
end
