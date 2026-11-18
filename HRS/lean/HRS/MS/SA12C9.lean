import HRS.MS.SA12C8

/-!
# S.A.12(c), packet E7.06 (part 7): integral Gronwall with prefactor one
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12C

/-- If `E' ≤ Λ E` on `[0,t]` (one-sided derivatives within `[0,t]`) then `E(τ) ≤ e^{Λτ} E(0)`. -/
theorem sa12c_gronwall {E E' : ℝ → ℝ} {t Λ : ℝ}
    (hder : ∀ τ ∈ Icc (0 : ℝ) t, HasDerivWithinAt E (E' τ) (Icc (0 : ℝ) t) τ)
    (hle : ∀ τ ∈ Icc (0 : ℝ) t, E' τ ≤ Λ * E τ) :
    ∀ τ ∈ Icc (0 : ℝ) t, E τ ≤ Real.exp (Λ * τ) * E 0 := by
  intro τ hτ
  set g : ℝ → ℝ := fun s => Real.exp (-(Λ * s)) * E s with hg
  have hgd : ∀ s ∈ Icc (0 : ℝ) t, HasDerivWithinAt g
      (Real.exp (-(Λ * s)) * (E' s - Λ * E s)) (Icc (0 : ℝ) t) s := by
    intro s hs
    have h1 : HasDerivAt (fun s : ℝ => Real.exp (-(Λ * s))) (Real.exp (-(Λ * s)) * (-Λ)) s := by
      have := ((hasDerivAt_id s).const_mul Λ).neg.exp
      simpa using this
    have h2 := h1.hasDerivWithinAt.mul (hder s hs)
    refine h2.congr_deriv ?_
    ring
  have hanti : AntitoneOn g (Icc (0 : ℝ) t) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc 0 t) ?_ ?_ ?_
    · intro s hs
      exact (hgd s hs).continuousWithinAt
    · intro s hs
      rw [interior_Icc] at hs
      exact (hgd s (Ioo_subset_Icc_self hs)).hasDerivAt (Icc_mem_nhds hs.1 hs.2) |>.differentiableAt
        |>.differentiableWithinAt
    · intro s hs
      rw [interior_Icc] at hs
      have hs' := Ioo_subset_Icc_self hs
      have hd := (hgd s hs').hasDerivAt (Icc_mem_nhds hs.1 hs.2)
      rw [hd.deriv]
      exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le (by linarith [hle s hs'])
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) t := ⟨le_rfl, hτ.1.trans hτ.2⟩
  have := hanti h0 hτ hτ.1
  simp only [hg, mul_zero, neg_zero, Real.exp_zero, one_mul] at this
  have h3 : Real.exp (Λ * τ) * Real.exp (-(Λ * τ)) = 1 := by
    rw [← Real.exp_add]; simp
  calc E τ = Real.exp (Λ * τ) * (Real.exp (-(Λ * τ)) * E τ) := by rw [← mul_assoc, h3, one_mul]
    _ ≤ Real.exp (Λ * τ) * E 0 := mul_le_mul_of_nonneg_left this (Real.exp_pos _).le

end HRS.MH.AdjointRd.Phase2SA12C
