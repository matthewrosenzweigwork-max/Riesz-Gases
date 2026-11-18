import HRS.MS.SA16StrongSL6

/-!
# S.A.16 SL8: `strong_lift_isWmpWeaklyContinuous`

A norm-continuous path in `WmpSpace` represents a function that is weakly continuous in the literal
all-`StrongDual`, every-compatible-lift sense: compatible lifts are unique (SL4) and their norms
are the `wNormE` values (SL6).
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16
open HRS HRS.Whole HRS.Whole.AppendixA

theorem strong_lift_isWmpWeaklyContinuous (d m : ℕ) (p T : ℝ)
    [Fact (2 ≤ p)] (F : ℝ → Euc d → ℝ) (G : ℝ → WmpSpace d m p)
    (hG : ContinuousOn G (Icc (0 : ℝ) T))
    (hrep : ∀ t ∈ Icc (0 : ℝ) T, ∀ᵐ x ∂(volume : Measure (Euc d)),
      ((G t : WLp d m p) : Euc d → (WIndex d m → ℝ)) x (wZero d m)=F t x) :
    IsWmpWeaklyContinuous m p T F := by
  refine ⟨fun τ hτ => ?_, fun G' hG' ℓ => ?_⟩
  · rw [wNormE_eq_lift_norm d m p (G τ) (F τ) (hrep τ hτ)]
    exact ENNReal.ofReal_lt_top
  · have heq : EqOn (fun τ => ℓ (G' τ)) (fun τ => ℓ (G τ)) (Icc (0 : ℝ) T) := by
      intro τ hτ
      have : G' τ = G τ := by
        refine wmp_zero_injective d m p (G' τ) (G τ) ?_
        filter_upwards [hG' τ hτ, hrep τ hτ] with x hx1 hx2
        rw [hx1, hx2]
      simp only [this]
    exact (ℓ.continuous.comp_continuousOn hG).congr heq

end HRS.Whole.AppendixA.Phase2SA16
