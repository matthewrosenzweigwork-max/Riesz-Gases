import HRS.MS.Fp81S21WickApprox13
import HRS.MS.Fp81S21EmbedField12

/-! Physical finite-coordinate particle approximants. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Classical MeasureTheory
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R26T6

/-- The physical finite-rank particle coefficient field has a jointly measurable
version, simultaneously representing every time and every selected rank kernel. -/
theorem fp81s21_particle_rankKernel_coordinate_field (p : Parameters) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → ∀ R : Trajectory p δ,
      ∀ N : ℕ, ∀ A : Particle R N, ∀ m : ℕ,
      ∀ D : Fin m → fp81s21_RankKernel p.d,
      ∃ q : ℝ → A.Ω → r26t6_Coeff,
        Measurable (Function.uncurry q) ∧
        ∀ᵐ ω ∂A.P, ∀ u : ℝ, 0 ≤ u →
          q u ω = ∑ j : Fin m,
            fp81s21_particleQuad A u (D j).kernel ω • fp81s21_coeffBasis j := by
  obtain ⟨δ₀, hδ₀, hhalf, hF⟩ := fp81s21_particle_rankKernel_joint p
  refine ⟨δ₀, hδ₀, hhalf, ?_⟩
  intro δ hδ hδle R N A m D
  choose F hFm hFe using fun j : Fin m => hF δ hδ hδle R N A (D j)
  let q : ℝ → A.Ω → r26t6_Coeff := fun u ω =>
    ∑ j : Fin m, F j (u, ω) • fp81s21_coeffBasis j
  refine ⟨q, ?_, ?_⟩
  · exact Finset.measurable_sum _ fun j _ => (hFm j).smul measurable_const
  · have hall : ∀ᵐ ω ∂A.P, ∀ j : Fin m, ∀ u : ℝ, 0 ≤ u →
        F j (u, ω) = fp81s21_particleQuad A u (D j).kernel ω := by
      exact ae_all_iff.mpr hFe
    filter_upwards [hall] with ω hω u hu
    dsimp [q]
    exact Finset.sum_congr rfl (fun j _ => by rw [hω j u hu])

#print axioms fp81s21_particle_rankKernel_coordinate_field
end HRS.Fp81.S21
end
