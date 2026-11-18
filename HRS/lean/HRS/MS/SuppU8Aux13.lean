import HRS.MS.SuppU8Aux12
import HRS.MS.SuppU8Aux8

/-!
# Worker U8 aux 13: Schwartz bounds in the form of the pointwise lemma, and real versus complex
-/

noncomputable section

open MeasureTheory
open scoped FourierTransform

namespace HRS.U8

variable {d : ℕ}

theorem u8_fd_ofReal {V : Type*} [AddCommGroup V] (L : List V) (v : V → ℝ) (x : V) :
    u8_fd L (fun z => ((v z : ℝ) : ℂ)) x = ((u8_fd L v x : ℝ) : ℂ) := by
  induction L generalizing v with
  | nil => rfl
  | cons h hs ih =>
    rw [u8_fd_cons, u8_fd_cons]
    have : (fun z => ((v (z + h) : ℝ) : ℂ) - ((v z : ℝ) : ℂ)) =
        fun z => (((v (z + h) - v z : ℝ)) : ℂ) := by
      funext z; push_cast; ring
    rw [this]
    exact ih (fun z => v (z + h) - v z)

theorem u8_schwartz_bounds (φ : SchwartzMap (EuclideanSpace ℝ (Fin d)) ℂ) (ℓ : ℕ) (b' : ℝ)
    (hb' : 0 ≤ b') :
    ∃ B : ℝ, 0 ≤ B ∧ (∀ z, ‖φ z‖ ≤ B * (1 + ‖z‖) ^ (-b')) ∧
      (∀ z, ‖iteratedFDeriv ℝ ℓ φ z‖ ≤ B * (1 + ‖z‖) ^ (-(b' + ℓ))) := by
  obtain ⟨k, hk⟩ : ∃ k : ℕ, b' + ℓ ≤ k := ⟨⌈b' + ℓ⌉₊, Nat.le_ceil _⟩
  obtain ⟨C0, hC0⟩ : ∃ C0 : ℝ, ∀ z, (1 + ‖z‖) ^ k * ‖iteratedFDeriv ℝ 0 (⇑φ) z‖ ≤ C0 :=
    ⟨_, fun z => SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (k, 0)) le_rfl le_rfl φ z⟩
  obtain ⟨C1, hC1⟩ : ∃ C1 : ℝ, ∀ z, (1 + ‖z‖) ^ k * ‖iteratedFDeriv ℝ ℓ (⇑φ) z‖ ≤ C1 :=
    ⟨_, fun z => SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (k, ℓ)) le_rfl le_rfl φ z⟩
  refine ⟨max C0 C1, le_max_of_le_left ?_, ?_, ?_⟩
  · have := hC0 0
    simp at this
    exact le_trans (by positivity) this
  · intro z
    have h1 := hC0 z
    rw [norm_iteratedFDeriv_zero] at h1
    have hz : 0 < 1 + ‖z‖ := by positivity
    have h2 : (1 + ‖z‖) ^ (-(k : ℝ)) * (1 + ‖z‖) ^ k = 1 := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hz]; simp
    have h3 : (1 + ‖z‖) ^ (-b') ≥ (1 + ‖z‖) ^ (-(k : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith [norm_nonneg z]) (by linarith)
    calc ‖φ z‖ = (1 + ‖z‖) ^ (-(k : ℝ)) * ((1 + ‖z‖) ^ k * ‖φ z‖) := by
          rw [← mul_assoc, h2, one_mul]
      _ ≤ (1 + ‖z‖) ^ (-(k : ℝ)) * max C0 C1 := by
          apply mul_le_mul_of_nonneg_left (h1.trans (le_max_left _ _)) (by positivity)
      _ ≤ (1 + ‖z‖) ^ (-b') * max C0 C1 := by
          apply mul_le_mul_of_nonneg_right h3
          exact le_max_of_le_left (by
            have := hC0 0
            simp at this
            exact le_trans (by positivity) this)
      _ = max C0 C1 * (1 + ‖z‖) ^ (-b') := by ring
  · intro z
    have h1 := hC1 z
    have hz : 0 < 1 + ‖z‖ := by positivity
    have h2 : (1 + ‖z‖) ^ (-(k : ℝ)) * (1 + ‖z‖) ^ k = 1 := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hz]; simp
    have h3 : (1 + ‖z‖) ^ (-(b' + ℓ)) ≥ (1 + ‖z‖) ^ (-(k : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith [norm_nonneg z]) (by linarith)
    have hC0' : 0 ≤ max C0 C1 := by
      refine le_max_of_le_left ?_
      have := hC0 0
      simp at this
      exact le_trans (by positivity) this
    calc ‖iteratedFDeriv ℝ ℓ (⇑φ) z‖
        = (1 + ‖z‖) ^ (-(k : ℝ)) * ((1 + ‖z‖) ^ k * ‖iteratedFDeriv ℝ ℓ (⇑φ) z‖) := by
          rw [← mul_assoc, h2, one_mul]
      _ ≤ (1 + ‖z‖) ^ (-(k : ℝ)) * max C0 C1 := by
          apply mul_le_mul_of_nonneg_left (h1.trans (le_max_right _ _)) (by positivity)
      _ ≤ (1 + ‖z‖) ^ (-(b' + ℓ)) * max C0 C1 := mul_le_mul_of_nonneg_right h3 hC0'
      _ = max C0 C1 * (1 + ‖z‖) ^ (-(b' + ℓ)) := by ring

end HRS.U8
