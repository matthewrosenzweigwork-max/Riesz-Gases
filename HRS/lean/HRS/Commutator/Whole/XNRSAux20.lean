import HRS.Commutator.Whole.XNRSAux19

/-!
# Packet X-NRS, part 20: `L¹`-translation estimate for Schwartz functions
-/

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal FourierTransform ContDiff SchwartzMap LineDeriv

noncomputable section

namespace HRS.Commutator.Whole.XNRS

variable {d : ℕ}

lemma xschw_decay_fderiv (f : 𝓢(Euc d, ℂ)) (k : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x, (1 + ‖x‖) ^ k * ‖fderiv ℝ f x‖ ≤ M := by
  refine ⟨2 ^ k * (Finset.Iic (k, 1)).sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) f, by positivity,
    fun x => ?_⟩
  have := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (k, 1)) (k := k) (n := 1)
    le_rfl le_rfl f x
  rwa [norm_iteratedFDeriv_one] at this

lemma xtrans_le (f : 𝓢(Euc d, ℂ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : Euc d, ∫ x, ‖f (x - t) - f x‖ ≤ C * min 1 ‖t‖ := by
  obtain ⟨M, hM0, hM⟩ := xschw_decay_fderiv f (d + 1)
  have hint : Integrable (fun x : Euc d => (1 + ‖x‖) ^ (-((d + 1 : ℕ) : ℝ))) :=
    integrable_one_add_norm (μ := volume) (by
      rw [show Module.finrank ℝ (Euc d) = d by simp [Euc]]; push_cast; linarith)
  set B : ℝ := M * 2 ^ (d + 1) * ∫ x : Euc d, (1 + ‖x‖) ^ (-((d + 1 : ℕ) : ℝ)) with hB
  set N : ℝ := ∫ x, ‖f x‖ with hN
  have hN0 : 0 ≤ N := integral_nonneg fun x => norm_nonneg _
  have hB0 : 0 ≤ B := by
    rw [hB]; exact mul_nonneg (by positivity) (integral_nonneg fun x => by positivity)
  refine ⟨max B (2 * N), le_max_of_le_left hB0, fun t => ?_⟩
  by_cases ht : ‖t‖ ≤ 1
  · rw [min_eq_right ht]
    have hpt : ∀ x : Euc d, ‖f (x - t) - f x‖ ≤
        (M * 2 ^ (d + 1) * (1 + ‖x‖) ^ (-((d + 1 : ℕ) : ℝ))) * ‖t‖ := by
      intro x
      have hmv := (convex_closedBall x 1).norm_image_sub_le_of_norm_fderiv_le
        (f := fun y => f y) (C := M * 2 ^ (d + 1) * (1 + ‖x‖) ^ (-((d + 1 : ℕ) : ℝ)))
        (fun y _ => f.differentiableAt) (fun y hy => ?_) (x := x) (y := x - t)
        (mem_closedBall_self zero_le_one) (by simpa [mem_closedBall, dist_eq_norm] using ht)
      · simpa using hmv
      · have hy1 : 1 + ‖x‖ ≤ 2 * (1 + ‖y‖) := by
          have : ‖x‖ ≤ ‖y‖ + 1 := by
            have := norm_sub_norm_le x y
            have h2 : ‖x - y‖ ≤ 1 := by simpa [mem_closedBall, dist_eq_norm, norm_sub_rev] using hy
            linarith
          have := norm_nonneg y
          linarith
        have hpos : 0 < (1 + ‖y‖) := by positivity
        have h1 := hM y
        have h3 : (1 + ‖x‖) ^ (d + 1) * ‖fderiv ℝ (fun y => f y) y‖ ≤ M * 2 ^ (d + 1) := by
          calc (1 + ‖x‖) ^ (d + 1) * ‖fderiv ℝ (fun y => f y) y‖
              ≤ (2 * (1 + ‖y‖)) ^ (d + 1) * ‖fderiv ℝ (fun y => f y) y‖ := by gcongr
            _ = 2 ^ (d + 1) * ((1 + ‖y‖) ^ (d + 1) * ‖fderiv ℝ (fun y => f y) y‖) := by
                rw [mul_pow]; ring
            _ ≤ 2 ^ (d + 1) * M := by gcongr
            _ = _ := by ring
        have hxpos : 0 < (1 + ‖x‖) := by positivity
        rw [Real.rpow_neg hxpos.le, Real.rpow_natCast, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
        linarith
    have hmaj : Integrable (fun x : Euc d => (M * 2 ^ (d + 1) * (1 + ‖x‖) ^ (-((d + 1 : ℕ) : ℝ))) * ‖t‖) :=
      (hint.const_mul _).mul_const _
    have hmeas : AEStronglyMeasurable (fun x : Euc d => ‖f (x - t) - f x‖) volume :=
      ((f.continuous.comp (continuous_id.sub continuous_const)).sub f.continuous).norm.aestronglyMeasurable
    calc ∫ x, ‖f (x - t) - f x‖
        ≤ ∫ x : Euc d, (M * 2 ^ (d + 1) * (1 + ‖x‖) ^ (-((d + 1 : ℕ) : ℝ))) * ‖t‖ :=
          integral_mono_of_nonneg (Eventually.of_forall fun x => norm_nonneg _) hmaj
            (Eventually.of_forall hpt)
      _ = B * ‖t‖ := by rw [integral_mul_const, integral_const_mul]
      _ ≤ max B (2 * N) * ‖t‖ := mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
  · push Not at ht
    rw [min_eq_left ht.le, mul_one]
    have h1 : Integrable (fun x : Euc d => ‖f (x - t)‖) :=
      (f.integrable.comp_sub_right t).norm
    have h2 : ∫ x : Euc d, ‖f (x - t)‖ = N := integral_sub_right_eq_self (fun x => ‖f x‖) t
    calc ∫ x, ‖f (x - t) - f x‖ ≤ ∫ x, (‖f (x - t)‖ + ‖f x‖) :=
          integral_mono_of_nonneg (Eventually.of_forall fun x => norm_nonneg _)
            (h1.add f.integrable.norm) (Eventually.of_forall fun x => norm_sub_le _ _)
      _ = 2 * N := by rw [integral_add h1 f.integrable.norm, h2]; ring
      _ ≤ max B (2 * N) := le_max_right _ _

end HRS.Commutator.Whole.XNRS
