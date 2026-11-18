import HRS.Commutator.Torus.LEIBTAux3

/-!
# LEIB-T helpers, part 4: derivative bounds for the symbol difference `m(a + tζ) - m(a)`
-/

noncomputable section

open MeasureTheory Filter Topology Metric Set
open scoped ENNReal NNReal BigOperators FourierTransform ContDiff SchwartzMap

namespace HRS.Commutator.TorusNote

open HRS

variable {d : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin d)

/-- The Bessel symbol `m(ξ) = (1 + 4π²|ξ|²)^{α/2}` (as a complex-valued function). -/
abbrev leibt_m (α : ℝ) : 𝔼 → ℂ := HRS.Commutator.Whole.XLI.bsymX α

/-- The difference of symbols `ζ ↦ m(a + tζ) - m(a)`. -/
def leibt_theta (α : ℝ) (a : 𝔼) (t : ℝ) (ζ : 𝔼) : ℂ := leibt_m α (a + t • ζ) - leibt_m α a

lemma leibt_theta_bound (α : ℝ) (n₀ : ℕ) :
    ∃ (C : ℝ) (k : ℕ), 0 ≤ C ∧ ∀ (a : 𝔼) (t : ℝ), 0 < t → t ≤ 1 → ∀ n ≤ n₀, ∀ ζ : 𝔼,
      ‖iteratedFDeriv ℝ n (leibt_theta α a t) ζ‖ ≤
        C * t * (1 + ‖a‖) ^ k * (1 + ‖ζ‖) ^ (k + 1) := by
  have hT := HRS.Commutator.Whole.XLI.bsymX_temperate (d := d) α
  obtain ⟨k₀, C₀, hC₀, hb⟩ := hT.norm_iteratedFDeriv_le_uniform (max n₀ 1)
  refine ⟨C₀, k₀, hC₀, fun a t ht ht1 n hn ζ => ?_⟩
  have hsm : ContDiff ℝ ∞ (leibt_m α : 𝔼 → ℂ) := hT.1
  have h1a : (1 : ℝ) ≤ 1 + ‖a‖ := by linarith [norm_nonneg a]
  have h1z : (1 : ℝ) ≤ 1 + ‖ζ‖ := by linarith [norm_nonneg ζ]
  have hprod : 1 + ‖a + t • ζ‖ ≤ (1 + ‖a‖) * (1 + ‖ζ‖) := by
    have : ‖a + t • ζ‖ ≤ ‖a‖ + ‖ζ‖ := by
      calc ‖a + t • ζ‖ ≤ ‖a‖ + ‖t • ζ‖ := norm_add_le _ _
        _ ≤ ‖a‖ + ‖ζ‖ := by
          gcongr
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht]
          calc t * ‖ζ‖ ≤ 1 * ‖ζ‖ := by gcongr
            _ = ‖ζ‖ := one_mul _
    nlinarith [norm_nonneg a, norm_nonneg ζ]
  rcases Nat.eq_zero_or_pos n with rfl | hnpos
  · -- n = 0: mean value inequality
    rw [norm_iteratedFDeriv_zero]
    unfold leibt_theta
    set B : ℝ := C₀ * ((1 + ‖a‖) * (1 + ‖ζ‖)) ^ k₀ with hB
    have hbound : ∀ x ∈ Metric.closedBall a (t * ‖ζ‖), ‖fderiv ℝ (leibt_m α) x‖ ≤ B := by
      intro x hx
      have hx1 : ‖x‖ ≤ ‖a‖ + t * ‖ζ‖ := by
        have := mem_closedBall_iff_norm.1 hx
        calc ‖x‖ = ‖(x - a) + a‖ := by rw [sub_add_cancel]
          _ ≤ ‖x - a‖ + ‖a‖ := norm_add_le _ _
          _ ≤ t * ‖ζ‖ + ‖a‖ := by linarith
          _ = ‖a‖ + t * ‖ζ‖ := by ring
      have h2 := hb 1 (by omega) x
      rw [norm_iteratedFDeriv_one] at h2
      refine h2.trans ?_
      rw [hB]
      gcongr
      have : t * ‖ζ‖ ≤ ‖ζ‖ := by
        calc t * ‖ζ‖ ≤ 1 * ‖ζ‖ := by gcongr
          _ = ‖ζ‖ := one_mul _
      nlinarith [norm_nonneg a, norm_nonneg ζ]
    have hmv := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) (f := leibt_m α)
      (s := Metric.closedBall a (t * ‖ζ‖)) (x := a) (y := a + t • ζ)
      (fun x _ => (hsm.differentiable (by simp)) x) hbound (convex_closedBall _ _)
      (Metric.mem_closedBall_self (by positivity))
      (by
        rw [mem_closedBall_iff_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos ht])
    rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos ht] at hmv
    refine hmv.trans ?_
    rw [hB, mul_pow]
    have e1 : (1 + ‖ζ‖) ^ (k₀ + 1) = (1 + ‖ζ‖) ^ k₀ * (1 + ‖ζ‖) := pow_succ _ _
    have e2 : ‖ζ‖ ≤ 1 + ‖ζ‖ := by linarith
    calc C₀ * ((1 + ‖a‖) ^ k₀ * (1 + ‖ζ‖) ^ k₀) * (t * ‖ζ‖)
        = C₀ * t * (1 + ‖a‖) ^ k₀ * ((1 + ‖ζ‖) ^ k₀ * ‖ζ‖) := by ring
      _ ≤ C₀ * t * (1 + ‖a‖) ^ k₀ * ((1 + ‖ζ‖) ^ k₀ * (1 + ‖ζ‖)) := by gcongr
      _ = _ := by rw [e1]
  · -- n ≥ 1: the constant disappears, scaling gives `t^n`
    have hg : ContDiff ℝ ∞ (fun z : 𝔼 => leibt_m α (a + z)) := hsm.comp (contDiff_const.add contDiff_id)
    have hg2 : ContDiff ℝ ∞ (fun z : 𝔼 => leibt_m α (a + t • z)) :=
      hsm.comp (contDiff_const.add (contDiff_id.const_smul t))
    have hth : leibt_theta α a t = (fun z : 𝔼 => leibt_m α (a + t • z)) - fun _ => leibt_m α a := rfl
    have e1 : iteratedFDeriv ℝ n (leibt_theta α a t) ζ = iteratedFDeriv ℝ n (fun z : 𝔼 => leibt_m α (a + t • z)) ζ := by
      rw [hth, iteratedFDeriv_sub_apply (hg2.of_le (by exact_mod_cast le_top)).contDiffAt contDiffAt_const,
        iteratedFDeriv_const_of_ne (by omega), Pi.zero_apply, sub_zero]
    have e2 : iteratedFDeriv ℝ n (fun z : 𝔼 => leibt_m α (a + t • z)) ζ =
        t ^ n • iteratedFDeriv ℝ n (fun z : 𝔼 => leibt_m α (a + z)) (t • ζ) := by
      have := iteratedFDeriv_comp_const_smul (𝕜 := ℝ) (i := n) (f := fun z : 𝔼 => leibt_m α (a + z)) t
        (hg.of_le (by exact_mod_cast le_top))
      exact congrFun this ζ
    have e3 : iteratedFDeriv ℝ n (fun z : 𝔼 => leibt_m α (a + z)) (t • ζ) =
        iteratedFDeriv ℝ n (leibt_m α) (a + t • ζ) := iteratedFDeriv_comp_add_left n a (t • ζ)
    rw [e1, e2, e3, norm_smul, norm_pow, Real.norm_eq_abs, abs_of_pos ht]
    have h2 := hb n (le_trans hn (le_max_left _ _)) (a + t • ζ)
    have htn : t ^ n ≤ t := by
      calc t ^ n ≤ t ^ 1 := pow_le_pow_of_le_one ht.le ht1 hnpos
        _ = t := pow_one t
    calc t ^ n * ‖iteratedFDeriv ℝ n (leibt_m α) (a + t • ζ)‖
        ≤ t * (C₀ * (1 + ‖a + t • ζ‖) ^ k₀) := by gcongr
      _ ≤ t * (C₀ * ((1 + ‖a‖) * (1 + ‖ζ‖)) ^ k₀) := by gcongr
      _ = C₀ * t * (1 + ‖a‖) ^ k₀ * (1 + ‖ζ‖) ^ k₀ := by rw [mul_pow]; ring
      _ ≤ C₀ * t * (1 + ‖a‖) ^ k₀ * (1 + ‖ζ‖) ^ (k₀ + 1) := by
        gcongr
        exact Nat.le_succ _

end HRS.Commutator.TorusNote
