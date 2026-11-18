import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.Distribution.TemperateGrowth
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Temperate growth of the high-frequency Riesz symbol (packet CMX-SAMP, helper file 4)

`(1 - χ(ξ)) (2π|ξ|)^{-α}` and the Bessel symbol `(1 + 4π²|ξ|²)^{α/2}` have temperate growth, so
they act on Schwartz functions (`SchwartzMap.smulLeftCLM`).
-/

open Metric Set
open scoped ContDiff

noncomputable section

namespace HRS.Commutator.Whole.SAMP1

variable {d : ℕ}

lemma rpow_le_eight_pow {x : ℝ} (hx1 : 1 / 8 < x) (hx2 : x < 2) (e : ℝ) :
    x ^ e ≤ 8 ^ |e| := by
  have hx0 : 0 < x := by linarith
  rcases le_or_gt 0 e with he | he
  · rw [abs_of_nonneg he]
    calc x ^ e ≤ 2 ^ e := Real.rpow_le_rpow hx0.le hx2.le he
      _ ≤ 8 ^ e := Real.rpow_le_rpow (by norm_num) (by norm_num) he
  · rw [abs_of_neg he]
    calc x ^ e ≤ (1 / 8 : ℝ) ^ e := Real.rpow_le_rpow_of_nonpos (by norm_num) hx1.le he.le
      _ = 8 ^ (-e) := by
          rw [one_div, Real.inv_rpow (by norm_num), ← Real.rpow_neg (by norm_num)]

/-- `y ↦ y^r` has temperate growth on `(1/8, 2)` (bounded derivatives). -/
lemma rpow_temperate_on (r : ℝ) :
    ∀ N : ℕ, ∃ (k : ℕ) (C : ℝ), ∃ (_ : 0 ≤ C), ∀ n ≤ N, ∀ x ∈ Ioo (1 / 8 : ℝ) 2,
      ‖iteratedFDerivWithin ℝ n (fun y : ℝ => y ^ r) (Ioo (1 / 8 : ℝ) 2) x‖ ≤ C * (1 + ‖x‖) ^ k := by
  intro N
  have hu : UniqueDiffOn ℝ (Ioo (1 / 8 : ℝ) 2) := uniqueDiffOn_Ioo _ _
  refine ⟨0, (∑ n ∈ Finset.range (N + 1), ‖Polynomial.eval r (descPochhammer ℝ n)‖) *
    8 ^ (|r| + N), ?_, ?_⟩
  · positivity
  intro n hn x hx
  have hx0 : 0 < x := by linarith [hx.1]
  have : ContDiffAt ℝ n (fun x : ℝ => x ^ r) x := Real.contDiffAt_rpow_const (Or.inl hx0.ne')
  rw [norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin,
    iteratedDerivWithin_eq_iteratedDeriv hu this hx, iteratedDeriv_eq_iterate,
    Real.iter_deriv_rpow_const, norm_mul, pow_zero, mul_one]
  gcongr 1
  · have : n ∈ Finset.range (N + 1) := by simp; omega
    exact Finset.single_le_sum (f := fun n => ‖Polynomial.eval r (descPochhammer ℝ n)‖)
      (fun _ _ => by positivity) this
  · rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hx0.le _)]
    refine (rpow_le_eight_pow hx.1 hx.2 _).trans ?_
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
    have h1 : |r - n| ≤ |r| + |(n : ℝ)| := abs_sub _ _
    have h2 : |(n : ℝ)| = n := abs_of_nonneg (Nat.cast_nonneg n)
    have h3 : (n : ℝ) ≤ N := by exact_mod_cast hn
    linarith


/-- The symbol `(1 - χ(ξ)) (2π|ξ|)^{-α}` has temperate growth (`χ = 1` on the unit ball). -/
theorem hasTemperateGrowth_riesz_cut (b : ContDiffBump (0 : EuclideanSpace ℝ (Fin d)))
    (hb1 : b.rIn = 1) (α : ℝ) :
    Function.HasTemperateGrowth
      (fun ξ : EuclideanSpace ℝ (Fin d) => (1 - b ξ) * (2 * Real.pi * ‖ξ‖) ^ (-α)) := by
  set cut : EuclideanSpace ℝ (Fin d) → ℝ := fun ξ => 1 - b ξ with hcut
  have hcutT : cut.HasTemperateGrowth := by
    have h1 : Function.HasTemperateGrowth (fun ξ : EuclideanSpace ℝ (Fin d) => b ξ) :=
      HasCompactSupport.hasTemperateGrowth b.hasCompactSupport b.contDiff
    exact (Function.HasTemperateGrowth.const 1).sub h1
  let b2 : ContDiffBump (0 : EuclideanSpace ℝ (Fin d)) := ⟨1 / 2, 1, by norm_num, by norm_num⟩
  set ζ : EuclideanSpace ℝ (Fin d) → ℝ := fun ξ => 1 - b2 ξ with hζ
  have hζT : ζ.HasTemperateGrowth := by
    have h1 : Function.HasTemperateGrowth (fun ξ : EuclideanSpace ℝ (Fin d) => b2 ξ) :=
      HasCompactSupport.hasTemperateGrowth b2.hasCompactSupport b2.contDiff
    exact (Function.HasTemperateGrowth.const 1).sub h1
  have heT : Function.HasTemperateGrowth
      (fun ξ : EuclideanSpace ℝ (Fin d) => (1 + ‖ξ‖ ^ 2) ^ (-α / 2)) :=
    Function.hasTemperateGrowth_one_add_norm_sq_rpow _ _
  have hsT : Function.HasTemperateGrowth
      (fun ξ : EuclideanSpace ℝ (Fin d) => (1 + ‖ξ‖ ^ 2) ^ (-1 : ℝ)) :=
    Function.hasTemperateGrowth_one_add_norm_sq_rpow _ _
  set σ : EuclideanSpace ℝ (Fin d) → ℝ := fun ξ => 1 - ζ ξ * (1 + ‖ξ‖ ^ 2) ^ (-1 : ℝ) with hσ
  have hσT : σ.HasTemperateGrowth := by
    have : (fun ξ : EuclideanSpace ℝ (Fin d) => ζ ξ * (1 + ‖ξ‖ ^ 2) ^ (-1 : ℝ)).HasTemperateGrowth :=
      hζT.mul hsT
    exact (Function.HasTemperateGrowth.const 1).sub this
  have hζ_one : ∀ ξ : EuclideanSpace ℝ (Fin d), 1 ≤ ‖ξ‖ → ζ ξ = 1 := by
    intro ξ h
    have : b2 ξ = 0 := b2.zero_of_le_dist (by simpa [b2] using h)
    simp [hζ, this]
  have hζ_zero : ∀ ξ : EuclideanSpace ℝ (Fin d), ‖ξ‖ ≤ 1 / 2 → ζ ξ = 0 := by
    intro ξ h
    have : b2 ξ = 1 := b2.one_of_mem_closedBall (by simpa [b2] using h)
    simp [hζ, this]
  have hζ01 : ∀ ξ, 0 ≤ ζ ξ ∧ ζ ξ ≤ 1 := fun ξ =>
    ⟨by simp [hζ, b2.le_one], by simp [hζ, b2.nonneg]⟩
  have hcut_ne : ∀ ξ, cut ξ ≠ 0 → 1 < ‖ξ‖ := by
    intro ξ hξ
    by_contra h
    push_neg at h
    apply hξ
    have : b ξ = 1 := b.one_of_mem_closedBall (by simp [hb1, h])
    simp [hcut, this]
  have hrange : Set.range σ ⊆ Ioo (1 / 8 : ℝ) 2 := by
    rintro _ ⟨ξ, rfl⟩
    have hs0 : 0 < (1 + ‖ξ‖ ^ 2) ^ (-1 : ℝ) := Real.rpow_pos_of_pos (by positivity) _
    obtain ⟨c0, c1⟩ := hζ01 ξ
    have hsq : (1 + ‖ξ‖ ^ 2) ^ (-1 : ℝ) = (1 + ‖ξ‖ ^ 2)⁻¹ := Real.rpow_neg_one _
    constructor
    · by_cases hr : ‖ξ‖ ≤ 1 / 2
      · simp only [hσ, hζ_zero ξ hr]; norm_num
      · push_neg at hr
        have : (1 + ‖ξ‖ ^ 2)⁻¹ ≤ 4 / 5 := by
          rw [inv_le_comm₀ (by positivity) (by norm_num)]
          nlinarith
        have h2 : ζ ξ * (1 + ‖ξ‖ ^ 2) ^ (-1 : ℝ) ≤ 4 / 5 := by
          rw [hsq]
          calc ζ ξ * (1 + ‖ξ‖ ^ 2)⁻¹ ≤ 1 * (1 + ‖ξ‖ ^ 2)⁻¹ :=
                mul_le_mul_of_nonneg_right c1 (by positivity)
            _ ≤ 4 / 5 := by linarith
        simp only [hσ]; linarith
    · simp only [hσ]
      nlinarith [mul_nonneg c0 hs0.le]
  have hg := Function.HasTemperateGrowth.comp' (g := fun y : ℝ => y ^ (-α / 2)) hrange
    (uniqueDiffOn_Ioo _ _)
    (contDiffOn_id.rpow_const_of_ne fun x hx => (lt_trans (by norm_num) hx.1).ne')
    (rpow_temperate_on _) hσT
  have hfull := ((Function.HasTemperateGrowth.const ((2 * Real.pi) ^ (-α))).mul
    (hcutT.mul (heT.mul hg)))
  have heq : (fun ξ : EuclideanSpace ℝ (Fin d) => (1 - b ξ) * (2 * Real.pi * ‖ξ‖) ^ (-α)) =
      (fun _ => (2 * Real.pi) ^ (-α)) * (cut * ((fun ξ : EuclideanSpace ℝ (Fin d) =>
        (1 + ‖ξ‖ ^ 2) ^ (-α / 2)) * ((fun y : ℝ => y ^ (-α / 2)) ∘ σ))) := by
    funext ξ
    by_cases hc : cut ξ = 0
    · have : 1 - b ξ = 0 := hc
      simp [this, hc]
    · have hr := hcut_ne ξ hc
      have hr0 : 0 < ‖ξ‖ := by linarith
      have h1 : σ ξ = ‖ξ‖ ^ 2 / (1 + ‖ξ‖ ^ 2) := by
        simp only [hσ, hζ_one ξ hr.le, Real.rpow_neg_one]
        field_simp; ring
      simp only [Pi.mul_apply, Function.comp, h1]
      have h2 : (1 + ‖ξ‖ ^ 2) ^ (-α / 2) * (‖ξ‖ ^ 2 / (1 + ‖ξ‖ ^ 2)) ^ (-α / 2) = ‖ξ‖ ^ (-α) := by
        rw [← Real.mul_rpow (by positivity) (by positivity)]
        have : (1 + ‖ξ‖ ^ 2) * (‖ξ‖ ^ 2 / (1 + ‖ξ‖ ^ 2)) = ‖ξ‖ ^ 2 := by field_simp
        rw [this, ← Real.rpow_natCast, ← Real.rpow_mul hr0.le]
        congr 1; push_cast; ring
      rw [Real.mul_rpow (by positivity) hr0.le, ← h2]
      show _ = _ * (cut ξ * _)
      simp only [hcut]
      ring
  rw [heq]; exact hfull


theorem schwartz_riesz_cut (b : ContDiffBump (0 : EuclideanSpace ℝ (Fin d)))
    (hb1 : b.rIn = 1) (α : ℝ) (Φ : SchwartzMap (EuclideanSpace ℝ (Fin d)) ℂ) :
    ∃ S : SchwartzMap (EuclideanSpace ℝ (Fin d)) ℂ, ∀ ξ,
      S ξ = ((((1 - b ξ) * (2 * Real.pi * ‖ξ‖) ^ (-α) : ℝ)) : ℂ) * Φ ξ := by
  have hT : Function.HasTemperateGrowth (fun ξ : EuclideanSpace ℝ (Fin d) =>
      ((((1 - b ξ) * (2 * Real.pi * ‖ξ‖) ^ (-α) : ℝ)) : ℂ)) :=
    Complex.hasTemperateGrowth_ofReal.comp (hasTemperateGrowth_riesz_cut b hb1 α)
  exact ⟨SchwartzMap.smulLeftCLM ℂ (fun ξ : EuclideanSpace ℝ (Fin d) =>
      ((((1 - b ξ) * (2 * Real.pi * ‖ξ‖) ^ (-α) : ℝ)) : ℂ)) Φ, fun ξ => by
    rw [SchwartzMap.smulLeftCLM_apply_apply hT, smul_eq_mul]⟩

theorem schwartz_bessel (α : ℝ) (Φ : SchwartzMap (EuclideanSpace ℝ (Fin d)) ℂ) :
    ∃ S : SchwartzMap (EuclideanSpace ℝ (Fin d)) ℂ, ∀ ξ,
      S ξ = ((((1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ (α / 2) : ℝ)) : ℂ) * Φ ξ := by
  have h1 : Function.HasTemperateGrowth (fun ξ : EuclideanSpace ℝ (Fin d) =>
      (1 + ‖(2 * Real.pi) • ξ‖ ^ 2) ^ (α / 2)) :=
    (Function.hasTemperateGrowth_one_add_norm_sq_rpow (EuclideanSpace ℝ (Fin d)) (α / 2)).comp
      (((2 * Real.pi) • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin d))).hasTemperateGrowth)
  have h2 : ∀ ξ : EuclideanSpace ℝ (Fin d),
      (1 + ‖(2 * Real.pi) • ξ‖ ^ 2) ^ (α / 2) = (1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ (α / 2) := by
    intro ξ
    rw [norm_smul, Real.norm_of_nonneg (by positivity), mul_pow]; ring_nf
  have hT : Function.HasTemperateGrowth (fun ξ : EuclideanSpace ℝ (Fin d) =>
      ((((1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ (α / 2) : ℝ)) : ℂ)) := by
    have := Complex.hasTemperateGrowth_ofReal.comp h1
    simpa [Function.comp_def, h2] using this
  exact ⟨SchwartzMap.smulLeftCLM ℂ (fun ξ : EuclideanSpace ℝ (Fin d) =>
      ((((1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ (α / 2) : ℝ)) : ℂ)) Φ, fun ξ => by
    rw [SchwartzMap.smulLeftCLM_apply_apply hT, smul_eq_mul]⟩

end HRS.Commutator.Whole.SAMP1
