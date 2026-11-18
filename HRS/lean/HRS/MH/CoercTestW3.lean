import Mathlib
import HRS.Whole.AppendixALemmas
import HRS.MH.CoercLowerDefs
import HRS.MH.CoercLowerFinal
import HRS.MH.CoercTestSpecDefs

noncomputable section

open MeasureTheory
open scoped BigOperators FourierTransform

namespace HRS.MH.CoercTest

open HRS.MH.CoercLower

variable {d N : ℕ}

/-- The weight constant: `wS s t = κ s * t^(s/2-1)` for `t > 0`. -/
def p_wt3_kappa (s : ℝ) : ℝ := if s = 0 then 1 / 2 else 1 / Real.Gamma (s / 2)

lemma p_wt3_kappa_pos {s : ℝ} (hs0 : 0 ≤ s) : 0 < p_wt3_kappa s := by
  unfold p_wt3_kappa
  split_ifs with h
  · norm_num
  · have : 0 < s := lt_of_le_of_ne hs0 (Ne.symm h)
    exact one_div_pos.mpr (Real.Gamma_pos_of_pos (by linarith))

lemma p_wt3_wS_eq {s t : ℝ} (ht : 0 < t) : wS s t = p_wt3_kappa s * t ^ (s / 2 - 1) := by
  unfold wS p_wt3_kappa
  split_ifs with h
  · subst h
    simp [Real.rpow_neg_one, div_eq_mul_inv, mul_comm]
  · rw [div_eq_mul_inv, one_div, mul_comm]

lemma p_wt3_wS_nonneg {s : ℝ} (hs0 : 0 ≤ s) {t : ℝ} (ht : 0 < t) : 0 ≤ wS s t := by
  rw [p_wt3_wS_eq ht]
  exact mul_nonneg (p_wt3_kappa_pos hs0).le (Real.rpow_nonneg ht.le _)

/-- [W3a] `0 ≤ M_T` (nonnegative integrand; for `T ≤ 0` the set is empty). -/
theorem Mhat_nonneg {s : ℝ} (hs0 : 0 ≤ s) (T : ℝ) (ξ : Euc d) : 0 ≤ Mhat d s T ξ := by
  unfold Mhat
  refine setIntegral_nonneg measurableSet_Ioc fun t ht => ?_
  have ht0 : 0 < t := ht.1
  exact mul_nonneg (p_wt3_wS_nonneg hs0 ht0)
    (mul_nonneg (Real.rpow_nonneg (div_nonneg Real.pi_pos.le ht0.le) _) (Real.exp_pos _).le)

/-- [W3b] `ξ ↦ M_T(ξ)` is measurable (parametric integral of a jointly measurable function;
`StronglyMeasurable.integral_prod_right'`). -/
theorem measurable_Mhat (d : ℕ) (s T : ℝ) : Measurable (Mhat d s T) := by
  have hm : Measurable (fun p : Euc d × ℝ =>
      wS s p.2 * ((Real.pi / p.2) ^ ((d : ℝ) / 2) * Real.exp (-Real.pi ^ 2 * ‖p.1‖ ^ 2 / p.2))) := by
    by_cases h : s = 0
    · simp only [wS, h, if_true]
      fun_prop
    · simp only [wS, h, if_false]
      fun_prop
  exact (hm.stronglyMeasurable.integral_prod_right' (ν := volume.restrict (Set.Ioc (0 : ℝ) T))).measurable


/-- The `t`-profile `t^{-(a+1)} e^{-β/t}`. -/
def p_wt3_g (a β t : ℝ) : ℝ := t ^ (-(a + 1)) * Real.exp (-β / t)

lemma p_wt3_g_nonneg (a β : ℝ) {t : ℝ} (ht : 0 < t) : 0 ≤ p_wt3_g a β t :=
  mul_nonneg (Real.rpow_nonneg ht.le _) (Real.exp_pos _).le

lemma p_wt3_integrand_eq {s : ℝ} {t : ℝ} (ht : 0 < t) (ξ : Euc d) :
    wS s t * ((Real.pi / t) ^ ((d : ℝ) / 2) * Real.exp (-Real.pi ^ 2 * ‖ξ‖ ^ 2 / t)) =
      (p_wt3_kappa s * Real.pi ^ ((d : ℝ) / 2)) *
        p_wt3_g (((d : ℝ) - s) / 2) (Real.pi ^ 2 * ‖ξ‖ ^ 2) t := by
  have h1 : t ^ (-((((d : ℝ) - s) / 2) + 1)) = t ^ (s / 2 - 1) * (t ^ ((d : ℝ) / 2))⁻¹ := by
    rw [← Real.rpow_neg ht.le, ← Real.rpow_add ht]
    congr 1
    ring
  have h2 : -Real.pi ^ 2 * ‖ξ‖ ^ 2 / t = -(Real.pi ^ 2 * ‖ξ‖ ^ 2) / t := by ring
  rw [p_wt3_wS_eq ht, Real.div_rpow Real.pi_pos.le ht.le, p_wt3_g, h1, h2]
  ring

lemma p_wt3_integrableOn {a β : ℝ} (T : ℝ) (ha : 0 < a) (hβ : 0 < β) :
    IntegrableOn (p_wt3_g a β) (Set.Ioc 0 T) := by
  set m : ℕ := ⌈a + 1⌉₊ with hm
  have hma : a + 1 ≤ (m : ℝ) := Nat.le_ceil _
  have hmeas : Measurable (p_wt3_g a β) := by
    unfold p_wt3_g
    fun_prop
  refine Measure.integrableOn_of_bounded (M := (m.factorial : ℝ) / β ^ m * T ^ ((m : ℝ) - (a + 1)))
    (by simp) hmeas.aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall fun t ht => ?_)
  have ht0 : 0 < t := ht.1
  have htT : t ≤ T := ht.2
  rw [Real.norm_of_nonneg (p_wt3_g_nonneg a β ht0)]
  have hx : 0 < β / t := div_pos hβ ht0
  have hfac : (0 : ℝ) < m.factorial := by exact_mod_cast Nat.factorial_pos m
  have hexp : Real.exp (-β / t) ≤ (m.factorial : ℝ) * (t / β) ^ m := by
    have h := Real.pow_div_factorial_le_exp (β / t) hx.le m
    have hpos : 0 < (β / t) ^ m / m.factorial := div_pos (pow_pos hx m) hfac
    have h' := inv_anti₀ hpos h
    rw [neg_div, Real.exp_neg]
    calc (Real.exp (β / t))⁻¹ ≤ ((β / t) ^ m / m.factorial)⁻¹ := h'
      _ = (m.factorial : ℝ) * (t / β) ^ m := by
        rw [inv_div, div_eq_mul_inv, ← inv_pow, inv_div]
  have hpow : t ^ (-(a + 1)) * t ^ m = t ^ ((m : ℝ) - (a + 1)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add ht0]
    congr 1
    ring
  have hT' : t ^ ((m : ℝ) - (a + 1)) ≤ T ^ ((m : ℝ) - (a + 1)) :=
    Real.rpow_le_rpow ht0.le htT (by linarith)
  calc p_wt3_g a β t = t ^ (-(a + 1)) * Real.exp (-β / t) := rfl
    _ ≤ t ^ (-(a + 1)) * ((m.factorial : ℝ) * (t / β) ^ m) :=
        mul_le_mul_of_nonneg_left hexp (Real.rpow_nonneg ht0.le _)
    _ = (m.factorial : ℝ) / β ^ m * (t ^ (-(a + 1)) * t ^ m) := by
        rw [div_pow]; field_simp
    _ = (m.factorial : ℝ) / β ^ m * t ^ ((m : ℝ) - (a + 1)) := by rw [hpow]
    _ ≤ (m.factorial : ℝ) / β ^ m * T ^ ((m : ℝ) - (a + 1)) :=
        mul_le_mul_of_nonneg_left hT' (div_nonneg hfac.le (pow_pos hβ m).le)

lemma p_wt3_core {a β T ℓ : ℝ} (ha : 0 < a) (hβ : 0 < β) (hℓ : 0 < ℓ) (hT : 2 * ℓ ≤ T) :
    ℓ * ((2 * ℓ) ^ (-(a + 1)) * Real.exp (-β / ℓ)) ≤ ∫ t in Set.Ioc (0 : ℝ) T, p_wt3_g a β t := by
  have hint := p_wt3_integrableOn T ha hβ
  have hsub : Set.Icc ℓ (2 * ℓ) ⊆ Set.Ioc 0 T := fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩
  calc ℓ * ((2 * ℓ) ^ (-(a + 1)) * Real.exp (-β / ℓ))
      = ((2 * ℓ) ^ (-(a + 1)) * Real.exp (-β / ℓ)) * volume.real (Set.Icc ℓ (2 * ℓ)) := by
        rw [Real.volume_real_Icc_of_le (by linarith)]; ring
    _ ≤ ∫ t in Set.Icc ℓ (2 * ℓ), p_wt3_g a β t := by
        refine setIntegral_ge_of_const_le_real measurableSet_Icc (by simp) (fun t ht => ?_)
          (hint.mono_set hsub)
        have ht0 : 0 < t := lt_of_lt_of_le hℓ ht.1
        unfold p_wt3_g
        refine mul_le_mul (Real.rpow_le_rpow_of_nonpos ht0 ht.2 (by linarith)) ?_
          (Real.exp_pos _).le (Real.rpow_nonneg ht0.le _)
        rw [Real.exp_le_exp]
        have : β / t ≤ β / ℓ := div_le_div_of_nonneg_left hβ.le hℓ ht.1
        rw [neg_div, neg_div]; linarith
    _ ≤ ∫ t in Set.Ioc (0 : ℝ) T, p_wt3_g a β t :=
        setIntegral_mono_set hint
          ((ae_restrict_iff' measurableSet_Ioc).2
            (Filter.Eventually.of_forall fun t ht => p_wt3_g_nonneg a β ht.1))
          (HasSubset.Subset.eventuallyLE hsub)

/-- [W3c] Spectral comparison `M_T(ξ) ≥ c (2π‖ξ‖)^{-(d-s)} e^{-2π²‖ξ‖²/T}` for `ξ ≠ 0`, with `c` independent of `T`, `ξ`.
Route: with `β = π²‖ξ‖²` the integrand is `const * t^{-a-1} e^{-β/t}` (`a = (d-s)/2 > 0`); restrict to
`[ℓ, 2ℓ] ⊆ (0,T]`, `ℓ = min(β, T/2)`, and split `β ≤ T/2` / `β > T/2`. -/
theorem Mhat_lower (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) :
    ∃ c : ℝ, 0 < c ∧ ∀ T : ℝ, 0 < T → ∀ ξ : Euc d, ξ ≠ 0 →
      c * (2 * Real.pi * ‖ξ‖) ^ (-((d : ℝ) - s)) * Real.exp (-2 * Real.pi ^ 2 * ‖ξ‖ ^ 2 / T) ≤ Mhat d s T ξ := by
  set a : ℝ := ((d : ℝ) - s) / 2 with ha_def
  have ha : 0 < a := by rw [ha_def]; linarith
  set K : ℝ := p_wt3_kappa s * Real.pi ^ ((d : ℝ) / 2) with hK_def
  have hK : 0 < K := mul_pos (p_wt3_kappa_pos hs0) (Real.rpow_pos_of_pos Real.pi_pos _)
  have h2a : (0 : ℝ) < 2 ^ a := Real.rpow_pos_of_pos two_pos _
  refine ⟨K / 2 * Real.exp (-1) * 2 ^ a, by positivity, ?_⟩
  intro T hT ξ hξ
  have hnorm : 0 < ‖ξ‖ := norm_pos_iff.2 hξ
  obtain ⟨β, hβdef⟩ : ∃ β : ℝ, β = Real.pi ^ 2 * ‖ξ‖ ^ 2 := ⟨_, rfl⟩
  have hβ : 0 < β := by rw [hβdef]; have := Real.pi_pos; positivity
  have hMh : Mhat d s T ξ = K * ∫ t in Set.Ioc (0 : ℝ) T, p_wt3_g a β t := by
    unfold Mhat
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioc (fun t ht => ?_)
    rw [hβdef]
    exact p_wt3_integrand_eq ht.1 ξ
  have hr : (2 * Real.pi * ‖ξ‖) ^ (-((d : ℝ) - s)) = (4 * β) ^ (-a) := by
    have h4 : 4 * β = (2 * Real.pi * ‖ξ‖) ^ (2 : ℕ) := by rw [hβdef]; ring
    rw [h4, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    congr 1
    rw [ha_def]; push_cast; ring
  have hE : -2 * Real.pi ^ 2 * ‖ξ‖ ^ 2 / T = -(2 * β) / T := by rw [hβdef]; ring
  set X : ℝ := (2 * β) ^ (-a) with hX_def
  have hX : 0 < X := Real.rpow_pos_of_pos (by positivity) _
  have h4X : (4 * β) ^ (-a) = (2 ^ a)⁻¹ * X := by
    have : 4 * β = 2 * (2 * β) := by ring
    rw [this, Real.mul_rpow (by norm_num) (by positivity), Real.rpow_neg (by norm_num)]
  set E : ℝ := Real.exp (-(2 * β) / T) with hE_def
  have hE0 : 0 < E := Real.exp_pos _
  have hE1 : E ≤ 1 := by
    rw [hE_def, Real.exp_le_one_iff]
    have : 0 < 2 * β / T := by positivity
    rw [neg_div]; linarith
  have he1 : Real.exp (-1) ≤ 1 := by rw [Real.exp_le_one_iff]; norm_num
  have he0 : 0 < Real.exp (-1) := Real.exp_pos _
  have hlhs : K / 2 * Real.exp (-1) * 2 ^ a * (2 * Real.pi * ‖ξ‖) ^ (-((d : ℝ) - s)) *
      Real.exp (-2 * Real.pi ^ 2 * ‖ξ‖ ^ 2 / T) = K / 2 * Real.exp (-1) * X * E := by
    rw [hr, h4X, hE]
    field_simp
    rw [hE_def, neg_div]
  rw [hMh, hlhs]
  rcases le_or_gt β (T / 2) with hc | hc
  · -- β ≤ T/2
    have hcore := p_wt3_core ha hβ hβ (by linarith : 2 * β ≤ T)
    have e1 : Real.exp (-β / β) = Real.exp (-1) := by
      congr 1; field_simp
    have e2 : (2 * β) ^ (-(a + 1)) = X * (2 * β)⁻¹ := by
      rw [hX_def, show -(a + 1) = -a + (-1) by ring, Real.rpow_add (by positivity),
        Real.rpow_neg_one]
    rw [e1, e2] at hcore
    have hI : X * Real.exp (-1) / 2 ≤ ∫ t in Set.Ioc (0 : ℝ) T, p_wt3_g a β t := by
      refine le_trans (le_of_eq ?_) hcore
      field_simp
    have : K / 2 * Real.exp (-1) * X * E ≤ K / 2 * Real.exp (-1) * X := by
      have : 0 < K / 2 * Real.exp (-1) * X := by positivity
      nlinarith
    nlinarith
  · -- β > T/2
    have hcore := p_wt3_core ha hβ (by linarith : 0 < T / 2) (by linarith : 2 * (T / 2) ≤ T)
    have e1 : Real.exp (-β / (T / 2)) = E := by
      show Real.exp (-β / (T / 2)) = Real.exp (-(2 * β) / T)
      congr 1; field_simp
    have e2 : (2 * (T / 2)) ^ (-(a + 1)) = T ^ (-a) * T⁻¹ := by
      rw [show 2 * (T / 2) = T by ring, show -(a + 1) = -a + (-1) by ring,
        Real.rpow_add hT, Real.rpow_neg_one]
    rw [e1, e2] at hcore
    have hTX : X ≤ T ^ (-a) :=
      Real.rpow_le_rpow_of_nonpos hT (by linarith) (by linarith)
    have hI : T ^ (-a) * E / 2 ≤ ∫ t in Set.Ioc (0 : ℝ) T, p_wt3_g a β t := by
      refine le_trans (le_of_eq ?_) hcore
      field_simp
    have h1 : X * E ≤ T ^ (-a) * E := mul_le_mul_of_nonneg_right hTX hE0.le
    have h2 : K / 2 * Real.exp (-1) * X * E ≤ K / 2 * (X * E) := by
      have : 0 < K / 2 * (X * E) := by positivity
      nlinarith
    nlinarith

end HRS.MH.CoercTest
