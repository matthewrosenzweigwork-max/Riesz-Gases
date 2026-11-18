import HRS.Whole.MovtrAux7

/-!
# MOVTR auxiliary 8: Sobolev bounds of translates, Gaussian moments
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole

variable {d : ℕ}

/-- Uniform Gaussian bound on the derivatives up to order `K`. -/
lemma movtr_gaussUpTo {ρ : Euc d → ℝ}
    (hgauss : ∀ k : ℕ, ∃ C c : ℝ, 0 < c ∧ ∀ x, ‖iteratedFDeriv ℝ k ρ x‖ ≤ C * Real.exp (-c * ‖x‖ ^ 2))
    (K : ℕ) : ∃ C c : ℝ, 0 ≤ C ∧ 0 < c ∧
      ∀ n ≤ K, ∀ x, ‖iteratedFDeriv ℝ n ρ x‖ ≤ C * Real.exp (-c * ‖x‖ ^ 2) := by
  induction K with
  | zero =>
    obtain ⟨C, c, hc, h⟩ := hgauss 0
    refine ⟨max C 0, c, le_max_right _ _, hc, fun n hn x => ?_⟩
    have : n = 0 := by omega
    subst this
    exact (h x).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)
  | succ K ih =>
    obtain ⟨C, c, hC, hc, h⟩ := ih
    obtain ⟨C', c', hc', h'⟩ := hgauss (K + 1)
    refine ⟨max C (max C' 0), min c c', le_max_of_le_right (le_max_right _ _), lt_min hc hc',
      fun n hn x => ?_⟩
    have hexp : ∀ c₀ : ℝ, min c c' ≤ c₀ →
        Real.exp (-c₀ * ‖x‖ ^ 2) ≤ Real.exp (-(min c c') * ‖x‖ ^ 2) := fun c₀ hc₀ => by
      apply Real.exp_le_exp.mpr
      nlinarith [sq_nonneg ‖x‖]
    by_cases hn' : n ≤ K
    · refine (h n hn' x).trans ?_
      calc C * Real.exp (-c * ‖x‖ ^ 2) ≤ max C (max C' 0) * Real.exp (-c * ‖x‖ ^ 2) :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le
        _ ≤ _ := mul_le_mul_of_nonneg_left (hexp c (min_le_left _ _))
              (le_trans hC (le_max_left _ _))
    · have : n = K + 1 := by omega
      subst this
      refine (h' x).trans ?_
      calc C' * Real.exp (-c' * ‖x‖ ^ 2) ≤ max C (max C' 0) * Real.exp (-c' * ‖x‖ ^ 2) :=
            mul_le_mul_of_nonneg_right (le_trans (le_max_left _ _) (le_max_right _ _))
              (Real.exp_pos _).le
        _ ≤ _ := mul_le_mul_of_nonneg_left (hexp c' (min_le_right _ _))
              (le_trans hC (le_max_left _ _))

lemma movtr_memLp_gauss (hd : 1 ≤ d) {c : ℝ} (hc : 0 < c) {p : ℝ≥0∞} (hp : 1 ≤ p) :
    MemLp (fun x : Euc d => Real.exp (-c * ‖x‖ ^ 2)) p := by
  have hmeas : AEStronglyMeasurable (fun x : Euc d => Real.exp (-c * ‖x‖ ^ 2)) volume :=
    (Real.continuous_exp.comp (continuous_const.mul (continuous_norm.pow 2))).aestronglyMeasurable
  by_cases hpt : p = (⊤ : ℝ≥0∞)
  · subst hpt
    refine memLp_top_of_bound hmeas 1 (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_one_iff.mpr
    nlinarith [sq_nonneg ‖x‖]
  · have hp0 : p ≠ 0 := by
      intro h; rw [h] at hp; simp at hp
    rw [← integrable_norm_rpow_iff hmeas hp0 hpt]
    have hpr : 0 < p.toReal := ENNReal.toReal_pos hp0 hpt
    have := movtr_integrable_rpow_gauss (d := d) hd (α := 0) (c := c * p.toReal)
      (by have : (0:ℝ) ≤ d := Nat.cast_nonneg d
          have : (1:ℝ) ≤ d := by exact_mod_cast hd
          linarith) (by positivity)
    refine this.congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [Real.rpow_zero, one_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    rw [← Real.exp_mul]
    congr 1
    ring

/-- A polynomial-Gaussian is dominated by a Gaussian with half the exponent. -/
lemma movtr_poly_gauss_le {c : ℝ} (hc : 0 < c) (K : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    (1 + t) ^ K * Real.exp (-(c / 2) * t ^ 2) ≤ Real.exp ((K : ℝ) ^ 2 / c) * Real.exp (-(c / 4) * t ^ 2) := by
  have h1 : (1 + t) ^ K ≤ Real.exp (K * t) := by
    calc (1 + t) ^ K ≤ (Real.exp t) ^ K := by
          apply pow_le_pow_left₀ (by positivity)
          have := Real.add_one_le_exp t; linarith
      _ = Real.exp (K * t) := by rw [← Real.exp_nat_mul]
  calc (1 + t) ^ K * Real.exp (-(c / 2) * t ^ 2) ≤ Real.exp (K * t) * Real.exp (-(c / 2) * t ^ 2) :=
        mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    _ = Real.exp (K * t + -(c / 2) * t ^ 2) := by rw [Real.exp_add]
    _ ≤ Real.exp ((K : ℝ) ^ 2 / c + -(c / 4) * t ^ 2) := by
        apply Real.exp_le_exp.mpr
        have : (K : ℝ) * t - (c / 4) * t ^ 2 ≤ (K : ℝ) ^ 2 / c := by
          have h2 : 0 ≤ (c / 4) * (t - 2 * K / c) ^ 2 := by positivity
          have h3 : (c / 4) * (t - 2 * K / c) ^ 2 = (c / 4) * t ^ 2 - K * t + (K : ℝ) ^ 2 / c := by
            field_simp
            ring
          linarith
        nlinarith
    _ = _ := by rw [Real.exp_add]


lemma movtr_delta_deriv_bound {ρ : Euc d → ℝ} (hsmooth : ContDiff ℝ ∞ ρ) {C c A : ℝ} (hC : 0 ≤ C)
    (hc : 0 < c) (N : ℕ)
    (hN : ∀ x, ‖iteratedFDeriv ℝ (N + 1) ρ x‖ ≤ C * Real.exp (-c * ‖x‖ ^ 2)) (a x : Euc d)
    (ha : ‖a‖ ≤ A) :
    ‖iteratedFDeriv ℝ N (fun y => ρ (y - a) - ρ y) x‖ ≤
      ‖a‖ * (C * Real.exp (c * A ^ 2) * Real.exp (-(c / 2) * ‖x‖ ^ 2)) := by
  have hcd1 : ContDiff ℝ N (fun y => ρ (y - a)) :=
    (hsmooth.of_le (mod_cast le_top)).comp (contDiff_id.sub contDiff_const)
  have hcd2 : ContDiff ℝ N ρ := hsmooth.of_le (mod_cast le_top)
  rw [show (fun y => ρ (y - a) - ρ y) = (fun y => ρ (y - a)) - ρ from rfl,
    iteratedFDeriv_sub_apply hcd1.contDiffAt hcd2.contDiffAt, iteratedFDeriv_comp_sub]
  have hu : Differentiable ℝ (iteratedFDeriv ℝ N ρ) :=
    hsmooth.differentiable_iteratedFDeriv (by exact_mod_cast WithTop.coe_lt_coe.mpr (by exact_mod_cast ENat.coe_lt_top N))
  set B : ℝ := C * Real.exp (c * A ^ 2) * Real.exp (-(c / 2) * ‖x‖ ^ 2) with hB
  have hmv := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) (f := iteratedFDeriv ℝ N ρ)
    (C := B) (s := Metric.closedBall x ‖a‖) (x := x) (y := x - a)
    (fun z _ => hu z) ?_ (convex_closedBall x ‖a‖) (Metric.mem_closedBall_self (norm_nonneg a)) ?_
  · have e : x - a - x = -a := by abel
    rw [e, norm_neg] at hmv
    calc _ ≤ B * ‖a‖ := hmv
      _ = _ := by rw [mul_comm]
  · intro z hz
    rw [norm_fderiv_iteratedFDeriv]
    refine (hN z).trans ?_
    have hzx : ‖x - z‖ ≤ A := by
      have : dist z x ≤ ‖a‖ := Metric.mem_closedBall.mp hz
      rw [dist_eq_norm] at this
      rw [norm_sub_rev]
      exact this.trans ha
    have := movtr_gauss_shift hc hzx x
    have e : x - z - x = -z := by abel
    rw [e, norm_neg] at this
    rw [hB, mul_assoc]
    exact mul_le_mul_of_nonneg_left this hC
  · rw [Metric.mem_closedBall, dist_eq_norm]
    simp


lemma movtr_bracket_temperate (ℓ : ℕ) :
    Function.HasTemperateGrowth (fun x : Euc d => movBracket x ^ ℓ) := by
  have h := (Function.hasTemperateGrowth_one_add_norm_sq_rpow (Euc d) (1 / 2 : ℝ)).pow ℓ
  have e : (fun x : Euc d => movBracket x ^ ℓ) =
      (fun x : Euc d => (1 + ‖x‖ ^ 2) ^ (1 / 2 : ℝ)) ^ ℓ := by
    funext x
    simp [movBracket, Real.sqrt_eq_rpow]
  rw [e]
  exact h

/-- The weighted Sobolev bound for the translation difference, uniform for `‖a‖ ≤ A`. -/
theorem movtr_sobolev (hd : 1 ≤ d) {ρ : Euc d → ℝ} (hsmooth : ContDiff ℝ ∞ ρ)
    (hgauss : ∀ k : ℕ, ∃ C c : ℝ, 0 < c ∧ ∀ x, ‖iteratedFDeriv ℝ k ρ x‖ ≤ C * Real.exp (-c * ‖x‖ ^ 2))
    (k ℓ : ℕ) (p : ℝ≥0∞) (hp : 1 ≤ p) (A : ℝ) :
    ∃ C : ℝ, ∀ a : Euc d, ‖a‖ ≤ A →
      ∑ i ∈ Finset.range (k + 1), eLpNorm
        (fun x => ‖iteratedFDeriv ℝ i (fun x => movBracket x ^ ℓ * (ρ (x - a) - ρ x)) x‖) p volume ≤
        ENNReal.ofReal (C * ‖a‖) := by
  have hwtg := movtr_bracket_temperate (d := d) ℓ
  obtain ⟨Kw, Cw, hCw, hw⟩ := hwtg.norm_iteratedFDeriv_le_uniform k
  obtain ⟨C, c, hC, hc, hder⟩ := movtr_gaussUpTo hgauss (k + 1)
  set B₁ : ℝ := C * Real.exp (c * A ^ 2) with hB₁
  set M : ℝ := 2 ^ k * Cw * B₁ * Real.exp ((Kw : ℝ) ^ 2 / c) with hM
  have hMnn : 0 ≤ M := by positivity
  have hG := (movtr_memLp_gauss (d := d) hd (c := c / 4) (by positivity) hp)
  set G : ℝ≥0∞ := eLpNorm (fun x : Euc d => Real.exp (-(c / 4) * ‖x‖ ^ 2)) p volume with hGdef
  have hGfin : G ≠ ⊤ := hG.eLpNorm_ne_top
  refine ⟨(k + 1 : ℝ) * M * G.toReal, fun a ha => ?_⟩
  have hcdw : ContDiff ℝ ∞ (fun x : Euc d => movBracket x ^ ℓ) := hwtg.1
  have hcdδ : ContDiff ℝ ∞ (fun x : Euc d => ρ (x - a) - ρ x) :=
    (hsmooth.comp (contDiff_id.sub contDiff_const)).sub hsmooth
  have hcdf : ContDiff ℝ ∞ (fun x : Euc d => movBracket x ^ ℓ * (ρ (x - a) - ρ x)) :=
    hcdw.mul hcdδ
  have hpt : ∀ i ≤ k, ∀ x : Euc d,
      ‖iteratedFDeriv ℝ i (fun x => movBracket x ^ ℓ * (ρ (x - a) - ρ x)) x‖ ≤
        ‖a‖ * M * Real.exp (-(c / 4) * ‖x‖ ^ 2) := by
    intro i hi x
    have hleib := norm_iteratedFDeriv_mul_le (𝕜 := ℝ) (f := fun x : Euc d => movBracket x ^ ℓ)
      (g := fun x : Euc d => ρ (x - a) - ρ x) (N := i) (hcdw.of_le (mod_cast le_top))
      (hcdδ.of_le (mod_cast le_top)) x le_rfl
    refine hleib.trans ?_
    have hterm : ∀ j ∈ Finset.range (i + 1),
        (i.choose j : ℝ) * ‖iteratedFDeriv ℝ j (fun x : Euc d => movBracket x ^ ℓ) x‖ *
          ‖iteratedFDeriv ℝ (i - j) (fun x : Euc d => ρ (x - a) - ρ x) x‖ ≤
        (i.choose j : ℝ) * (Cw * (1 + ‖x‖) ^ Kw) *
          (‖a‖ * (B₁ * Real.exp (-(c / 2) * ‖x‖ ^ 2))) := by
      intro j hj
      have hj' : j ≤ i := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      have h1 := hw j (hj'.trans hi) x
      have h2 := movtr_delta_deriv_bound hsmooth hC hc (i - j)
        (fun y => hder (i - j + 1) (by omega) y) a x ha
      have h2' : ‖iteratedFDeriv ℝ (i - j) (fun x : Euc d => ρ (x - a) - ρ x) x‖ ≤
          ‖a‖ * (B₁ * Real.exp (-(c / 2) * ‖x‖ ^ 2)) := by
        refine h2.trans (le_of_eq ?_)
        rw [hB₁]
      have hn1 : 0 ≤ (i.choose j : ℝ) := Nat.cast_nonneg _
      calc (i.choose j : ℝ) * ‖iteratedFDeriv ℝ j (fun x : Euc d => movBracket x ^ ℓ) x‖ *
            ‖iteratedFDeriv ℝ (i - j) (fun x : Euc d => ρ (x - a) - ρ x) x‖
          ≤ (i.choose j : ℝ) * (Cw * (1 + ‖x‖) ^ Kw) *
            ‖iteratedFDeriv ℝ (i - j) (fun x : Euc d => ρ (x - a) - ρ x) x‖ := by
            apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
            exact mul_le_mul_of_nonneg_left h1 hn1
        _ ≤ _ := by
            apply mul_le_mul_of_nonneg_left h2'
            exact mul_nonneg hn1 (mul_nonneg hCw (by positivity))
    refine (Finset.sum_le_sum hterm).trans ?_
    have hsum : ∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ) * (Cw * (1 + ‖x‖) ^ Kw) *
        (‖a‖ * (B₁ * Real.exp (-(c / 2) * ‖x‖ ^ 2))) =
        2 ^ i * (Cw * ‖a‖ * B₁) * ((1 + ‖x‖) ^ Kw * Real.exp (-(c / 2) * ‖x‖ ^ 2)) := by
      have : ∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ) = 2 ^ i := by
        exact_mod_cast Nat.sum_range_choose i
      calc ∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ) * (Cw * (1 + ‖x‖) ^ Kw) *
            (‖a‖ * (B₁ * Real.exp (-(c / 2) * ‖x‖ ^ 2)))
          = (∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ)) *
            ((Cw * (1 + ‖x‖) ^ Kw) * (‖a‖ * (B₁ * Real.exp (-(c / 2) * ‖x‖ ^ 2)))) := by
            rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun j _ => by ring
        _ = _ := by rw [this]; ring
    rw [hsum]
    have hpg := movtr_poly_gauss_le hc Kw ‖x‖ (norm_nonneg x)
    have h2i : (2 : ℝ) ^ i ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) hi
    have hB1nn : 0 ≤ B₁ := by rw [hB₁]; positivity
    calc 2 ^ i * (Cw * ‖a‖ * B₁) * ((1 + ‖x‖) ^ Kw * Real.exp (-(c / 2) * ‖x‖ ^ 2))
        ≤ 2 ^ k * (Cw * ‖a‖ * B₁) * (Real.exp ((Kw : ℝ) ^ 2 / c) * Real.exp (-(c / 4) * ‖x‖ ^ 2)) := by
          apply mul_le_mul _ hpg (by positivity) (by positivity)
          exact mul_le_mul_of_nonneg_right h2i (by positivity)
      _ = ‖a‖ * M * Real.exp (-(c / 4) * ‖x‖ ^ 2) := by rw [hM]; ring
  -- L^p estimate
  have hbound : ∀ i ≤ k, eLpNorm
      (fun x => ‖iteratedFDeriv ℝ i (fun x => movBracket x ^ ℓ * (ρ (x - a) - ρ x)) x‖) p volume ≤
      ENNReal.ofReal (‖a‖ * M) * G := by
    intro i hi
    have hmeas : AEStronglyMeasurable
        (fun x => ‖iteratedFDeriv ℝ i (fun x => movBracket x ^ ℓ * (ρ (x - a) - ρ x)) x‖) volume :=
      ((hcdf.continuous_iteratedFDeriv (m := i) (by exact_mod_cast le_top)).norm).aestronglyMeasurable
    calc _ ≤ eLpNorm ((‖a‖ * M) • fun x : Euc d => Real.exp (-(c / 4) * ‖x‖ ^ 2)) p volume := by
          apply eLpNorm_mono hmeas
          intro x
          rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), Pi.smul_apply, smul_eq_mul,
            Real.norm_eq_abs, abs_of_nonneg (by positivity)]
          have := hpt i hi x
          calc _ ≤ _ := this
            _ = _ := by ring
      _ = ENNReal.ofReal (‖a‖ * M) * G := by
          rw [eLpNorm_const_smul, Real.enorm_eq_ofReal (by positivity)]
  calc _ ≤ ∑ i ∈ Finset.range (k + 1), ENNReal.ofReal (‖a‖ * M) * G :=
        Finset.sum_le_sum fun i hi => hbound i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))
    _ = ENNReal.ofReal ((k + 1 : ℝ) * M * G.toReal * ‖a‖) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        conv_lhs => rw [← ENNReal.ofReal_toReal hGfin]
        rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        push_cast
        ring


/-- A common Gaussian moment of the translates. -/
theorem movtr_gauss_moment (hd : 1 ≤ d) {ρ : Euc d → ℝ} {C₀ c₀ : ℝ} (hc₀ : 0 < c₀)
    (hρc : Continuous ρ) (h0 : ∀ y, |ρ y| ≤ C₀ * Real.exp (-c₀ * ‖y‖ ^ 2)) (A : ℝ) :
    ∃ b : ℝ, 0 < b ∧ ∃ C : ℝ, ∀ a : Euc d, ‖a‖ ≤ A →
      ∫⁻ x, ENNReal.ofReal (Real.exp (b * ‖x‖ ^ 2) * ρ (x - a)) ≤ ENNReal.ofReal C := by
  have hC₀ : 0 ≤ C₀ := by
    have := h0 0
    simp at this
    exact le_trans (abs_nonneg _) this
  set G : ℝ := ∫ y : Euc d, Real.exp (-(c₀ / 2) * ‖y‖ ^ 2) with hG
  have hGint : Integrable (fun y : Euc d => Real.exp (-(c₀ / 2) * ‖y‖ ^ 2)) := by
    have := movtr_integrable_rpow_gauss (d := d) hd (α := 0) (c := c₀ / 2) (by
      have : (1:ℝ) ≤ d := by exact_mod_cast hd
      linarith) (by positivity)
    refine this.congr (Filter.Eventually.of_forall fun y => ?_)
    simp
  refine ⟨c₀ / 4, by positivity, C₀ * Real.exp (c₀ / 2 * A ^ 2) * G, fun a ha => ?_⟩
  set K : ℝ := C₀ * Real.exp (c₀ / 2 * A ^ 2) with hK
  have hpt : ∀ x : Euc d, Real.exp (c₀ / 4 * ‖x‖ ^ 2) * ρ (x - a) ≤
      K * Real.exp (-(c₀ / 2) * ‖x - a‖ ^ 2) := by
    intro x
    have h1 := h0 (x - a)
    have h2 : ‖x‖ ^ 2 ≤ 2 * ‖x - a‖ ^ 2 + 2 * ‖a‖ ^ 2 := by
      have : ‖x‖ ≤ ‖x - a‖ + ‖a‖ := by
        calc ‖x‖ = ‖(x - a) + a‖ := by simp
          _ ≤ _ := norm_add_le _ _
      nlinarith [norm_nonneg x, norm_nonneg (x - a), norm_nonneg a, sq_nonneg (‖x - a‖ - ‖a‖)]
    have h3 : ‖a‖ ^ 2 ≤ A ^ 2 := by
      have := norm_nonneg a
      nlinarith
    calc Real.exp (c₀ / 4 * ‖x‖ ^ 2) * ρ (x - a)
        ≤ Real.exp (c₀ / 4 * ‖x‖ ^ 2) * (C₀ * Real.exp (-c₀ * ‖x - a‖ ^ 2)) :=
          mul_le_mul_of_nonneg_left ((le_abs_self _).trans h1) (Real.exp_pos _).le
      _ = C₀ * Real.exp (c₀ / 4 * ‖x‖ ^ 2 + -c₀ * ‖x - a‖ ^ 2) := by
          rw [Real.exp_add]; ring
      _ ≤ C₀ * Real.exp (c₀ / 2 * A ^ 2 + -(c₀ / 2) * ‖x - a‖ ^ 2) := by
          apply mul_le_mul_of_nonneg_left _ hC₀
          apply Real.exp_le_exp.mpr
          nlinarith
      _ = _ := by rw [Real.exp_add, hK]; ring
  have hint : Integrable (fun x : Euc d => K * Real.exp (-(c₀ / 2) * ‖x - a‖ ^ 2)) :=
    (hGint.comp_sub_right a).const_mul K
  calc ∫⁻ x, ENNReal.ofReal (Real.exp (c₀ / 4 * ‖x‖ ^ 2) * ρ (x - a))
      ≤ ∫⁻ x, ENNReal.ofReal (K * Real.exp (-(c₀ / 2) * ‖x - a‖ ^ 2)) :=
        lintegral_mono fun x => ENNReal.ofReal_le_ofReal (hpt x)
    _ = ENNReal.ofReal (∫ x, K * Real.exp (-(c₀ / 2) * ‖x - a‖ ^ 2)) := by
        rw [ofReal_integral_eq_lintegral_ofReal hint
          (Filter.Eventually.of_forall fun x => by positivity)]
    _ = ENNReal.ofReal (K * G) := by
        rw [integral_const_mul, hG,
          integral_sub_right_eq_self (fun y : Euc d => Real.exp (-(c₀ / 2) * ‖y‖ ^ 2)) a]

end HRS.Whole
