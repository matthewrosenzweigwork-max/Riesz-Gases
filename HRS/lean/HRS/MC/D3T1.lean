import HRS.MC.D3T1Aux3

/-!
# Packet D3T1: Lemma D.3 on `𝕋^d`, items (i) and (iv).

Spec: `HRS/Appendix/FDL.lean`, `HRS.fdl_kernel_torus`.  Two standalone theorems whose conclusions
are the corresponding conjuncts of `fdl_kernel_torus`.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace HRS.MC.D3T1

open HRS HRS.MC.FDLE HRS.MC.Per

variable {d : ℕ}

/-- `w_λ = 0` and `g_λ = g` for `λ ≤ |x|`. -/
lemma d3t_trunc_eq {ψ : Euc d → ℝ} (hψ : IsFDLProfile ψ) {s b lam : ℝ} (hlam : 0 < lam)
    {x : Torus d} (hx : lam ≤ KernelGrad.tdist x 0) :
    fdlWT ψ s b lam x = 0 ∧ fdlTruncT ψ s b lam x = periodicRiesz d s x := by
  have hW : fdlWT ψ s b lam x = 0 := by
    unfold fdlWT
    have h0 : ∫ t in Ioc 0 lam, t ^ ((d : ℝ) - s) * fdlPer (fdlPhiScale ψ t) x / t
        = ∫ _ in Ioc 0 lam, (0 : ℝ) :=
      setIntegral_congr_fun measurableSet_Ioc (fun t ht => by
        show t ^ ((d : ℝ) - s) * fdlPer (fdlPhiScale ψ t) x / t = 0
        rw [d3t_per_zero hψ ht.1 (ht.2.trans hx), mul_zero, zero_div])
    rw [h0, integral_zero, mul_zero]
  refine ⟨hW, ?_⟩
  unfold fdlTruncT
  rw [if_neg (d3t_ne_zero_of_le hlam hx), hW, sub_zero]

lemma d3t_F_nonneg {ψ : Euc d → ℝ} (hψ : IsFDLProfile ψ) (s : ℝ) {t : ℝ} (ht : 0 < t)
    (x : Torus d) : 0 ≤ t ^ ((d : ℝ) - s) * fdlPer (fdlPhiScale ψ t) x / t :=
  div_nonneg (mul_nonneg (Real.rpow_nonneg ht.le _) (d3t_per_nonneg hψ ht x)) ht.le

/-- Lemma D.3(i) on the torus. -/
theorem d3t_part_i (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {ψ : Euc d → ℝ}
    (hψ : IsFDLProfile ψ) {b : ℝ} (hb : IsFDLConst ψ s b) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ lam : ℝ, 0 < lam → lam < 1 →
      (∀ x : Torus d, x ≠ 0 → 0 ≤ fdlWT ψ s b lam x) ∧
      (∀ x : Torus d, lam ≤ KernelGrad.tdist x 0 →
        fdlWT ψ s b lam x = 0 ∧ fdlTruncT ψ s b lam x = periodicRiesz d s x) ∧
      (∀ x : Torus d, x ≠ 0 → fdlWT ψ s b lam x ≤ periodicRiesz d s x + C) ∧
      ∫⁻ x : Torus d, ENNReal.ofReal (fdlWT ψ s b lam x) ≤
        ENNReal.ofReal (C * lam ^ ((d : ℝ) - s)) := by
  have hb0 : 0 < b := hb.1
  have hds : 0 < (d : ℝ) - s := by linarith
  have hI0 : 0 ≤ ∫ x, fdlPhi ψ x := integral_nonneg (fdle_phi_nonneg hψ)
  obtain ⟨B, hB0, hB⟩ := d3t_g_lower hd hs0 hsd hψ hb
  have hE0 : 0 ≤ b * (∫ x, fdlPhi ψ x) / ((d : ℝ) - s) :=
    div_nonneg (mul_nonneg hb0.le hI0) hds.le
  refine ⟨B + b * (∫ x, fdlPhi ψ x) / ((d : ℝ) - s), add_nonneg hB0 hE0,
    fun lam hlam0 hlam1 => ?_⟩
  refine ⟨fun x _ => ?_, fun x hx => d3t_trunc_eq hψ hlam0 hx, fun x hx => ?_, ?_⟩
  · unfold fdlWT
    exact mul_nonneg hb0.le
      (setIntegral_nonneg measurableSet_Ioc (fun t ht => d3t_F_nonneg hψ s ht.1 x))
  · have hmono : ∫ t in Ioc (0 : ℝ) lam, t ^ ((d : ℝ) - s) * fdlPer (fdlPhiScale ψ t) x / t
        ≤ ∫ t in Ioc (0 : ℝ) 1, t ^ ((d : ℝ) - s) * fdlPer (fdlPhiScale ψ t) x / t :=
      setIntegral_mono_set (d3t_F_integrable hsd hb hx one_pos)
        ((ae_restrict_iff' measurableSet_Ioc).mpr
          (Eventually.of_forall fun t ht => d3t_F_nonneg hψ s ht.1 x))
        (Eventually.of_forall fun t ht => Ioc_subset_Ioc_right hlam1.le ht)
    have h1 := hB x hx
    have h2 := mul_le_mul_of_nonneg_left hmono hb0.le
    unfold fdlWT
    linarith [hE0]
  · refine (d3t_lintegral_W hd hs0 hsd hψ hb hlam0).trans ?_
    apply ENNReal.ofReal_le_ofReal
    have hlp : 0 ≤ lam ^ ((d : ℝ) - s) := Real.rpow_nonneg hlam0.le _
    have : b * (∫ x, fdlPhi ψ x) * (lam ^ ((d : ℝ) - s) / ((d : ℝ) - s))
        = (b * (∫ x, fdlPhi ψ x) / ((d : ℝ) - s)) * lam ^ ((d : ℝ) - s) := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_right (by linarith) hlp

/-- `∫_a^e t^{-s}/t = (a^{-s} - e^{-s})/s` for `s > 0`. -/
lemma d3t_int_rpow {s : ℝ} (hs : 0 < s) {a e : ℝ} (ha : 0 < a) (hae : a ≤ e) :
    ∫ t in Ioc a e, t ^ (-s) / t = (a ^ (-s) - e ^ (-s)) / s := by
  have hcongr : ∫ t in Ioc a e, t ^ (-s) / t = ∫ t in Ioc a e, t ^ (-s - 1) :=
    setIntegral_congr_fun measurableSet_Ioc (fun t ht =>
      (Real.rpow_sub_one (ne_of_gt (lt_trans ha ht.1)) (-s)).symm)
  rw [hcongr, ← intervalIntegral.integral_of_le hae,
    integral_rpow (Or.inr ⟨fun h' => by linarith, ?_⟩)]
  · have hr1 : -s - 1 + 1 = -s := by ring
    rw [hr1, div_neg]
    ring
  · rw [uIcc_of_le hae]
    intro h'
    linarith [h'.1]

/-- `∫_a^e t^{-0}/t = log (e/a)`. -/
lemma d3t_int_log {a e : ℝ} (ha : 0 < a) (hae : a ≤ e) :
    ∫ t in Ioc a e, t ^ (-(0 : ℝ)) / t = Real.log (e / a) := by
  have hsimp : ∀ t : ℝ, t ^ (-(0 : ℝ)) / t = t⁻¹ := by
    intro t; simp
  simp_rw [hsimp]
  rw [← intervalIntegral.integral_of_le hae, integral_inv_of_pos ha (lt_of_lt_of_le ha hae)]

/-- Lower bound of the integral of `F_x` by the nearest-term estimate. -/
lemma d3t_int_lower {ψ : Euc d → ℝ} (hψ : IsFDLProfile ψ) {s : ℝ} (hsd : s < d) {b : ℝ}
    (hb : IsFDLConst ψ s b) {c0 : ℝ}
    (hc0 : ∀ y : Euc d, ‖y‖ ≤ 1 / 4 → c0 ≤ fdlPhi ψ y) {x : Torus d} (hx : x ≠ 0)
    {a e R : ℝ} (ha : 0 < a) (hae : a ≤ e) (heR : e ≤ R)
    (hnear : ∀ t : ℝ, a < t → KernelGrad.tdist x 0 ≤ t / 4) :
    c0 * ∫ t in Ioc a e, t ^ (-s) / t
      ≤ ∫ t in Ioc (0 : ℝ) R, t ^ ((d : ℝ) - s) * fdlPer (fdlPhiScale ψ t) x / t := by
  have hF : IntegrableOn (fun t : ℝ => t ^ ((d : ℝ) - s) * fdlPer (fdlPhiScale ψ t) x / t)
      (Ioc 0 R) := d3t_F_integrable hsd hb hx (lt_of_lt_of_le ha (hae.trans heR))
  have h1 : ∫ t in Ioc a e, t ^ ((d : ℝ) - s) * fdlPer (fdlPhiScale ψ t) x / t
      ≤ ∫ t in Ioc (0 : ℝ) R, t ^ ((d : ℝ) - s) * fdlPer (fdlPhiScale ψ t) x / t :=
    setIntegral_mono_set hF
      ((ae_restrict_iff' measurableSet_Ioc).mpr
        (Eventually.of_forall fun t ht => d3t_F_nonneg hψ s ht.1 x))
      (Eventually.of_forall fun t ht => ⟨lt_trans ha ht.1, ht.2.trans heR⟩)
  have hsub : Ioc a e ⊆ Ioc 0 R := fun t ht => ⟨lt_trans ha ht.1, ht.2.trans heR⟩
  have h2 : ∫ t in Ioc a e, c0 * (t ^ (-s) / t)
      ≤ ∫ t in Ioc a e, t ^ ((d : ℝ) - s) * fdlPer (fdlPhiScale ψ t) x / t := by
    refine setIntegral_mono_on ((fdle_lower_integrable s ha).const_mul c0)
      (hF.mono_set hsub) measurableSet_Ioc (fun t ht => ?_)
    have ht0 : 0 < t := lt_trans ha ht.1
    obtain ⟨z, hz, hzn⟩ := d3t_exists_rep x
    refine d3t_per_lower hψ s hc0 ht0 hz ?_
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 ht0.le), ← div_eq_inv_mul, hzn,
      div_le_iff₀ ht0]
    linarith [hnear t ht.1]
  rw [integral_const_mul] at h2
  exact h2.trans h1

/-- Lemma D.3(iv) on the torus. -/
theorem d3t_part_iv (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {ψ : Euc d → ℝ}
    (hψ : IsFDLProfile ψ) {b : ℝ} (hb : IsFDLConst ψ s b) :
    (0 < s → ∃ c C : ℝ, 0 < c ∧ 0 ≤ C ∧ ∀ lam : ℝ, 0 < lam → lam < 1 → ∀ x : Torus d,
      lam ≤ KernelGrad.tdist x 0 →
      c * KernelGrad.tdist x 0 ^ (-s) - C ≤ fdlTruncT ψ s b lam x) ∧
    (s = 0 → ∃ c C : ℝ, 0 < c ∧ 0 ≤ C ∧ ∀ lam : ℝ, 0 < lam → lam < 1 → ∀ x : Torus d,
      lam ≤ KernelGrad.tdist x 0 → KernelGrad.tdist x 0 ≤ 1 / 2 →
      c * Real.log (1 / KernelGrad.tdist x 0) - C ≤ fdlTruncT ψ s b lam x) ∧
    (∀ K : ℝ, fdlK ≤ K → ∃ c : ℝ, 0 < c ∧ ∀ lam : ℝ, 0 < lam → lam < 1 → ∀ x : Torus d, x ≠ 0 →
      KernelGrad.tdist x 0 ≤ 2 * lam →
      c * (if s = 0 then 1 else lam ^ (-s)) ≤ fdlWT ψ s b (K * lam) x) := by
  have hb0 : 0 < b := hb.1
  obtain ⟨B, hB0, hB⟩ := d3t_g_lower hd hs0 hsd hψ hb
  obtain ⟨c0, hc0pos, hc0⟩ := fdle_phi_min hψ
  -- `∫_0^1 F ≥ 0`
  have hFnn : ∀ x : Torus d, 0 ≤ ∫ t in Ioc (0 : ℝ) 1,
      t ^ ((d : ℝ) - s) * fdlPer (fdlPhiScale ψ t) x / t := fun x =>
    setIntegral_nonneg measurableSet_Ioc (fun t ht => d3t_F_nonneg hψ s ht.1 x)
  refine ⟨fun h => ?_, fun h0 => ?_, fun K hK => ?_⟩
  · -- first item, `s > 0`
    refine ⟨b * c0 * (4 : ℝ) ^ (-s) / s, B + b * c0 / s, div_pos (mul_pos (mul_pos hb0 hc0pos)
      (Real.rpow_pos_of_pos (by norm_num) _)) h, add_nonneg hB0 (div_nonneg
      (mul_nonneg hb0.le hc0pos.le) h.le), fun lam hlam0 hlam1 x hx => ?_⟩
    have hx0 : x ≠ 0 := d3t_ne_zero_of_le hlam0 hx
    rw [(d3t_trunc_eq hψ hlam0 hx).2]
    have htd : 0 < KernelGrad.tdist x 0 := KernelGrad.tdist_pos hx0
    set td := KernelGrad.tdist x 0 with htddef
    have hg := hB x hx0
    by_cases h4 : 4 * td ≤ 1
    · have hlow := d3t_int_lower hψ hsd hb hc0 hx0 (a := 4 * td) (e := 1) (R := 1)
        (by linarith) h4 le_rfl (fun t ht => by linarith)
      rw [d3t_int_rpow h (by linarith) h4, Real.one_rpow,
        Real.mul_rpow (by norm_num) htd.le] at hlow
      have h5 := mul_le_mul_of_nonneg_left hlow hb0.le
      have e1 : b * (c0 * (((4 : ℝ) ^ (-s) * td ^ (-s) - 1) / s))
          = b * c0 * (4 : ℝ) ^ (-s) / s * td ^ (-s) - b * c0 / s := by
        field_simp
      linarith
    · push Not at h4
      have hle : td ^ (-s) ≤ (4 : ℝ) ^ s := by
        have h14 : (1 / 4 : ℝ) < td := by linarith
        have := Real.rpow_le_rpow_of_nonpos (by norm_num : (0 : ℝ) < 1 / 4) h14.le
          (by linarith : -s ≤ 0)
        calc td ^ (-s) ≤ (1 / 4 : ℝ) ^ (-s) := this
          _ = (4 : ℝ) ^ s := by
            rw [one_div, Real.inv_rpow (by norm_num), Real.rpow_neg (by norm_num), inv_inv]
      have h6 : b * c0 * (4 : ℝ) ^ (-s) / s * td ^ (-s) ≤ b * c0 / s := by
        calc b * c0 * (4 : ℝ) ^ (-s) / s * td ^ (-s)
            ≤ b * c0 * (4 : ℝ) ^ (-s) / s * (4 : ℝ) ^ s :=
              mul_le_mul_of_nonneg_left hle (div_nonneg (mul_nonneg (mul_nonneg hb0.le hc0pos.le)
                (Real.rpow_nonneg (by norm_num) _)) h.le)
          _ = b * c0 / s := by
              have : (4 : ℝ) ^ (-s) * (4 : ℝ) ^ s = 1 := by
                rw [← Real.rpow_add (by norm_num)]; simp
              calc b * c0 * (4 : ℝ) ^ (-s) / s * (4 : ℝ) ^ s
                  = b * c0 / s * ((4 : ℝ) ^ (-s) * (4 : ℝ) ^ s) := by ring
                _ = b * c0 / s := by rw [this, mul_one]
      have h7 := mul_nonneg hb0.le (hFnn x)
      linarith
  · -- second item, `s = 0`
    subst h0
    refine ⟨b * c0, B + b * c0 * Real.log 4, mul_pos hb0 hc0pos, add_nonneg hB0
      (mul_nonneg (mul_nonneg hb0.le hc0pos.le) (Real.log_nonneg (by norm_num))),
      fun lam hlam0 hlam1 x hx hx2 => ?_⟩
    have hx0 : x ≠ 0 := d3t_ne_zero_of_le hlam0 hx
    rw [(d3t_trunc_eq hψ hlam0 hx).2]
    have htd : 0 < KernelGrad.tdist x 0 := KernelGrad.tdist_pos hx0
    set td := KernelGrad.tdist x 0 with htddef
    have hg := hB x hx0
    by_cases h4 : 4 * td ≤ 1
    · have hlow := d3t_int_lower hψ hsd hb hc0 hx0 (a := 4 * td) (e := 1) (R := 1)
        (by linarith) h4 le_rfl (fun t ht => by linarith)
      rw [d3t_int_log (by linarith) h4] at hlow
      have hl : Real.log (1 / (4 * td)) = Real.log (1 / td) - Real.log 4 := by
        rw [show 1 / (4 * td) = (1 / td) / 4 by field_simp,
          Real.log_div (by positivity) (by norm_num)]
      rw [hl] at hlow
      have h5 := mul_le_mul_of_nonneg_left hlow hb0.le
      nlinarith [h5, hg]
    · push Not at h4
      have hl : Real.log (1 / td) ≤ Real.log 4 := by
        apply Real.log_le_log (by positivity)
        rw [div_le_iff₀ htd]; linarith
      have h7 := mul_nonneg hb0.le (hFnn x)
      have h8 : b * c0 * Real.log (1 / td) ≤ b * c0 * Real.log 4 :=
        mul_le_mul_of_nonneg_left hl (mul_nonneg hb0.le hc0pos.le)
      linarith
  · -- third item
    have hK16 : (16 : ℝ) ≤ K := hK
    rcases hs0.eq_or_lt with h | h
    · subst h
      refine ⟨b * c0 * Real.log (K / 8), mul_pos (mul_pos hb0 hc0pos)
        (Real.log_pos ((one_lt_div (by norm_num)).mpr (by linarith))),
        fun lam hlam0 hlam1 x hx0 hxl => ?_⟩
      rw [if_pos rfl, mul_one]
      have hKl : 0 < K * lam := mul_pos (by linarith) hlam0
      have h8 : 0 < 8 * lam := by linarith
      have hle8 : 8 * lam ≤ K * lam := mul_le_mul_of_nonneg_right (by linarith) hlam0.le
      have hlow := d3t_int_lower hψ hsd hb hc0 hx0 (a := 8 * lam) (e := K * lam) (R := K * lam)
        h8 hle8 le_rfl (fun t ht => by linarith)
      rw [d3t_int_log h8 hle8, mul_div_mul_right _ _ hlam0.ne'] at hlow
      unfold fdlWT
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left hlow hb0.le
    · have hs' : s ≠ 0 := ne_of_gt h
      have hK8 : (8 : ℝ) < K := by linarith
      have hpow : K ^ (-s) < (8 : ℝ) ^ (-s) :=
        Real.rpow_lt_rpow_of_neg (by norm_num) hK8 (by linarith)
      refine ⟨b * c0 * ((8 : ℝ) ^ (-s) - K ^ (-s)) / s,
        div_pos (mul_pos (mul_pos hb0 hc0pos) (by linarith)) h,
        fun lam hlam0 hlam1 x hx0 hxl => ?_⟩
      rw [if_neg hs']
      have hKl : 0 < K * lam := mul_pos (by linarith) hlam0
      have h8 : 0 < 8 * lam := by linarith
      have hle8 : 8 * lam ≤ K * lam := mul_le_mul_of_nonneg_right (by linarith) hlam0.le
      have hlow := d3t_int_lower hψ hsd hb hc0 hx0 (a := 8 * lam) (e := K * lam) (R := K * lam)
        h8 hle8 le_rfl (fun t ht => by linarith)
      rw [d3t_int_rpow h h8 hle8, Real.mul_rpow (by norm_num) hlam0.le,
        Real.mul_rpow (by linarith) hlam0.le] at hlow
      have := mul_le_mul_of_nonneg_left hlow hb0.le
      unfold fdlWT
      calc b * c0 * ((8 : ℝ) ^ (-s) - K ^ (-s)) / s * lam ^ (-s)
          = b * (c0 * (((8 : ℝ) ^ (-s) * lam ^ (-s) - K ^ (-s) * lam ^ (-s)) / s)) := by ring
        _ ≤ b * ∫ t in Ioc 0 (K * lam), t ^ ((d : ℝ) - s) * fdlPer (fdlPhiScale ψ t) x / t := this

end HRS.MC.D3T1
