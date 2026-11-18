import HRS.MC.FDLEAux3

/-!
# Packet FDLE: Lemma D.3 on `ℝ^d`, items (i) (with the repair at `s = 0`) and (iv).

Spec: `HRS/Appendix/FDL.lean`, `HRS.fdl_kernel_euclid`.  Helpers live in `HRS/MC/FDLEAux*.lean`.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace HRS.MC.FDLE

open HRS

variable {d : ℕ}

/-- `w_λ = 0` on `‖z‖ ≥ λ`. -/
lemma fdle_W_vanish {ψ : Euc d → ℝ} (hψ : IsFDLProfile ψ) {s b lam : ℝ} {z : Euc d}
    (hz : lam ≤ ‖z‖) (hlam : 0 < lam) : fdlWE ψ s b lam z = 0 := by
  unfold fdlWE
  have h0 : ∫ t in Ioc 0 lam, t ^ ((d : ℝ) - s) * fdlPhiScale ψ t z / t
      = ∫ _ in Ioc 0 lam, (0 : ℝ) :=
    setIntegral_congr_fun measurableSet_Ioc (fun t ht => by
      show t ^ ((d : ℝ) - s) * fdlPhiScale ψ t z / t = 0
      rw [fdle_phiScale_eq_zero hψ ht.1 (le_trans ht.2 hz), mul_zero, zero_div])
  rw [h0, integral_zero, mul_zero]

/-- Lower-bound integrability of `t ↦ t^{-s}/t` on `(a, b]`, `a > 0`. -/
lemma fdle_lower_integrable (s : ℝ) {a b : ℝ} (ha : 0 < a) :
    IntegrableOn (fun t : ℝ => t ^ (-s) / t) (Ioc a b) := by
  have hc : ContinuousOn (fun t : ℝ => t ^ (-s) / t) (Icc a b) :=
    ContinuousOn.div
      (continuousOn_id.rpow_const (fun t ht => Or.inl (ne_of_gt (lt_of_lt_of_le ha ht.1))))
      continuousOn_id (fun t ht => ne_of_gt (lt_of_lt_of_le ha ht.1))
  exact hc.integrableOn_Icc.mono_set Ioc_subset_Icc_self

/-- Lemma D.3(i) with the repair at `s = 0` (premise `‖z‖ ≤ 1` in the third bullet). -/
theorem fdle_part_i (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {ψ : Euc d → ℝ}
    (hψ : IsFDLProfile ψ) {b : ℝ} (hb : IsFDLConst ψ s b) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ lam : ℝ, 0 < lam → lam < 1 →
      (∀ z : Euc d, z ≠ 0 → 0 ≤ fdlWE ψ s b lam z) ∧
      (∀ z : Euc d, lam ≤ ‖z‖ →
        fdlWE ψ s b lam z = 0 ∧ fdlTruncE ψ s b lam z = Whole.rieszKernel d s z) ∧
      (∀ z : Euc d, z ≠ 0 → (s = 0 → ‖z‖ ≤ 1) →
        fdlWE ψ s b lam z ≤ Whole.rieszKernel d s z + C * (if s = 0 then 1 else 0)) ∧
      ∫⁻ z : Euc d, ENNReal.ofReal (fdlWE ψ s b lam z) ≤
        ENNReal.ofReal (C * lam ^ ((d : ℝ) - s)) := by
  have hb0 : 0 < b := hb.1
  have hds : 0 < (d : ℝ) - s := by linarith
  have hI0 : 0 ≤ ∫ x, fdlPhi ψ x := integral_nonneg (fdle_phi_nonneg hψ)
  refine ⟨b * (∫ x, fdlPhi ψ x) / ((d : ℝ) - s),
    div_nonneg (mul_nonneg hb0.le hI0) hds.le, fun lam hlam0 hlam1 => ?_⟩
  have hC0 : 0 ≤ b * (∫ x, fdlPhi ψ x) / ((d : ℝ) - s) :=
    div_nonneg (mul_nonneg hb0.le hI0) hds.le
  refine ⟨fun z hz => ?_, fun z hz => ?_, fun z hz hs1 => ?_, ?_⟩
  · -- nonnegativity
    unfold fdlWE
    exact mul_nonneg hb0.le
      (setIntegral_nonneg measurableSet_Ioc (fun t ht => fdle_F_nonneg hψ s ht.1 z))
  · -- vanishing beyond `λ` and the truncated kernel
    have hz0 : z ≠ 0 := fun h => by rw [h, norm_zero] at hz; linarith
    have hW := fdle_W_vanish (s := s) (b := b) hψ hz hlam0
    refine ⟨hW, ?_⟩
    unfold fdlTruncE
    rw [if_neg hz0, hW, sub_zero]
  · -- the repaired third bullet
    have hz0 : z ≠ 0 := hz
    rcases hs0.eq_or_lt with h | h
    · subst h
      have hr1 : ‖z‖ ≤ 1 := hs1 rfl
      rw [if_pos rfl, mul_one, fdle_rk0]
      by_cases hr : lam ≤ ‖z‖
      · rw [fdle_W_vanish (s := 0) (b := b) hψ hr hlam0]
        have := Real.log_nonpos (norm_nonneg z) hr1
        linarith
      · push_neg at hr
        have hr0 : 0 < ‖z‖ := norm_pos_iff.mpr hz0
        have hφ0 := fdle_b_phi0 hd hb
        unfold fdlWE
        have hsplit : ∫ t in Ioc 0 lam, t ^ ((d : ℝ) - 0) * fdlPhiScale ψ t z / t
            = ∫ t in Ioc ‖z‖ lam, t ^ ((d : ℝ) - 0) * fdlPhiScale ψ t z / t := by
          refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioc
            (Ioc_subset_Ioc_left hr0.le) (fun t ht => ?_)
          have htz : t ≤ ‖z‖ := by
            by_contra h'
            exact ht.2 ⟨not_le.mp h', ht.1.2⟩
          show t ^ ((d : ℝ) - 0) * fdlPhiScale ψ t z / t = 0
          rw [fdle_phiScale_eq_zero hψ ht.1.1 htz, mul_zero, zero_div]
        have hFint : IntegrableOn (fun t : ℝ => t ^ ((d : ℝ) - 0) * fdlPhiScale ψ t z / t)
            (Ioc ‖z‖ lam) :=
          (fdle_F_integrable hs0 hb hz0 hlam0).mono_set (Ioc_subset_Ioc_left hr0.le)
        have hGint : IntegrableOn (fun t : ℝ => fdlPhi ψ 0 * t⁻¹) (Ioc ‖z‖ lam) := by
          have hc : ContinuousOn (fun t : ℝ => fdlPhi ψ 0 * t⁻¹) (Icc ‖z‖ lam) :=
            continuousOn_const.mul (continuousOn_inv₀.mono (fun t ht => by
              exact ne_of_gt (lt_of_lt_of_le hr0 ht.1)))
          exact hc.integrableOn_Icc.mono_set Ioc_subset_Icc_self
        have hmono : ∫ t in Ioc ‖z‖ lam, t ^ ((d : ℝ) - 0) * fdlPhiScale ψ t z / t
            ≤ ∫ t in Ioc ‖z‖ lam, fdlPhi ψ 0 * t⁻¹ := by
          refine setIntegral_mono_on hFint hGint measurableSet_Ioc (fun t ht => ?_)
          have ht0 : 0 < t := lt_of_le_of_lt hr0.le ht.1
          rw [fdle_F0_eq ht0 z, ← div_eq_mul_inv]
          exact div_le_div_of_nonneg_right (fdle_phi_le_phi0 hψ _) ht0.le
        have hval : ∫ t in Ioc ‖z‖ lam, fdlPhi ψ 0 * t⁻¹ = fdlPhi ψ 0 * Real.log (lam / ‖z‖) := by
          rw [integral_const_mul, ← intervalIntegral.integral_of_le hr.le,
            integral_inv_of_pos hr0 hlam0]
        have hbound : b * ∫ t in Ioc 0 lam, t ^ ((d : ℝ) - 0) * fdlPhiScale ψ t z / t
            ≤ Real.log (lam / ‖z‖) := by
          rw [hsplit]
          have := mul_le_mul_of_nonneg_left (hmono.trans hval.le) hb0.le
          calc b * ∫ t in Ioc ‖z‖ lam, t ^ ((d : ℝ) - 0) * fdlPhiScale ψ t z / t
              ≤ b * (fdlPhi ψ 0 * Real.log (lam / ‖z‖)) := by
                exact mul_le_mul_of_nonneg_left (hmono.trans hval.le) hb0.le
            _ = (b * fdlPhi ψ 0) * Real.log (lam / ‖z‖) := by ring
            _ = Real.log (lam / ‖z‖) := by rw [hφ0, one_mul]
        have hlog : Real.log (lam / ‖z‖) = Real.log lam - Real.log ‖z‖ :=
          Real.log_div hlam0.ne' hr0.ne'
        have hlam_log := Real.log_nonpos hlam0.le hlam1.le
        linarith
    · have hs' : s ≠ 0 := ne_of_gt h
      rw [if_neg hs', mul_zero, add_zero]
      have hrk := (hb.2.1 h z hz0).2
      rw [hrk]
      refine mul_le_mul_of_nonneg_left ?_ hb0.le
      refine setIntegral_mono_set (hb.2.1 h z hz0).1 ?_ ?_
      · exact (ae_restrict_iff' measurableSet_Ioi).mpr
          (Eventually.of_forall fun t ht => fdle_F_nonneg hψ s (show (0:ℝ) < t from ht) z)
      · exact Eventually.of_forall fun t ht => Ioc_subset_Ioi_self ht
  · -- the `L¹` bound
    rw [fdle_lintegral_W hd hs0 hsd hψ hb hlam0]
    apply le_of_eq
    congr 1
    ring

/-- Lemma D.3(iv), the three items of `fdl_kernel_euclid` verbatim. -/
theorem fdle_part_iv (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {ψ : Euc d → ℝ}
    (hψ : IsFDLProfile ψ) {b : ℝ} (hb : IsFDLConst ψ s b) :
    (0 < s → ∃ c : ℝ, 0 < c ∧ ∀ lam : ℝ, 0 < lam → lam < 1 → ∀ z : Euc d, lam ≤ ‖z‖ →
      c * ‖z‖ ^ (-s) ≤ fdlTruncE ψ s b lam z) ∧
    (s = 0 → ∃ c C : ℝ, 0 < c ∧ ∀ lam : ℝ, 0 < lam → lam < 1 → ∀ z : Euc d, lam ≤ ‖z‖ →
      ‖z‖ ≤ 1 / 2 → c * Real.log (1 / ‖z‖) - C ≤ fdlTruncE ψ s b lam z) ∧
    (∀ K : ℝ, fdlK ≤ K → ∃ c : ℝ, 0 < c ∧ ∀ lam : ℝ, 0 < lam → lam < 1 → ∀ z : Euc d, z ≠ 0 →
      ‖z‖ ≤ 2 * lam → c * (if s = 0 then 1 else lam ^ (-s)) ≤ fdlWE ψ s b (K * lam) z) := by
  have hb0 : 0 < b := hb.1
  refine ⟨fun h => ?_, fun h0 => ?_, fun K hK => ?_⟩
  · -- (iv), first item, `s > 0`
    refine ⟨1, one_pos, fun lam hlam0 hlam1 z hz => ?_⟩
    have hz0 : z ≠ 0 := fun h' => by rw [h', norm_zero] at hz; linarith
    have hT : fdlTruncE ψ s b lam z = Whole.rieszKernel d s z := by
      unfold fdlTruncE
      rw [if_neg hz0, fdle_W_vanish hψ hz hlam0, sub_zero]
    rw [hT, fdle_rk_pos s h.ne' z, one_mul]
  · -- (iv), second item, `s = 0`
    subst h0
    refine ⟨1, 0, one_pos, fun lam hlam0 hlam1 z hz hz2 => ?_⟩
    have hz0 : z ≠ 0 := fun h' => by rw [h', norm_zero] at hz; linarith
    have hT : fdlTruncE ψ 0 b lam z = Whole.rieszKernel d 0 z := by
      unfold fdlTruncE
      rw [if_neg hz0, fdle_W_vanish hψ hz hlam0, sub_zero]
    rw [hT, fdle_rk0, one_mul, sub_zero, one_div, Real.log_inv]
  · -- (iv), third item
    have hK16 : (16 : ℝ) ≤ K := hK
    obtain ⟨c0, hc0pos, hc0⟩ := fdle_phi_min hψ
    rcases hs0.eq_or_lt with h | h
    · subst h
      refine ⟨b * c0 * Real.log (K / 8), mul_pos (mul_pos hb0 hc0pos)
        (Real.log_pos ((one_lt_div (by norm_num)).mpr (by linarith))),
        fun lam hlam0 hlam1 z hz0 hzl => ?_⟩
      rw [if_pos rfl, mul_one]
      have hKl : 0 < K * lam := mul_pos (by linarith) hlam0
      have h8 : 0 < 8 * lam := by linarith
      have hpos8 : (0 : ℝ) ≤ 8 * lam := h8.le
      have hle8 : 8 * lam ≤ K * lam := mul_le_mul_of_nonneg_right (by linarith) hlam0.le
      have hr0 : 0 < ‖z‖ := norm_pos_iff.mpr hz0
      have hFint : IntegrableOn (fun t : ℝ => t ^ ((d : ℝ) - 0) * fdlPhiScale ψ t z / t)
          (Ioc 0 (K * lam)) := fdle_F_integrable hs0 hb hz0 hKl
      have h1 : ∫ t in Ioc (8 * lam) (K * lam), t ^ ((d : ℝ) - 0) * fdlPhiScale ψ t z / t
          ≤ ∫ t in Ioc 0 (K * lam), t ^ ((d : ℝ) - 0) * fdlPhiScale ψ t z / t :=
        setIntegral_mono_set hFint
          ((ae_restrict_iff' measurableSet_Ioc).mpr
            (Eventually.of_forall fun t ht => fdle_F_nonneg hψ 0 ht.1 z))
          (Eventually.of_forall fun t ht => Ioc_subset_Ioc_left hpos8 ht)
      have h2 : ∫ t in Ioc (8 * lam) (K * lam), c0 * (t ^ (-(0 : ℝ)) / t)
          ≤ ∫ t in Ioc (8 * lam) (K * lam), t ^ ((d : ℝ) - 0) * fdlPhiScale ψ t z / t := by
        refine setIntegral_mono_on ((fdle_lower_integrable 0 h8).const_mul c0)
          (hFint.mono_set (Ioc_subset_Ioc_left hpos8)) measurableSet_Ioc (fun t ht => ?_)
        have ht0 : 0 < t := lt_trans h8 ht.1
        have hzt : ‖t⁻¹ • z‖ ≤ 1 / 4 := by
          rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 ht0.le), ← div_eq_inv_mul,
            div_le_iff₀ ht0]
          linarith [ht.1]
        exact fdle_F_lower 0 hc0 ht0 hzt
      have h3 : ∫ t in Ioc (8 * lam) (K * lam), c0 * (t ^ (-(0 : ℝ)) / t)
          = c0 * Real.log (K / 8) := by
        have hsimp : ∀ t : ℝ, c0 * (t ^ (-(0 : ℝ)) / t) = c0 * t⁻¹ := by
          intro t
          simp
        simp_rw [hsimp]
        rw [integral_const_mul, ← intervalIntegral.integral_of_le (by linarith : 8 * lam ≤ K * lam),
          integral_inv_of_pos h8 hKl, mul_div_mul_right _ _ hlam0.ne']
      have hfin : c0 * Real.log (K / 8) ≤
          ∫ t in Ioc 0 (K * lam), t ^ ((d : ℝ) - 0) * fdlPhiScale ψ t z / t := by
        rw [← h3]
        exact h2.trans h1
      unfold fdlWE
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left hfin hb0.le
    · -- `s > 0`
      have hs' : s ≠ 0 := ne_of_gt h
      have hK8 : (8 : ℝ) < K := by linarith
      have hpow : K ^ (-s) < (8 : ℝ) ^ (-s) :=
        Real.rpow_lt_rpow_of_neg (by norm_num) hK8 (by linarith)
      refine ⟨b * c0 * ((8 : ℝ) ^ (-s) - K ^ (-s)) / s,
        div_pos (mul_pos (mul_pos hb0 hc0pos) (by linarith)) h,
        fun lam hlam0 hlam1 z hz0 hzl => ?_⟩
      rw [if_neg hs']
      have hKl : 0 < K * lam := mul_pos (by linarith) hlam0
      have h8 : 0 < 8 * lam := by linarith
      have hpos8 : (0 : ℝ) ≤ 8 * lam := h8.le
      have hle8 : 8 * lam ≤ K * lam := mul_le_mul_of_nonneg_right (by linarith) hlam0.le
      have hr0 : 0 < ‖z‖ := norm_pos_iff.mpr hz0
      have hFint : IntegrableOn (fun t : ℝ => t ^ ((d : ℝ) - s) * fdlPhiScale ψ t z / t)
          (Ioc 0 (K * lam)) := fdle_F_integrable hs0 hb hz0 hKl
      have h1 : ∫ t in Ioc (8 * lam) (K * lam), t ^ ((d : ℝ) - s) * fdlPhiScale ψ t z / t
          ≤ ∫ t in Ioc 0 (K * lam), t ^ ((d : ℝ) - s) * fdlPhiScale ψ t z / t :=
        setIntegral_mono_set hFint
          ((ae_restrict_iff' measurableSet_Ioc).mpr
            (Eventually.of_forall fun t ht => fdle_F_nonneg hψ s ht.1 z))
          (Eventually.of_forall fun t ht => Ioc_subset_Ioc_left hpos8 ht)
      have h2 : ∫ t in Ioc (8 * lam) (K * lam), c0 * (t ^ (-s) / t)
          ≤ ∫ t in Ioc (8 * lam) (K * lam), t ^ ((d : ℝ) - s) * fdlPhiScale ψ t z / t := by
        refine setIntegral_mono_on ((fdle_lower_integrable s h8).const_mul c0)
          (hFint.mono_set (Ioc_subset_Ioc_left hpos8)) measurableSet_Ioc (fun t ht => ?_)
        have ht0 : 0 < t := lt_trans h8 ht.1
        have hzt : ‖t⁻¹ • z‖ ≤ 1 / 4 := by
          rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 ht0.le), ← div_eq_inv_mul,
            div_le_iff₀ ht0]
          linarith [ht.1]
        exact fdle_F_lower s hc0 ht0 hzt
      have h3 : ∫ t in Ioc (8 * lam) (K * lam), c0 * (t ^ (-s) / t)
          = c0 * (((8 * lam) ^ (-s) - (K * lam) ^ (-s)) / s) := by
        have hcongr : ∫ t in Ioc (8 * lam) (K * lam), t ^ (-s) / t
            = ∫ t in Ioc (8 * lam) (K * lam), t ^ (-s - 1) :=
          setIntegral_congr_fun measurableSet_Ioc (fun t ht => by
            exact (Real.rpow_sub_one (ne_of_gt (lt_trans h8 ht.1)) (-s)).symm)
        rw [integral_const_mul, hcongr, ← intervalIntegral.integral_of_le (by linarith : 8 * lam ≤ K * lam),
          integral_rpow (Or.inr ⟨fun h' => by linarith, ?_⟩)]
        · have hr1 : -s - 1 + 1 = -s := by ring
          rw [hr1, div_neg]
          ring
        · rw [uIcc_of_le (by linarith : 8 * lam ≤ K * lam)]
          intro h'
          linarith [h'.1]
      have key : c0 * (((8 * lam) ^ (-s) - (K * lam) ^ (-s)) / s)
          ≤ ∫ t in Ioc 0 (K * lam), t ^ ((d : ℝ) - s) * fdlPhiScale ψ t z / t := by
        rw [← h3]
        exact h2.trans h1
      rw [Real.mul_rpow (by norm_num) hlam0.le, Real.mul_rpow (by linarith) hlam0.le] at key
      have := mul_le_mul_of_nonneg_left key hb0.le
      unfold fdlWE
      calc b * c0 * ((8 : ℝ) ^ (-s) - K ^ (-s)) / s * lam ^ (-s)
          = b * (c0 * (((8 : ℝ) ^ (-s) * lam ^ (-s) - K ^ (-s) * lam ^ (-s)) / s)) := by ring
        _ ≤ b * ∫ t in Ioc 0 (K * lam), t ^ ((d : ℝ) - s) * fdlPhiScale ψ t z / t := this

end HRS.MC.FDLE
