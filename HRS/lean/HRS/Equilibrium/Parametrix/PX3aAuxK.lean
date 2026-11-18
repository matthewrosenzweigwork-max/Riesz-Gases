import HRS.Equilibrium.Parametrix.PX3aAuxJ

/-!
# Packet PX3a auxiliaries K: bounds on the far kernel
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.Parx

variable {d : ℕ}

lemma Ekap_hyp (hd : 2 ≤ d) : ∃ B : ℝ, 0 ≤ B ∧ ∀ r : ℝ, 0 < r → ∀ y : Euc d, r / 16 ≤ ‖y‖ → ‖y‖ ≤ r / 8 →
    |Efund d y - Ekap d r| ≤ B * (r / 8) ^ ((2 : ℝ) - d) := by
  by_cases h2 : d = 2
  · subst h2
    refine ⟨1, zero_le_one, fun r hr y hy1 hy2 => ?_⟩
    have hn : 0 < ‖y‖ := lt_of_lt_of_le (by positivity) hy1
    have hy0 : y ≠ 0 := norm_pos_iff.mp hn
    have e1 : Efund 2 y - Ekap 2 r = (1 / (2 * Real.pi)) * Real.log (r / ‖y‖) := by
      simp only [Efund, e0, Ekap, if_true]
      rw [Real.log_pow, Real.log_pow, Real.log_div hr.ne' hn.ne']
      push_cast
      field_simp
      ring
    have hp : 0 < Real.pi := Real.pi_pos
    have hlog0 : 0 ≤ Real.log (r / ‖y‖) := Real.log_nonneg (by rw [le_div_iff₀ hn]; linarith)
    have hlog1 : Real.log (r / ‖y‖) ≤ Real.log 16 := by
      refine Real.log_le_log (by positivity) ?_
      rw [div_le_iff₀ hn]; linarith
    have h16 : Real.log 16 ≤ 3 := by
      have : Real.log 16 = 4 * Real.log 2 := by
        rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]; norm_num
      have := Real.log_two_lt_d9
      linarith
    rw [e1, abs_of_nonneg (by positivity)]
    simp only [Nat.cast_ofNat, sub_self, Real.rpow_zero, mul_one]
    have : 1 / (2 * Real.pi) ≤ 1 / 6 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      have := Real.pi_gt_three
      linarith
    calc 1 / (2 * Real.pi) * Real.log (r / ‖y‖) ≤ 1 / 6 * 3 := by
          apply mul_le_mul this (hlog1.trans h16) hlog0 (by norm_num)
      _ ≤ 1 := by norm_num
  · obtain ⟨c, hc0, hc⟩ := Efund_abs_le hd
    refine ⟨c * 2 ^ ((d : ℝ) - 2), by positivity, fun r hr y hy1 hy2 => ?_⟩
    have hn : 0 < ‖y‖ := lt_of_lt_of_le (by positivity) hy1
    have hy0 : y ≠ 0 := norm_pos_iff.mp hn
    simp only [Ekap, h2, if_false, sub_zero]
    refine (hc y hy0).trans ?_
    simp only [h2, if_false, pow_zero, mul_one]
    have h3 : ‖y‖ ^ (-((d : ℝ) - 2)) ≤ (r / 16) ^ (-((d : ℝ) - 2)) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hy1 (by
        have : (2 : ℝ) ≤ d := by exact_mod_cast hd
        linarith)
    have h4 : (r / 16) ^ (-((d : ℝ) - 2)) = 2 ^ ((d : ℝ) - 2) * (r / 8) ^ ((2 : ℝ) - d) := by
      have e : r / 16 = (1 / 2) * (r / 8) := by ring
      have e2 : (1 / 2 : ℝ) ^ (-((d : ℝ) - 2)) = 2 ^ ((d : ℝ) - 2) := by
        rw [one_div, Real.inv_rpow (by norm_num), Real.rpow_neg (by norm_num), inv_inv]
      rw [e, Real.mul_rpow (by norm_num) (by positivity), e2,
        show (-((d : ℝ) - 2)) = (2 : ℝ) - d by ring]
    rw [mul_assoc]
    calc c * (‖y‖ ^ (-((d : ℝ) - 2))) ≤ c * (2 ^ ((d : ℝ) - 2) * (r / 8) ^ ((2 : ℝ) - d)) := by
          rw [← h4]; exact mul_le_mul_of_nonneg_left h3 hc0
      _ = _ := by ring

lemma iteratedFDeriv_Lf_eq_zero {ρ : ℝ} (hρ : 0 < ρ) (κ : ℝ) {j : ℕ} {y : Euc d} (hy : ‖y‖ < ρ / 2) :
    iteratedFDeriv ℝ j (Lf d κ ρ) y = 0 := by
  have : Lf d κ ρ =ᶠ[𝓝 y] fun _ => (0 : ℝ) := by
    filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds hy] with u hu
    have hu' : ‖u‖ < ρ / 2 := hu
    simp [Lf, px3a_zeta_eq_one hρ hu'.le]
  rw [(this.iteratedFDeriv ℝ j).eq_of_nhds]
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · ext v; simp [iteratedFDeriv_zero_eq_comp]
  · have := iteratedFDeriv_const_of_ne (𝕜 := ℝ) (E := Euc d) (by omega : j ≠ 0) (0 : ℝ)
    exact congrFun this y

lemma far_kernel_bound (hd : 2 ≤ d) {c : ℕ} (hc : 1 ≤ c) :
    ∃ Ck : ℝ, 0 ≤ Ck ∧ ∀ r : ℝ, 0 < r → ∀ y : Euc d, ‖y‖ < 1 / 2 →
      ‖iteratedFDeriv ℝ c (Lf d (Ekap d r) (r / 8)) y‖ ≤
        Ck * (if r / 16 ≤ ‖y‖ then ‖y‖ ^ ((2 : ℝ) - d - c) else 0) := by
  obtain ⟨C, hC0, hC⟩ := norm_iteratedFDeriv_Lf_le hd c hc
  obtain ⟨B, hB0, hB⟩ := Ekap_hyp hd
  refine ⟨C * (1 + B), by positivity, fun r hr y hy => ?_⟩
  have hρ : 0 < r / 8 := by positivity
  by_cases h : r / 16 ≤ ‖y‖
  · rw [if_pos h]
    exact hC (Ekap d r) (r / 8) B hρ hB0 (fun y' h1 h2 => hB r hr y' (by linarith) h2) y (by linarith) hy
  · rw [if_neg h, mul_zero]
    rw [iteratedFDeriv_Lf_eq_zero hρ _ (by linarith [not_le.mp h])]
    simp

/-- The evaluated far integrand. -/
def farPsi (d : ℕ) (g : Euc d × Euc d → ℝ) (κ ρ : ℝ) (X0 z0 : Euc d) {a c : ℕ}
    (u : Fin a → Euc d) (v : Fin c → Euc d) (w : Euc d) : ℝ :=
  (iteratedFDeriv ℝ (a + c) (fun q : Euc d × Euc d => Lf d κ ρ (q.2 - w) * g (q.1, w)) (X0, z0)) (pat u v)

lemma farPsi_eq {σ : ℝ} {b m : ℕ} {A : ℝ} {g : Euc d × Euc d → ℝ} (h : SrcCls d σ b m A g)
    {ρ : ℝ} (hρ : 0 < ρ) (κ : ℝ) {a c : ℕ} (hac : a + c ≤ m) (X0 z0 : Euc d)
    (u : Fin a → Euc d) (v : Fin c → Euc d) {w : Euc d} (hw : w ≠ 0) :
    farPsi d g κ ρ X0 z0 u v w =
      (iteratedFDeriv ℝ c (Lf d κ ρ) (z0 - w)) v * (iteratedFDeriv ℝ a (fun X' => g (X', w)) X0) u := by
  have h1 : ContDiff ℝ ((a + c : ℕ) : WithTop ℕ∞) (fun y : Euc d => Lf d κ ρ (y - w)) := by
    have : ContDiff ℝ ((a + c : ℕ) : WithTop ℕ∞) (Lf d κ ρ) := by
      exact_mod_cast Lf_contDiff hρ κ ((a + c : ℕ) : ℕ∞)
    exact this.comp (contDiff_id.sub contDiff_const)
  have h2 : ContDiff ℝ ((a + c : ℕ) : WithTop ℕ∞) (fun X' : Euc d => g (X', w)) := by
    have := h.smooth.of_le (by exact_mod_cast hac : ((a + c : ℕ) : WithTop ℕ∞) ≤ m) |>.comp
      (by fun_prop : ContDiff ℝ ((a + c : ℕ) : WithTop ℕ∞) (fun X' : Euc d => ((X', w) : Euc d × Euc d))).contDiffOn
      (s := Set.univ) (fun X' _ => hw)
    exact contDiffOn_univ.mp this
  unfold farPsi
  have := iteratedFDeriv_prodpat (a + c) a c rfl _ _ h1 h2 (X0, z0) u v
  rw [this]
  have e : iteratedFDeriv ℝ c (fun y : Euc d => Lf d κ ρ (y - w)) z0 = iteratedFDeriv ℝ c (Lf d κ ρ) (z0 - w) :=
    iteratedFDeriv_comp_sub c w z0
  simp only [e]

lemma ae_norm_ne_sixteenth (hd : 1 ≤ d) : ∀ᵐ w : Euc d ∂(volume : Measure (Euc d)), ‖w‖ ≠ 1 / 16 := by
  have h0 : (volume : Measure (Euc d)) (Metric.sphere (0 : Euc d) (1 / 16)) = 0 :=
    Measure.addHaar_sphere_of_ne_zero volume (0 : Euc d) (r := 1 / 16) (by norm_num)
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp h0] with w hw
  simpa using hw

lemma farPsi_zero_of_gt {σ : ℝ} {b m : ℕ} {A : ℝ} {g : Euc d × Euc d → ℝ} (h : SrcCls d σ b m A g)
    {ρ : ℝ} (hρ : 0 < ρ) (κ : ℝ) {a c : ℕ} (hac : a + c ≤ m) (X0 z0 : Euc d)
    (u : Fin a → Euc d) (v : Fin c → Euc d) {w : Euc d} (hw : 1 / 16 < ‖w‖) :
    farPsi d g κ ρ X0 z0 u v w = 0 := by
  have hw0 : w ≠ 0 := norm_pos_iff.mp (lt_trans (by norm_num) hw)
  rw [farPsi_eq h hρ κ hac X0 z0 u v hw0, h.slice_zero a hw X0]
  simp

lemma farPsi_bound {σ : ℝ} {b m : ℕ} {A : ℝ} {g : Euc d × Euc d → ℝ} (h : SrcCls d σ b m A g)
    (hσ0 : 0 ≤ σ) {ρ : ℝ} (hρ : 0 < ρ) (κ : ℝ) {a c : ℕ} (hac : a + c ≤ m) (X0 z0 : Euc d)
    (u : Fin a → Euc d) (v : Fin c → Euc d) {w : Euc d} (hw : w ≠ 0) (hw1 : ‖w‖ ≤ 1 / 16) :
    |farPsi d g κ ρ X0 z0 u v w| ≤
      ‖iteratedFDeriv ℝ c (Lf d κ ρ) (z0 - w)‖ * (∏ j, ‖v j‖) *
        ((A * (1 + ‖w‖ ^ (-σ) * lw ‖w‖ ^ b)) * ∏ i, ‖u i‖) := by
  rw [farPsi_eq h hρ κ hac X0 z0 u v hw, abs_mul]
  have h1 : |(iteratedFDeriv ℝ c (Lf d κ ρ) (z0 - w)) v| ≤
      ‖iteratedFDeriv ℝ c (Lf d κ ρ) (z0 - w)‖ * ∏ j, ‖v j‖ := by
    rw [← Real.norm_eq_abs]; exact ContinuousMultilinearMap.le_opNorm _ _
  have h2 : |(iteratedFDeriv ℝ a (fun X' => g (X', w)) X0) u| ≤
      (A * (1 + ‖w‖ ^ (-σ) * lw ‖w‖ ^ b)) * ∏ i, ‖u i‖ := by
    rw [← Real.norm_eq_abs]
    refine (ContinuousMultilinearMap.le_opNorm _ _).trans ?_
    exact mul_le_mul_of_nonneg_right (h.slice_bound (by omega) X0 w hw) (Finset.prod_nonneg fun i _ => norm_nonneg _)
  exact mul_le_mul h1 h2 (abs_nonneg _) (mul_nonneg (norm_nonneg _) (Finset.prod_nonneg fun i _ => norm_nonneg _))

set_option maxHeartbeats 1600000 in
/-- Pointwise majorants of the far integrand (`c ≥ 1`). -/
lemma far_pointwise (hd : 2 ≤ d) {σ : ℝ} (hσ0 : 0 ≤ σ) {b m : ℕ} {A : ℝ} {g : Euc d × Euc d → ℝ}
    (h : SrcCls d σ b m A g) (hA : 0 ≤ A) {a c : ℕ} (hac : a + c ≤ m) {r : ℝ} (hr : 0 < r)
    (hr1 : r < 1 / 8) (X0 z0 : Euc d) (hz0 : ‖z0‖ = r) (u : Fin a → Euc d) (v : Fin c → Euc d)
    {Ck : ℝ} (hCk0 : 0 ≤ Ck)
    (hK : ∀ y : Euc d, ‖y‖ < 1 / 2 → ‖iteratedFDeriv ℝ c (Lf d (Ekap d r) (r / 8)) y‖ ≤
      Ck * (if r / 16 ≤ ‖y‖ then ‖y‖ ^ ((2 : ℝ) - d - c) else 0))
    (he0n : (2 : ℝ) - d - c < 0) :
    (∀ᵐ w : Euc d ∂volume, ‖w‖ < 2 * r → ‖farPsi d g (Ekap d r) (r / 8) X0 z0 u v w‖ ≤
      (Ck * (r / 16) ^ ((2 : ℝ) - d - c) * (2 * A * ((∏ i, ‖u i‖) * ∏ j, ‖v j‖))) *
        (‖w‖ ^ (-σ) * lw ‖w‖ ^ b)) ∧
    (∀ᵐ w : Euc d ∂volume, 2 * r ≤ ‖w‖ → ‖w‖ < 1 / 16 → ‖farPsi d g (Ekap d r) (r / 8) X0 z0 u v w‖ ≤
      (Ck * 2 ^ (-((2 : ℝ) - d - c)) * (2 * A * ((∏ i, ‖u i‖) * ∏ j, ‖v j‖))) *
        (‖w‖ ^ (-(σ + c + ((d : ℝ) - 2))) * lw ‖w‖ ^ b)) ∧
    (∀ᵐ w : Euc d ∂volume, 1 / 16 ≤ ‖w‖ → farPsi d g (Ekap d r) (r / 8) X0 z0 u v w = 0) := by
  have hρ : 0 < r / 8 := by positivity
  have hae0 := ae_ne_zero_euc (d := d) (by omega)
  have hae16 := ae_norm_ne_sixteenth (d := d) (by omega)
  set e0 : ℝ := (2 : ℝ) - d - c with he0
  have hP0 : 0 ≤ (∏ i, ‖u i‖) * ∏ j, ‖v j‖ :=
    mul_nonneg (Finset.prod_nonneg fun i _ => norm_nonneg _) (Finset.prod_nonneg fun i _ => norm_nonneg _)
  refine ⟨?_, ?_, ?_⟩
  · filter_upwards [hae0] with w hw0 hw2
    rw [Real.norm_eq_abs]
    have hnn : 0 ≤ (Ck * (r / 16) ^ e0 * (2 * A * ((∏ i, ‖u i‖) * ∏ j, ‖v j‖))) *
        (‖w‖ ^ (-σ) * lw ‖w‖ ^ b) := by
      have h1 : 0 ≤ (r / 16) ^ e0 := Real.rpow_nonneg (by positivity) _
      have h2 : 0 ≤ ‖w‖ ^ (-σ) := Real.rpow_nonneg (norm_nonneg _) _
      have h3 : 0 ≤ lw ‖w‖ ^ b := pow_nonneg (lw_pos _).le b
      exact mul_nonneg (mul_nonneg (mul_nonneg hCk0 h1) (mul_nonneg (mul_nonneg (by norm_num) hA) hP0))
        (mul_nonneg h2 h3)
    by_cases hw1 : ‖w‖ ≤ 1 / 16
    · refine (farPsi_bound h hσ0 hρ (Ekap d r) hac X0 z0 u v hw0 hw1).trans ?_
      have hy : ‖z0 - w‖ < 1 / 2 := by
        have := norm_sub_le z0 w; linarith
      have hk := hK (z0 - w) hy
      have hk2 : ‖iteratedFDeriv ℝ c (Lf d (Ekap d r) (r / 8)) (z0 - w)‖ ≤ Ck * (r / 16) ^ e0 := by
        refine hk.trans ?_
        by_cases hc : r / 16 ≤ ‖z0 - w‖
        · rw [if_pos hc]
          exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos (by positivity) hc he0n.le) hCk0
        · rw [if_neg hc, mul_zero]
          exact mul_nonneg hCk0 (Real.rpow_nonneg (by positivity) _)
      have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hw0
      have hs := SrcCls.weight_pure hσ0 b hwpos (by linarith)
      have hs' : A * (1 + ‖w‖ ^ (-σ) * lw ‖w‖ ^ b) ≤ 2 * A * (‖w‖ ^ (-σ) * lw ‖w‖ ^ b) := by nlinarith
      have hwl : 0 ≤ ‖w‖ ^ (-σ) * lw ‖w‖ ^ b :=
        mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (pow_nonneg (lw_pos _).le b)
      have hPu : 0 ≤ ∏ i, ‖u i‖ := Finset.prod_nonneg fun i _ => norm_nonneg _
      have hPv : 0 ≤ ∏ j, ‖v j‖ := Finset.prod_nonneg fun i _ => norm_nonneg _
      calc ‖iteratedFDeriv ℝ c (Lf d (Ekap d r) (r / 8)) (z0 - w)‖ * (∏ j, ‖v j‖) *
            ((A * (1 + ‖w‖ ^ (-σ) * lw ‖w‖ ^ b)) * ∏ i, ‖u i‖)
          ≤ (Ck * (r / 16) ^ e0) * (∏ j, ‖v j‖) * ((2 * A * (‖w‖ ^ (-σ) * lw ‖w‖ ^ b)) * ∏ i, ‖u i‖) :=
            mul_le_mul (mul_le_mul_of_nonneg_right hk2 hPv)
              (mul_le_mul_of_nonneg_right hs' hPu) (mul_nonneg (mul_nonneg hA (by linarith [hwl])) hPu)
              (mul_nonneg (mul_nonneg hCk0 (Real.rpow_nonneg (by positivity) _)) hPv)
        _ = _ := by ring
    · rw [farPsi_zero_of_gt h hρ (Ekap d r) hac X0 z0 u v (not_le.mp hw1), abs_zero]
      exact hnn
  · filter_upwards [hae0] with w hw0 hw2 hw3
    rw [Real.norm_eq_abs]
    have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hw0
    have hw1 : ‖w‖ ≤ 1 / 16 := hw3.le
    refine (farPsi_bound h hσ0 hρ (Ekap d r) hac X0 z0 u v hw0 hw1).trans ?_
    have hy : ‖z0 - w‖ < 1 / 2 := by
      have := norm_sub_le z0 w; linarith
    have hyl : ‖w‖ / 2 ≤ ‖z0 - w‖ := by
      have := norm_sub_norm_le w z0
      rw [norm_sub_rev] at this
      linarith
    have hk := hK (z0 - w) hy
    have hc : r / 16 ≤ ‖z0 - w‖ := by linarith
    have hk2 : ‖iteratedFDeriv ℝ c (Lf d (Ekap d r) (r / 8)) (z0 - w)‖ ≤
        Ck * (2:ℝ) ^ (-e0) * ‖w‖ ^ e0 := by
      refine hk.trans ?_
      rw [if_pos hc]
      have h1 : ‖z0 - w‖ ^ e0 ≤ (‖w‖ / 2) ^ e0 :=
        Real.rpow_le_rpow_of_nonpos (by positivity) hyl he0n.le
      have h2 : (‖w‖ / 2) ^ e0 = (2:ℝ) ^ (-e0) * ‖w‖ ^ e0 := by
        rw [Real.div_rpow hwpos.le (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
        ring
      calc Ck * ‖z0 - w‖ ^ e0 ≤ Ck * ((2:ℝ) ^ (-e0) * ‖w‖ ^ e0) :=
            mul_le_mul_of_nonneg_left (h1.trans h2.le) hCk0
        _ = _ := by ring
    have hs := SrcCls.weight_pure hσ0 b hwpos (by linarith)
    have hs' : A * (1 + ‖w‖ ^ (-σ) * lw ‖w‖ ^ b) ≤ 2 * A * (‖w‖ ^ (-σ) * lw ‖w‖ ^ b) := by nlinarith
    have hwl : 0 ≤ ‖w‖ ^ (-σ) * lw ‖w‖ ^ b :=
      mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (pow_nonneg (lw_pos _).le b)
    have hPu : 0 ≤ ∏ i, ‖u i‖ := Finset.prod_nonneg fun i _ => norm_nonneg _
    have hPv : 0 ≤ ∏ j, ‖v j‖ := Finset.prod_nonneg fun i _ => norm_nonneg _
    have hexp : ‖w‖ ^ e0 * ‖w‖ ^ (-σ) = ‖w‖ ^ (-(σ + c + ((d : ℝ) - 2))) := by
      rw [← Real.rpow_add hwpos]; congr 1; rw [he0]; ring
    have h2c : 0 ≤ (2:ℝ) ^ (-e0) := Real.rpow_nonneg (by norm_num) _
    calc ‖iteratedFDeriv ℝ c (Lf d (Ekap d r) (r / 8)) (z0 - w)‖ * (∏ j, ‖v j‖) *
          ((A * (1 + ‖w‖ ^ (-σ) * lw ‖w‖ ^ b)) * ∏ i, ‖u i‖)
        ≤ (Ck * (2:ℝ) ^ (-e0) * ‖w‖ ^ e0) * (∏ j, ‖v j‖) *
            ((2 * A * (‖w‖ ^ (-σ) * lw ‖w‖ ^ b)) * ∏ i, ‖u i‖) :=
          mul_le_mul (mul_le_mul_of_nonneg_right hk2 hPv)
            (mul_le_mul_of_nonneg_right hs' hPu) (mul_nonneg (mul_nonneg hA (by linarith [hwl])) hPu)
            (mul_nonneg (mul_nonneg (mul_nonneg hCk0 h2c) (Real.rpow_nonneg (norm_nonneg _) _)) hPv)
      _ = (Ck * (2:ℝ) ^ (-e0) * (2 * A * ((∏ i, ‖u i‖) * ∏ j, ‖v j‖))) *
          ((‖w‖ ^ e0 * ‖w‖ ^ (-σ)) * lw ‖w‖ ^ b) := by ring
      _ = _ := by rw [hexp]
  · filter_upwards [hae16] with w hw hw1
    exact farPsi_zero_of_gt h hρ (Ekap d r) hac X0 z0 u v (lt_of_le_of_ne hw1 (Ne.symm hw))

end HRS.Parx
