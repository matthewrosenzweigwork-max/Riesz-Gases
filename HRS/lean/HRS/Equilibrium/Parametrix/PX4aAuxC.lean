import HRS.Equilibrium.Parametrix.PX4aAuxB

/-!
# Packet PX4a auxiliaries C: the base estimate for the potential `kPot` (`0 ≤ σ < d`)

Near piece: all derivatives on the source (`g_pat_bound`), `∫ |kN| ≲ ρ^{d-s}`; far piece:
all derivatives on the far kernel, evaluated with `far_estimate`.  No resonance bookkeeping: the
logarithm power is `b + 1` throughout.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.Parx

variable {d : ℕ}

local notation "∞'" => ((⊤ : ℕ∞) : WithTop ℕ∞)

section Base

variable {s : ℝ} {k : Euc d → ℝ}

lemma near_integral_k (hd : 2 ≤ d) (hk : LocKer d s k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ρ Mt : ℝ), 0 < ρ → ρ ≤ 1 → 0 ≤ Mt → ∀ ψ : Euc d → ℝ,
      (∀ x, ‖ψ x‖ ≤ Mt * ‖kN k ρ x‖) →
      ‖∫ x, ψ x‖ ≤ C * Mt * ρ ^ ((d : ℝ) - s) := by
  obtain ⟨c, hc0, hc⟩ := hk.norm_kN_le
  obtain ⟨I, hI0, hI⟩ := norm_integral_ball_le (d := d) (by omega) (q := s) hk.s_lt 0
  refine ⟨cpol d * c * I, by have := cpol_nonneg d; positivity, fun ρ Mt hρ hρ1 hMt ψ hψ => ?_⟩
  have key := hI ρ (Mt * c) hρ hρ1 (by positivity) ψ ?_
  · refine key.trans (le_of_eq ?_)
    simp only [pow_zero, mul_one]
    ring
  · filter_upwards [ae_ne_zero_euc (by omega : 1 ≤ d)] with x hx
    refine (hψ x).trans ?_
    by_cases hxρ : ‖x‖ < ρ
    · simp only [if_pos hxρ, pow_zero, mul_one]
      calc Mt * ‖kN k ρ x‖ ≤ Mt * (c * ‖x‖ ^ (-s)) := by gcongr; exact hc ρ x hx
        _ = _ := by ring
    · simp only [if_neg hxρ, mul_zero]
      simp [LocKer.kN_eq_zero hρ (not_lt.mp hxρ)]

/-- The evaluated far integrand. -/
def farKPsi (d : ℕ) (g : Euc d × Euc d → ℝ) (k : Euc d → ℝ) (ρ : ℝ) (X0 z0 : Euc d) {a c : ℕ}
    (u : Fin a → Euc d) (v : Fin c → Euc d) (w : Euc d) : ℝ :=
  (iteratedFDeriv ℝ (a + c) (fun q : Euc d × Euc d => kF k ρ (q.2 - w) * g (q.1, w)) (X0, z0)) (pat u v)

lemma farKPsi_eq (hk : LocKer d s k) {σ : ℝ} {b m : ℕ} {A : ℝ} {g : Euc d × Euc d → ℝ}
    (h : SrcCls d σ b m A g) {ρ : ℝ} (hρ : 0 < ρ) {a c : ℕ} (hac : a + c ≤ m) (X0 z0 : Euc d)
    (u : Fin a → Euc d) (v : Fin c → Euc d) {w : Euc d} (hw : w ≠ 0) :
    farKPsi d g k ρ X0 z0 u v w =
      (iteratedFDeriv ℝ c (kF k ρ) (z0 - w)) v * (iteratedFDeriv ℝ a (fun X' => g (X', w)) X0) u := by
  have h1 : ContDiff ℝ ((a + c : ℕ) : WithTop ℕ∞) (fun y : Euc d => kF k ρ (y - w)) := by
    have : ContDiff ℝ ((a + c : ℕ) : WithTop ℕ∞) (kF k ρ) := by
      exact_mod_cast hk.kF_contDiff hρ ((a + c : ℕ) : ℕ∞)
    exact this.comp (contDiff_id.sub contDiff_const)
  have h2 : ContDiff ℝ ((a + c : ℕ) : WithTop ℕ∞) (fun X' : Euc d => g (X', w)) := by
    have := h.smooth.of_le (by exact_mod_cast hac : ((a + c : ℕ) : WithTop ℕ∞) ≤ m) |>.comp
      (by fun_prop : ContDiff ℝ ((a + c : ℕ) : WithTop ℕ∞) (fun X' : Euc d => ((X', w) : Euc d × Euc d))).contDiffOn
      (s := Set.univ) (fun X' _ => hw)
    exact contDiffOn_univ.mp this
  unfold farKPsi
  have := iteratedFDeriv_prodpat (a + c) a c rfl _ _ h1 h2 (X0, z0) u v
  rw [this]
  have e : iteratedFDeriv ℝ c (fun y : Euc d => kF k ρ (y - w)) z0 = iteratedFDeriv ℝ c (kF k ρ) (z0 - w) :=
    iteratedFDeriv_comp_sub c w z0
  simp only [e]

lemma farKPsi_zero_of_gt (hk : LocKer d s k) {σ : ℝ} {b m : ℕ} {A : ℝ} {g : Euc d × Euc d → ℝ}
    (h : SrcCls d σ b m A g) {ρ : ℝ} (hρ : 0 < ρ) {a c : ℕ} (hac : a + c ≤ m) (X0 z0 : Euc d)
    (u : Fin a → Euc d) (v : Fin c → Euc d) {w : Euc d} (hw : 1 / 16 < ‖w‖) :
    farKPsi d g k ρ X0 z0 u v w = 0 := by
  have hw0 : w ≠ 0 := norm_pos_iff.mp (lt_trans (by norm_num) hw)
  rw [farKPsi_eq hk h hρ hac X0 z0 u v hw0, h.slice_zero a hw X0]
  simp

lemma farKPsi_bound (hk : LocKer d s k) {σ : ℝ} {b m : ℕ} {A : ℝ} {g : Euc d × Euc d → ℝ}
    (h : SrcCls d σ b m A g) {ρ : ℝ} (hρ : 0 < ρ) {a c : ℕ} (hac : a + c ≤ m) (X0 z0 : Euc d)
    (u : Fin a → Euc d) (v : Fin c → Euc d) {w : Euc d} (hw : w ≠ 0) :
    |farKPsi d g k ρ X0 z0 u v w| ≤
      ‖iteratedFDeriv ℝ c (kF k ρ) (z0 - w)‖ * (∏ j, ‖v j‖) *
        ((A * (1 + ‖w‖ ^ (-σ) * lw ‖w‖ ^ b)) * ∏ i, ‖u i‖) := by
  rw [farKPsi_eq hk h hρ hac X0 z0 u v hw, abs_mul]
  have h1 : |(iteratedFDeriv ℝ c (kF k ρ) (z0 - w)) v| ≤
      ‖iteratedFDeriv ℝ c (kF k ρ) (z0 - w)‖ * ∏ j, ‖v j‖ := by
    rw [← Real.norm_eq_abs]; exact ContinuousMultilinearMap.le_opNorm _ _
  have h2 : |(iteratedFDeriv ℝ a (fun X' => g (X', w)) X0) u| ≤
      (A * (1 + ‖w‖ ^ (-σ) * lw ‖w‖ ^ b)) * ∏ i, ‖u i‖ := by
    rw [← Real.norm_eq_abs]
    refine (ContinuousMultilinearMap.le_opNorm _ _).trans ?_
    exact mul_le_mul_of_nonneg_right (h.slice_bound (by omega) X0 w hw) (Finset.prod_nonneg fun i _ => norm_nonneg _)
  exact mul_le_mul h1 h2 (abs_nonneg _) (mul_nonneg (norm_nonneg _) (Finset.prod_nonneg fun i _ => norm_nonneg _))

set_option maxHeartbeats 1600000 in
/-- Pointwise majorants of the far integrand. -/
lemma far_pointwise_k (hd : 2 ≤ d) (hk : LocKer d s k) {σ : ℝ} (hσ0 : 0 ≤ σ) {b m : ℕ} {A : ℝ}
    {g : Euc d × Euc d → ℝ} (h : SrcCls d σ b m A g) (hA : 0 ≤ A) {a c : ℕ} (hac : a + c ≤ m)
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1 / 8) (X0 z0 : Euc d) (u : Fin a → Euc d) (v : Fin c → Euc d)
    {Ck : ℝ} (hCk0 : 0 ≤ Ck)
    (hK : ∀ y : Euc d, ‖iteratedFDeriv ℝ c (kF k (r / 8)) y‖ ≤
      Ck * (if r / 16 ≤ ‖y‖ then ‖y‖ ^ (-(s + c)) else 0)) (hz0 : ‖z0‖ = r) :
    (∀ᵐ w : Euc d ∂volume, ‖w‖ < 2 * r → ‖farKPsi d g k (r / 8) X0 z0 u v w‖ ≤
      (Ck * (r / 16) ^ (-(s + c)) * (2 * A * ((∏ i, ‖u i‖) * ∏ j, ‖v j‖))) *
        (‖w‖ ^ (-σ) * lw ‖w‖ ^ b)) ∧
    (∀ᵐ w : Euc d ∂volume, 2 * r ≤ ‖w‖ → ‖w‖ < 1 / 16 → ‖farKPsi d g k (r / 8) X0 z0 u v w‖ ≤
      (Ck * 2 ^ (s + c) * (2 * A * ((∏ i, ‖u i‖) * ∏ j, ‖v j‖))) *
        (‖w‖ ^ (-(σ + (s + c))) * lw ‖w‖ ^ b)) ∧
    (∀ᵐ w : Euc d ∂volume, 1 / 16 ≤ ‖w‖ → farKPsi d g k (r / 8) X0 z0 u v w = 0) := by
  have hρ : 0 < r / 8 := by positivity
  have hae0 := ae_ne_zero_euc (d := d) (by omega)
  have hae16 := ae_norm_ne_sixteenth (d := d) (by omega)
  have hsc : 0 < s + (c : ℝ) := by have := hk.s_pos; have : (0 : ℝ) ≤ c := Nat.cast_nonneg c; linarith
  obtain ⟨e0, he0⟩ : ∃ e0 : ℝ, e0 = -(s + (c : ℝ)) := ⟨_, rfl⟩
  rw [← he0] at hK ⊢
  have he0n : e0 < 0 := by rw [he0]; linarith
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
    · refine (farKPsi_bound hk h hρ hac X0 z0 u v hw0).trans ?_
      have hk2 : ‖iteratedFDeriv ℝ c (kF k (r / 8)) (z0 - w)‖ ≤ Ck * (r / 16) ^ e0 := by
        refine (hK (z0 - w)).trans ?_
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
      calc ‖iteratedFDeriv ℝ c (kF k (r / 8)) (z0 - w)‖ * (∏ j, ‖v j‖) *
            ((A * (1 + ‖w‖ ^ (-σ) * lw ‖w‖ ^ b)) * ∏ i, ‖u i‖)
          ≤ (Ck * (r / 16) ^ e0) * (∏ j, ‖v j‖) * ((2 * A * (‖w‖ ^ (-σ) * lw ‖w‖ ^ b)) * ∏ i, ‖u i‖) :=
            mul_le_mul (mul_le_mul_of_nonneg_right hk2 hPv)
              (mul_le_mul_of_nonneg_right hs' hPu) (mul_nonneg (mul_nonneg hA (by linarith [hwl])) hPu)
              (mul_nonneg (mul_nonneg hCk0 (Real.rpow_nonneg (by positivity) _)) hPv)
        _ = _ := by ring
    · rw [farKPsi_zero_of_gt hk h hρ hac X0 z0 u v (not_le.mp hw1), abs_zero]
      exact hnn
  · filter_upwards [hae0] with w hw0 hw2 hw3
    rw [Real.norm_eq_abs]
    have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hw0
    have hw1 : ‖w‖ ≤ 1 / 16 := hw3.le
    refine (farKPsi_bound hk h hρ hac X0 z0 u v hw0).trans ?_
    have hyl : ‖w‖ / 2 ≤ ‖z0 - w‖ := by
      have := norm_sub_norm_le w z0
      rw [norm_sub_rev] at this
      linarith
    have hc : r / 16 ≤ ‖z0 - w‖ := by linarith
    have hk2 : ‖iteratedFDeriv ℝ c (kF k (r / 8)) (z0 - w)‖ ≤
        Ck * (2:ℝ) ^ (-e0) * ‖w‖ ^ e0 := by
      refine (hK (z0 - w)).trans ?_
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
    have hexp : ‖w‖ ^ e0 * ‖w‖ ^ (-σ) = ‖w‖ ^ (-(σ + (s + c))) := by
      rw [← Real.rpow_add hwpos]; congr 1; rw [he0]; ring
    have h2c : 0 ≤ (2:ℝ) ^ (-e0) := Real.rpow_nonneg (by norm_num) _
    have h2e : (2 : ℝ) ^ (-e0) = 2 ^ (s + c) := by rw [he0, neg_neg]
    rw [h2e] at hk2 h2c
    calc ‖iteratedFDeriv ℝ c (kF k (r / 8)) (z0 - w)‖ * (∏ j, ‖v j‖) *
          ((A * (1 + ‖w‖ ^ (-σ) * lw ‖w‖ ^ b)) * ∏ i, ‖u i‖)
        ≤ (Ck * (2:ℝ) ^ (s + c) * ‖w‖ ^ e0) * (∏ j, ‖v j‖) *
            ((2 * A * (‖w‖ ^ (-σ) * lw ‖w‖ ^ b)) * ∏ i, ‖u i‖) :=
          mul_le_mul (mul_le_mul_of_nonneg_right hk2 hPv)
            (mul_le_mul_of_nonneg_right hs' hPu) (mul_nonneg (mul_nonneg hA (by linarith [hwl])) hPu)
            (mul_nonneg (mul_nonneg (mul_nonneg hCk0 h2c) (Real.rpow_nonneg (norm_nonneg _) _)) hPv)
      _ = (Ck * (2:ℝ) ^ (s + c) * (2 * A * ((∏ i, ‖u i‖) * ∏ j, ‖v j‖))) *
          ((‖w‖ ^ e0 * ‖w‖ ^ (-σ)) * lw ‖w‖ ^ b) := by ring
      _ = _ := by rw [hexp]
  · filter_upwards [hae16] with w hw hw1
    exact farKPsi_zero_of_gt hk h hρ hac X0 z0 u v (lt_of_le_of_ne hw1 (Ne.symm hw))

lemma kpot_pat_eq (hd : 1 ≤ d) (hk : LocKer d s k) {σ : ℝ} (hσ : σ < d) {b m : ℕ} {A : ℝ}
    (hA : 0 ≤ A) {g : Euc d × Euc d → ℝ} (h : SrcCls d σ b m A g) {a c : ℕ} (hac : a + c ≤ m)
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1 / 8) (X0 z0 : Euc d) (hz0 : ‖z0‖ = r)
    (u : Fin a → Euc d) (v : Fin c → Euc d) :
    iteratedFDeriv ℝ (a + c) (kPot d k g) (X0, z0) (pat u v) =
      (∫ x, kN k (r / 8) x * iteratedFDeriv ℝ (a + c) g (X0, z0 - x) (pat u v)) +
        ∫ w, farKPsi d g k (r / 8) X0 z0 u v w := by
  obtain ⟨-, hform, hint⟩ := kPot_FL hd hk hσ hA h hr hr1 hz0
  have hp0 : ((X0, z0) : Euc d × Euc d) ∈ {p : Euc d × Euc d | ‖p.2 - z0‖ < r / 16} := by
    show ‖z0 - z0‖ < r / 16
    simp; positivity
  obtain ⟨hi1, hi2⟩ := hint (a + c) hac (X0, z0) hp0
  rw [hform (a + c) hac (X0, z0) hp0, ContinuousMultilinearMap.add_apply,
    eval_integral hi1, eval_integral hi2]
  rfl

set_option maxHeartbeats 1600000 in
/-- Base estimate (`0 ≤ σ < d`), logarithm power `b + 1`. -/
lemma kpot_base (hd : 2 ≤ d) (hk : LocKer d s k) {σ : ℝ} (hσ0 : 0 ≤ σ) (hσ : σ < d) (b m c : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {g : Euc d × Euc d → ℝ} {A : ℝ} (_h : SrcCls d σ b m A g), 0 ≤ A →
      ∀ {a : ℕ}, a + c ≤ m → ∀ {r : ℝ}, 0 < r → r < 1 / 8 → ∀ (X0 z0 : Euc d), ‖z0‖ = r →
      ∀ (u : Fin a → Euc d) (v : Fin c → Euc d),
      |iteratedFDeriv ℝ (a + c) (kPot d k g) (X0, z0) (pat u v)| ≤
        C * A * (1 + r ^ (-(σ + s - d + c)) * lw r ^ (b + 1)) *
          ((∏ i, ‖u i‖) * ∏ j, ‖v j‖) := by
  have hd1 : 1 ≤ d := by omega
  have hs0 := hk.s_pos
  obtain ⟨Cn0, hCn00, hCn0⟩ := near_integral_k hd hk
  have hCnex : ∃ Cn : ℝ, 0 ≤ Cn ∧ ∀ {g : Euc d × Euc d → ℝ} {A : ℝ} (_h : SrcCls d σ b m A g), 0 ≤ A →
      ∀ {a : ℕ}, a + c ≤ m → ∀ {r : ℝ}, 0 < r → r < 1 / 8 → ∀ (X0 z0 : Euc d), ‖z0‖ = r →
      ∀ (u : Fin a → Euc d) (v : Fin c → Euc d),
      |∫ x, kN k (r / 8) x * iteratedFDeriv ℝ (a + c) g (X0, z0 - x) (pat u v)| ≤
        Cn * A * (r ^ (-(σ + c)) * lw r ^ b) * r ^ ((d : ℝ) - s) * ((∏ i, ‖u i‖) * ∏ j, ‖v j‖) := by
    refine ⟨Cn0 * (2 * (8 / 7 : ℝ) ^ (σ + m) * 2 ^ b) * (1 / 8 : ℝ) ^ ((d : ℝ) - s), by positivity,
      fun {g} {A} h hA a hac r hr hr1 X0 z0 hz0 u v => ?_⟩
    have hρ : 0 < r / 8 := by positivity
    set Mt : ℝ := (2 * A * (8 / 7) ^ (σ + m) * 2 ^ b * (r ^ (-(σ + c)) * lw r ^ b)) *
      ((∏ i, ‖u i‖) * ∏ j, ‖v j‖) with hMt
    have hMt0 : 0 ≤ Mt := by
      have hP : 0 ≤ (∏ i, ‖u i‖) * ∏ j, ‖v j‖ :=
        mul_nonneg (Finset.prod_nonneg fun i _ => norm_nonneg _) (Finset.prod_nonneg fun i _ => norm_nonneg _)
      have h8 : 0 ≤ (8 / 7 : ℝ) ^ (σ + m) := Real.rpow_nonneg (by norm_num) _
      have hr' : 0 ≤ r ^ (-(σ + c)) := Real.rpow_nonneg hr.le _
      have hlw : 0 ≤ lw r ^ b := pow_nonneg (lw_pos r).le b
      exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hA) h8)
        (pow_nonneg (by norm_num) b)) (mul_nonneg hr' hlw)) hP
    have key := hCn0 (r / 8) Mt hρ (by linarith) hMt0
      (fun x => kN k (r / 8) x * iteratedFDeriv ℝ (a + c) g (X0, z0 - x) (pat u v)) ?_
    · rw [← Real.norm_eq_abs]
      refine key.trans ?_
      have hρb : (r / 8) ^ ((d : ℝ) - s) = (1 / 8 : ℝ) ^ ((d : ℝ) - s) * r ^ ((d : ℝ) - s) := by
        rw [show r / 8 = (1 / 8) * r by ring, Real.mul_rpow (by norm_num) hr.le]
      rw [hρb]
      have hMt' : Mt = (2 * (8 / 7 : ℝ) ^ (σ + m) * 2 ^ b) * A * (r ^ (-(σ + c)) * lw r ^ b) *
          ((∏ i, ‖u i‖) * ∏ j, ‖v j‖) := by rw [hMt]; ring
      rw [hMt']
      apply le_of_eq
      ring
    · intro x
      by_cases hx : ‖x‖ < r / 8
      · rw [norm_mul, mul_comm]
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
        have h1 : 7 * r / 8 ≤ ‖(X0, z0 - x).2‖ := by
          show 7 * r / 8 ≤ ‖z0 - x‖
          have h2 := norm_sub_norm_le z0 x
          linarith
        have h2 : ‖(X0, z0 - x).2‖ ≤ 9 * r / 8 := by
          show ‖z0 - x‖ ≤ 9 * r / 8
          have := norm_sub_le z0 x
          linarith
        have := h.g_pat_bound hA hσ0 hac hr hr1 h1 h2 u v
        rw [Real.norm_eq_abs, hMt, ← mul_assoc]
        exact this
      · have : kN k (r / 8) x = 0 := LocKer.kN_eq_zero hρ (not_lt.mp hx)
        simp [this]
  obtain ⟨Cn, hCn0', hCn⟩ := hCnex
  obtain ⟨Ck, hCk0, hCk⟩ := hk.kF_bound c
  obtain ⟨C1, C2, hC10, hC20, hfe⟩ := far_estimate hd hσ (σ + (s + c)) b
  set K1 : ℝ := (16 : ℝ) ^ (s + c) with hK1
  set K2 : ℝ := (2 : ℝ) ^ (s + c) with hK2
  have hK10 : 0 ≤ K1 := Real.rpow_nonneg (by norm_num) _
  have hK20 : 0 ≤ K2 := Real.rpow_nonneg (by norm_num) _
  refine ⟨Cn + 2 * C1 * Ck * K1 + 2 * C2 * Ck * K2, by positivity,
    fun {g} {A} h hA a hac r hr hr1 X0 z0 hz0 u v => ?_⟩
  set P : ℝ := (∏ i, ‖u i‖) * ∏ j, ‖v j‖ with hP
  have hP0 : 0 ≤ P :=
    mul_nonneg (Finset.prod_nonneg fun i _ => norm_nonneg _) (Finset.prod_nonneg fun i _ => norm_nonneg _)
  have hρ : 0 < r / 8 := by positivity
  rw [kpot_pat_eq hd1 hk hσ hA h hac hr hr1 X0 z0 hz0 u v]
  have hnear := hCn h hA hac hr hr1 X0 z0 hz0 u v
  -- far
  obtain ⟨hp1, hp2, hp3⟩ := far_pointwise_k hd hk hσ0 h hA hac hr hr1 X0 z0 u v hCk0
    (fun y => by have := hCk (r / 8) hρ y; rwa [show r / 8 / 2 = r / 16 by ring] at this) hz0
  have hint : Integrable (fun w => farKPsi d g k (r / 8) X0 z0 u v w) := by
    obtain ⟨-, -, hi⟩ := kPot_FL hd1 hk hσ hA h hr hr1 hz0
    have hp0 : ((X0, z0) : Euc d × Euc d) ∈ {p : Euc d × Euc d | ‖p.2 - z0‖ < r / 16} := by
      show ‖z0 - z0‖ < r / 16
      simp; positivity
    exact integrable_eval (hi (a + c) hac (X0, z0) hp0).2 (pat u v)
  set M1 : ℝ := Ck * (r / 16) ^ (-(s + (c : ℝ))) * (2 * A * P) with hM1
  set M2 : ℝ := Ck * K2 * (2 * A * P) with hM2
  have hM10 : 0 ≤ M1 := mul_nonneg (mul_nonneg hCk0 (Real.rpow_nonneg (by positivity) _))
    (mul_nonneg (mul_nonneg (by norm_num) hA) hP0)
  have hM20 : 0 ≤ M2 := mul_nonneg (mul_nonneg hCk0 hK20) (mul_nonneg (mul_nonneg (by norm_num) hA) hP0)
  have hfar := hfe r M1 M2 hr hr1 hM10 hM20 _ hint hp1 hp2 hp3
  -- arithmetic
  set W : ℝ := r ^ (-(σ + s - d + c)) with hW
  have hW0 : 0 ≤ W := Real.rpow_nonneg hr.le _
  have hexp1 : r ^ (-(σ + c)) * r ^ ((d : ℝ) - s) = W := by
    rw [← Real.rpow_add hr]; congr 1; ring
  have hexp2 : (r / 16) ^ (-(s + (c : ℝ))) * r ^ ((d : ℝ) - σ) = K1 * W := by
    rw [show r / 16 = (1 / 16 : ℝ) * r by ring, Real.mul_rpow (by norm_num) hr.le, mul_assoc,
      ← Real.rpow_add hr, hK1, one_div, Real.inv_rpow (by norm_num), ← Real.rpow_neg (by norm_num),
      neg_neg]
    congr 2
    ring
  have hexp3 : (d : ℝ) - (σ + (s + c)) = -(σ + s - d + c) := by ring
  rw [hexp3] at hfar
  set Lb : ℝ := lw r ^ b with hLb
  set L' : ℝ := lw r ^ (b + 1) with hL'
  have hLb0 : 0 ≤ Lb := pow_nonneg (lw_pos _).le b
  have hLL : Lb ≤ L' := pow_le_pow_right₀ (one_le_lw r) (by omega)
  have hLε : lw r ^ (b + if -(σ + s - d + c) = 0 then 1 else 0) ≤ L' := by
    refine pow_le_pow_right₀ (one_le_lw r) ?_
    split_ifs <;> omega
  set T : ℝ := 1 + W * L' with hT
  have hT1 : W * Lb ≤ T := by
    have : W * Lb ≤ W * L' := mul_le_mul_of_nonneg_left hLL hW0
    linarith
  have hT2 : 0 ≤ T := by
    have : 0 ≤ W * L' := mul_nonneg hW0 (hLb0.trans hLL)
    linarith
  have hX : 0 ≤ A * P := mul_nonneg hA hP0
  have hfar' : ‖∫ w, farKPsi d g k (r / 8) X0 z0 u v w‖ ≤
      C1 * M1 * (r ^ ((d : ℝ) - σ) * Lb) + C2 * M2 * T := by
    refine hfar.trans ?_
    have : C2 * M2 * (1 + r ^ (-(σ + s - d + c)) * lw r ^ (b + if -(σ + s - d + c) = 0 then 1 else 0)) ≤
        C2 * M2 * T := by
      refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hC20 hM20)
      rw [hT]
      have : r ^ (-(σ + s - d + c)) * lw r ^ (b + if -(σ + s - d + c) = 0 then 1 else 0) ≤ W * L' :=
        mul_le_mul_of_nonneg_left hLε hW0
      linarith
    linarith
  -- terms
  have t1 : Cn * A * (r ^ (-(σ + c)) * Lb) * r ^ ((d : ℝ) - s) * P = (Cn * (A * P)) * (W * Lb) := by
    calc _ = Cn * (A * P) * ((r ^ (-(σ + c)) * r ^ ((d : ℝ) - s)) * Lb) := by ring
      _ = _ := by rw [hexp1]
  have t2 : C1 * M1 * (r ^ ((d : ℝ) - σ) * Lb) = (2 * C1 * Ck * K1 * (A * P)) * (W * Lb) := by
    calc _ = 2 * C1 * Ck * (A * P) * (((r / 16) ^ (-(s + (c : ℝ))) * r ^ ((d : ℝ) - σ)) * Lb) := by
          rw [hM1]; ring
      _ = _ := by rw [hexp2]; ring
  have t3 : C2 * M2 * T = (2 * C2 * Ck * K2 * (A * P)) * T := by
    rw [hM2]; ring
  have hsum : |(∫ x, kN k (r / 8) x * iteratedFDeriv ℝ (a + c) g (X0, z0 - x) (pat u v)) +
      ∫ w, farKPsi d g k (r / 8) X0 z0 u v w| ≤
      (Cn * (A * P)) * (W * Lb) + (2 * C1 * Ck * K1 * (A * P)) * (W * Lb) +
        (2 * C2 * Ck * K2 * (A * P)) * T := by
    refine (abs_add_le _ _).trans ?_
    have e1 := hnear.trans_eq t1
    have e2 : |∫ w, farKPsi d g k (r / 8) X0 z0 u v w| ≤
        (2 * C1 * Ck * K1 * (A * P)) * (W * Lb) + (2 * C2 * Ck * K2 * (A * P)) * T := by
      rw [← Real.norm_eq_abs]
      refine hfar'.trans (le_of_eq ?_)
      rw [t2, t3]
    linarith
  have a1 : (Cn * (A * P)) * (W * Lb) ≤ (Cn * (A * P)) * T :=
    mul_le_mul_of_nonneg_left hT1 (mul_nonneg hCn0' hX)
  have a2 : (2 * C1 * Ck * K1 * (A * P)) * (W * Lb) ≤ (2 * C1 * Ck * K1 * (A * P)) * T :=
    mul_le_mul_of_nonneg_left hT1 (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hC10) hCk0) hK10) hX)
  refine hsum.trans ?_
  calc _ ≤ (Cn * (A * P)) * T + (2 * C1 * Ck * K1 * (A * P)) * T + (2 * C2 * Ck * K2 * (A * P)) * T := by
        linarith
    _ = _ := by rw [hT]; ring

end Base

end HRS.Parx

end
