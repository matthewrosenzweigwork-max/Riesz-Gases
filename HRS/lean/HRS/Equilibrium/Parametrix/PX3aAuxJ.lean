import HRS.Equilibrium.Parametrix.PX3aAuxI

/-!
# Packet PX3a auxiliaries J: pointwise bounds on the source jets
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.Parx

variable {d : ℕ}

namespace SrcCls

variable {σ : ℝ} {b m : ℕ} {A : ℝ} {g : Euc d × Euc d → ℝ}

/-- Pure form of the weight: for `0 < t ≤ 1` and `p ≥ 0`, `1 + t^{-p} L^b ≤ 2 t^{-p} L^b`. -/
lemma weight_pure {p : ℝ} (hp : 0 ≤ p) (b : ℕ) {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    1 + t ^ (-p) * lw t ^ b ≤ 2 * (t ^ (-p) * lw t ^ b) := by
  have h1 : 1 ≤ t ^ (-p) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos ht ht1 (by linarith)
  have h2 : 1 ≤ lw t ^ b := one_le_pow₀ (one_le_lw t)
  nlinarith

lemma g_pat_bound (h : SrcCls d σ b m A g) (hA : 0 ≤ A) (hσ0 : 0 ≤ σ) {a c : ℕ} (hac : a + c ≤ m)
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1 / 8) {q : Euc d × Euc d} (hq1 : 7 * r / 8 ≤ ‖q.2‖)
    (hq2 : ‖q.2‖ ≤ 9 * r / 8) (u : Fin a → Euc d) (v : Fin c → Euc d) :
    |iteratedFDeriv ℝ (a + c) g q (pat u v)| ≤
      (2 * A * (8 / 7) ^ (σ + m) * 2 ^ b * (r ^ (-(σ + c)) * lw r ^ b)) *
        (∏ i, ‖u i‖) * ∏ j, ‖v j‖ := by
  have hq0 : q.2 ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le (by positivity) hq1)
  have hqpos : 0 < ‖q.2‖ := norm_pos_iff.mpr hq0
  have hqU : q ∈ {p : Euc d × Euc d | p.2 ≠ 0} := hq0
  have hTB : TB g q a c (A * (1 + ‖q.2‖ ^ (-(σ + c)) * (1 + |Real.log ‖q.2‖|) ^ b)) :=
    tb_of_norm_le isOpen_ne_snd (h.smooth.of_le (by exact_mod_cast hac)) hqU
      (h.bound a c hac q.1 q.2 hq0)
  have hpc : 0 ≤ σ + c := by have : (0 : ℝ) ≤ c := Nat.cast_nonneg c; linarith
  have h1 := weight_pure hpc b hqpos (by linarith)
  have h2 : ‖q.2‖ ^ (-(σ + c)) ≤ (8 / 7) ^ (σ + m) * r ^ (-(σ + c)) := by
    have h3 : ‖q.2‖ ^ (-(σ + c)) ≤ (7 * r / 8) ^ (-(σ + c)) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hq1 (by linarith)
    refine h3.trans ?_
    have e : 7 * r / 8 = (7 / 8) * r := by ring
    rw [e, Real.mul_rpow (by norm_num) hr.le, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 7 / 8),
      ← Real.inv_rpow (by norm_num : (0 : ℝ) ≤ 7 / 8)]
    have h5 : ((7 / 8 : ℝ)⁻¹) ^ (σ + c) ≤ (8 / 7) ^ (σ + m) := by
      have : ((7 / 8 : ℝ)⁻¹) = 8 / 7 := by norm_num
      rw [this]
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by
        have : (c : ℝ) ≤ m := by exact_mod_cast (by omega : c ≤ m)
        linarith)
    have : 0 ≤ r ^ (-(σ + c)) := by positivity
    exact mul_le_mul_of_nonneg_right h5 this
  have h4 : lw ‖q.2‖ ^ b ≤ (2 * lw r) ^ b :=
    pow_le_pow_left₀ (lw_pos _).le (lw_le_two_mul hr (by linarith) (by linarith)) b
  refine (hTB u v).trans ?_
  have hP1 : 0 ≤ ∏ i, ‖u i‖ := Finset.prod_nonneg fun i _ => norm_nonneg _
  have hP2 : 0 ≤ ∏ j, ‖v j‖ := Finset.prod_nonneg fun i _ => norm_nonneg _
  have h1' : 1 + ‖q.2‖ ^ (-(σ + c)) * (1 + |Real.log ‖q.2‖|) ^ b ≤
      2 * (‖q.2‖ ^ (-(σ + c)) * lw ‖q.2‖ ^ b) := h1
  have hl0 : 0 ≤ lw ‖q.2‖ ^ b := by have := lw_pos ‖q.2‖; positivity
  have hW : A * (1 + ‖q.2‖ ^ (-(σ + c)) * (1 + |Real.log ‖q.2‖|) ^ b) ≤
      2 * A * (8 / 7) ^ (σ + m) * 2 ^ b * (r ^ (-(σ + c)) * lw r ^ b) := by
    calc A * (1 + ‖q.2‖ ^ (-(σ + c)) * (1 + |Real.log ‖q.2‖|) ^ b)
        ≤ A * (2 * (‖q.2‖ ^ (-(σ + c)) * lw ‖q.2‖ ^ b)) := by gcongr
      _ ≤ A * (2 * (((8 / 7) ^ (σ + m) * r ^ (-(σ + c))) * (2 * lw r) ^ b)) := by
          gcongr
      _ = _ := by rw [mul_pow]; ring
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hW hP1) hP2


end SrcCls

lemma eval_integral {α : Type*} [MeasurableSpace α] {μ : Measure α} {n : ℕ}
    {F : α → ContinuousMultilinearMap ℝ (fun _ : Fin n => Euc d × Euc d) ℝ} (hF : Integrable F μ)
    (x : Fin n → Euc d × Euc d) :
    (∫ w, F w ∂μ) x = ∫ w, F w x ∂μ := by
  exact ContinuousMultilinearMap.integral_apply hF x

namespace SrcCls

variable {σ : ℝ} {b m : ℕ} {A : ℝ} {g : Euc d × Euc d → ℝ}

/-- Evaluated near integral, `κ = 0`. -/
lemma near_val_zero (hd : 2 ≤ d) (hσ0 : 0 ≤ σ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {g : Euc d × Euc d → ℝ} {A : ℝ} (h : SrcCls d σ b m A g), 0 ≤ A → ∀ {a c : ℕ}, a + c ≤ m →
      ∀ {r : ℝ}, 0 < r → r < 1 / 8 → ∀ (X0 z0 : Euc d), ‖z0‖ = r →
      ∀ (u : Fin a → Euc d) (v : Fin c → Euc d),
      |∫ x, Ln d 0 (r / 8) x * iteratedFDeriv ℝ (a + c) g (X0, z0 - x) (pat u v)| ≤
        C * A * (r ^ (-(σ + c)) * lw r ^ b) * (r ^ (2 : ℝ) * lw r ^ (if d = 2 then 1 else 0)) *
          ((∏ i, ‖u i‖) * ∏ j, ‖v j‖) := by
  obtain ⟨C0, hC0, hC⟩ := near_integral_zero hd
  have hK1 : 0 ≤ 2 * (8 / 7 : ℝ) ^ (σ + m) * 2 ^ b := by positivity
  have hK2 : 0 ≤ (1 / 8 : ℝ) ^ (2 : ℝ) * lw (1 / 8) ^ (if d = 2 then 1 else 0) := by
    have := lw_pos (1 / 8 : ℝ); positivity
  refine ⟨C0 * (2 * (8 / 7 : ℝ) ^ (σ + m) * 2 ^ b) * ((1 / 8 : ℝ) ^ (2 : ℝ) * lw (1 / 8) ^ (if d = 2 then 1 else 0)),
    mul_nonneg (mul_nonneg hC0 hK1) hK2, fun {g} {A} h hA a c hac r hr hr1 X0 z0 hz0 u v => ?_⟩
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
  have key := hC (r / 8) Mt hρ (by linarith) hMt0
    (fun x => Ln d 0 (r / 8) x * iteratedFDeriv ℝ (a + c) g (X0, z0 - x) (pat u v)) ?_
  · rw [← Real.norm_eq_abs]
    refine key.trans ?_
    have hρb : (r / 8) ^ (2 : ℝ) * lw (r / 8) ^ (if d = 2 then 1 else 0) ≤
        ((1 / 8 : ℝ) ^ (2 : ℝ) * lw (1 / 8) ^ (if d = 2 then 1 else 0)) *
          (r ^ (2 : ℝ) * lw r ^ (if d = 2 then 1 else 0)) := by
      have h1 : lw (r / 8) ≤ lw r * lw (1 / 8) := by
        have := lw_mul_le hr (by norm_num : (0 : ℝ) < 1 / 8)
        have e : r * (1 / 8) = r / 8 := by ring
        rwa [e] at this
      have h2 : lw (r / 8) ^ (if d = 2 then 1 else 0) ≤ (lw r * lw (1 / 8)) ^ (if d = 2 then 1 else 0) :=
        pow_le_pow_left₀ (lw_pos _).le h1 _
      rw [mul_pow] at h2
      have h3 : (r / 8) ^ (2 : ℝ) = (1 / 8 : ℝ) ^ (2 : ℝ) * r ^ (2 : ℝ) := by
        rw [show r / 8 = (1 / 8) * r by ring, Real.mul_rpow (by norm_num) hr.le]
      rw [h3]
      have h4 : 0 ≤ (1 / 8 : ℝ) ^ (2 : ℝ) * r ^ (2 : ℝ) := by positivity
      calc (1 / 8 : ℝ) ^ (2 : ℝ) * r ^ (2 : ℝ) * lw (r / 8) ^ (if d = 2 then 1 else 0)
          ≤ (1 / 8 : ℝ) ^ (2 : ℝ) * r ^ (2 : ℝ) *
            (lw r ^ (if d = 2 then 1 else 0) * lw (1 / 8) ^ (if d = 2 then 1 else 0)) :=
            mul_le_mul_of_nonneg_left h2 h4
        _ = _ := by ring
    have hC0' := hC0
    have hMt' : Mt = (2 * (8 / 7 : ℝ) ^ (σ + m) * 2 ^ b) * A * (r ^ (-(σ + c)) * lw r ^ b) *
        ((∏ i, ‖u i‖) * ∏ j, ‖v j‖) := by rw [hMt]; ring
    rw [hMt']
    have hrest : 0 ≤ C0 * ((2 * (8 / 7 : ℝ) ^ (σ + m) * 2 ^ b) * A * (r ^ (-(σ + c)) * lw r ^ b) *
        ((∏ i, ‖u i‖) * ∏ j, ‖v j‖)) := by
      have : 0 ≤ Mt := hMt0
      rw [hMt'] at this
      exact mul_nonneg hC0 this
    calc C0 * ((2 * (8 / 7 : ℝ) ^ (σ + m) * 2 ^ b) * A * (r ^ (-(σ + c)) * lw r ^ b) *
          ((∏ i, ‖u i‖) * ∏ j, ‖v j‖)) * ((r / 8) ^ (2 : ℝ) * lw (r / 8) ^ (if d = 2 then 1 else 0))
        ≤ C0 * ((2 * (8 / 7 : ℝ) ^ (σ + m) * 2 ^ b) * A * (r ^ (-(σ + c)) * lw r ^ b) *
          ((∏ i, ‖u i‖) * ∏ j, ‖v j‖)) * (((1 / 8 : ℝ) ^ (2 : ℝ) * lw (1 / 8) ^ (if d = 2 then 1 else 0)) *
          (r ^ (2 : ℝ) * lw r ^ (if d = 2 then 1 else 0))) := mul_le_mul_of_nonneg_left hρb hrest
      _ = _ := by ring
  · intro x
    by_cases hx : ‖x‖ < r / 8
    · rw [norm_mul, mul_comm]
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      have h1 : 7 * r / 8 ≤ ‖(X0, z0 - x).2‖ := by
        have := norm_sub_norm_le z0 x
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
    · have : Ln d 0 (r / 8) x = 0 := by simp [Ln, px3a_zeta_eq_zero hρ (not_lt.mp hx)]
      simp [this]

/-- Evaluated near integral, `d = 2`, `κ = Ekap`. -/
lemma near_val_two (hσ0 : 0 ≤ σ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {g : Euc 2 × Euc 2 → ℝ} {A : ℝ} (h : SrcCls 2 σ b m A g), 0 ≤ A →
      ∀ {a c : ℕ}, a + c ≤ m →
      ∀ {r : ℝ}, 0 < r → r < 1 / 8 → ∀ (X0 z0 : Euc 2), ‖z0‖ = r →
      ∀ (u : Fin a → Euc 2) (v : Fin c → Euc 2),
      |∫ x, Ln 2 (Ekap 2 r) (r / 8) x * iteratedFDeriv ℝ (a + c) g (X0, z0 - x) (pat u v)| ≤
        C * A * (r ^ (-(σ + c)) * lw r ^ b) * r ^ (2 : ℝ) *
          ((∏ i, ‖u i‖) * ∏ j, ‖v j‖) := by
  obtain ⟨C0, hC0, hC⟩ := near_integral_two
  have hK1 : 0 ≤ 2 * (8 / 7 : ℝ) ^ (σ + m) * 2 ^ b := by positivity
  refine ⟨C0 * (2 * (8 / 7 : ℝ) ^ (σ + m) * 2 ^ b), mul_nonneg hC0 hK1,
    fun {g} {A} h hA a c hac r hr hr1 X0 z0 hz0 u v => ?_⟩
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
  have key := hC r Mt hr (by linarith) hMt0
    (fun x => Ln 2 (Ekap 2 r) (r / 8) x * iteratedFDeriv ℝ (a + c) g (X0, z0 - x) (pat u v)) ?_
  · rw [← Real.norm_eq_abs]
    refine key.trans (le_of_eq ?_)
    rw [hMt]; ring
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
    · have : Ln 2 (Ekap 2 r) (r / 8) x = 0 := by simp [Ln, px3a_zeta_eq_zero hρ (not_lt.mp hx)]
      simp [this]

end SrcCls

end HRS.Parx

end
