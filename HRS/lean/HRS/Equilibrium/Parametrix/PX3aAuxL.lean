import HRS.Equilibrium.Parametrix.PX3aAuxK

/-!
# Packet PX3a auxiliaries L: the base estimate for the Newton potential (`0 ≤ σ < d`)
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.Parx

variable {d : ℕ}

local notation "∞'" => ((⊤ : ℕ∞) : WithTop ℕ∞)

lemma intg_contDiffOn (hd : 2 ≤ d) {σ : ℝ} (hσ : σ < d) {b m : ℕ} {A : ℝ} (hA : 0 ≤ A)
    {g : Euc d × Euc d → ℝ} (h : SrcCls d σ b m A g) {r : ℝ} (hr : 0 < r) (hr1 : r < 1 / 8)
    {z0 : Euc d} (hz0 : ‖z0‖ = r) :
    ContDiffOn ℝ (m : WithTop ℕ∞) (fun p : Euc d × Euc d => ∫ w, g (p.1, w))
      {p : Euc d × Euc d | ‖p.2 - z0‖ < r / 16} := by
  have h0 := (newtonPot_FL hd hσ hA h hr hr1 hz0 0).1
  have h1 := (newtonPot_FL hd hσ hA h hr hr1 hz0 1).1
  refine (h0.sub h1).congr ?_
  intro p _
  simp

lemma intg_contDiff (hd : 2 ≤ d) {σ : ℝ} (hσ : σ < d) {b m : ℕ} {A : ℝ} (hA : 0 ≤ A)
    {g : Euc d × Euc d → ℝ} (h : SrcCls d σ b m A g) :
    ContDiff ℝ (m : WithTop ℕ∞) (fun X : Euc d => ∫ w, g (X, w)) := by
  have : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
  rw [contDiff_iff_contDiffAt]
  intro X0
  set z0 : Euc d := (1 / 16 : ℝ) • EuclideanSpace.single (⟨0, by omega⟩ : Fin d) (1 : ℝ) with hz
  have hz0 : ‖z0‖ = 1 / 16 := by
    rw [hz, norm_smul]; simp
  have h1 := intg_contDiffOn hd hσ hA h (r := 1 / 16) (by norm_num) (by norm_num) hz0
  have hU : IsOpen {p : Euc d × Euc d | ‖p.2 - z0‖ < 1 / 16 / 16} := isOpen_near z0 _
  have h2 : ContDiffAt ℝ (m : WithTop ℕ∞) (fun p : Euc d × Euc d => ∫ w, g (p.1, w)) (X0, z0) :=
    h1.contDiffAt (hU.mem_nhds (by simp))
  have h3 : ContDiffAt ℝ (m : WithTop ℕ∞) (fun X : Euc d => ((X, z0) : Euc d × Euc d)) X0 :=
    (by fun_prop : ContDiff ℝ (m : WithTop ℕ∞) (fun X : Euc d => ((X, z0) : Euc d × Euc d))).contDiffAt
  exact ContDiffAt.comp (g := fun p : Euc d × Euc d => ∫ w, g (p.1, w))
    (f := fun X : Euc d => ((X, z0) : Euc d × Euc d)) X0 h2 h3

lemma newtonPot_pat_eq (hd : 2 ≤ d) {σ : ℝ} (hσ : σ < d) {b m : ℕ} {A : ℝ} (hA : 0 ≤ A)
    {g : Euc d × Euc d → ℝ} (h : SrcCls d σ b m A g) {a c : ℕ} (hac : a + c ≤ m) (hc : 1 ≤ c)
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1 / 8) (X0 z0 : Euc d) (hz0 : ‖z0‖ = r) (κ : ℝ)
    (u : Fin a → Euc d) (v : Fin c → Euc d) :
    iteratedFDeriv ℝ (a + c) (newtonPot d g) (X0, z0) (pat u v) =
      (∫ x, Ln d κ (r / 8) x * iteratedFDeriv ℝ (a + c) g (X0, z0 - x) (pat u v)) +
        ∫ w, farPsi d g κ (r / 8) X0 z0 u v w := by
  obtain ⟨hs, hform, hint⟩ := newtonPot_FL hd hσ hA h hr hr1 hz0 κ
  set ψ : Euc d → ℝ := fun X => ∫ w, g (X, w) with hψdef
  have hψ : ContDiff ℝ (m : WithTop ℕ∞) ψ := intg_contDiff hd hσ hA h
  have hU : IsOpen {p : Euc d × Euc d | ‖p.2 - z0‖ < r / 16} := isOpen_near z0 _
  have hp0 : ((X0, z0) : Euc d × Euc d) ∈ {p : Euc d × Euc d | ‖p.2 - z0‖ < r / 16} := by
    show ‖z0 - z0‖ < r / 16
    simp; positivity
  have hΦ : ContDiffAt ℝ ((a + c : ℕ) : WithTop ℕ∞)
      (fun p : Euc d × Euc d => newtonPot d g p - κ * ∫ w, g (p.1, w)) (X0, z0) :=
    (hs.contDiffAt (hU.mem_nhds hp0)).of_le (by exact_mod_cast hac)
  have hΨ : ContDiff ℝ ((a + c : ℕ) : WithTop ℕ∞) (fun X : Euc d => κ * ψ X) :=
    (contDiff_const.mul hψ).of_le (by exact_mod_cast hac)
  have hΨ' : ContDiffAt ℝ ((a + c : ℕ) : WithTop ℕ∞) (fun p : Euc d × Euc d => κ * ψ p.1) (X0, z0) :=
    (hΨ.comp contDiff_fst).contDiffAt
  have e : newtonPot d g = (fun p : Euc d × Euc d => newtonPot d g p - κ * ∫ w, g (p.1, w)) +
      (fun p : Euc d × Euc d => κ * ψ p.1) := by
    funext p; simp [hψdef]
  have h2 : iteratedFDeriv ℝ (a + c) (fun p : Euc d × Euc d => κ * ψ p.1) (X0, z0) (pat u v) = 0 := by
    have e2 : (fun p : Euc d × Euc d => κ * ψ p.1) =
        fun q : Euc d × Euc d => (fun _ : Euc d => (1 : ℝ)) q.2 * (fun X : Euc d => κ * ψ X) q.1 := by
      funext q; simp
    rw [e2, iteratedFDeriv_prodpat (a + c) a c rfl _ _ contDiff_const hΨ (X0, z0) u v]
    have : iteratedFDeriv ℝ c (fun _ : Euc d => (1 : ℝ)) z0 = 0 := by
      have := iteratedFDeriv_const_of_ne (𝕜 := ℝ) (E := Euc d) (by omega : c ≠ 0) (1 : ℝ)
      exact congrFun this z0
    simp [this]
  conv_lhs => rw [e]
  rw [iteratedFDeriv_add_apply hΦ hΨ', ContinuousMultilinearMap.add_apply, h2, add_zero]
  obtain ⟨hi1, hi2⟩ := hint (a + c) hac (X0, z0) hp0
  rw [hform (a + c) hac (X0, z0) hp0, ContinuousMultilinearMap.add_apply,
    eval_integral hi1, eval_integral hi2]
  rfl

lemma integrable_eval {α : Type*} [MeasurableSpace α] {μ : Measure α} {n : ℕ}
    {F : α → ContinuousMultilinearMap ℝ (fun _ : Fin n => Euc d × Euc d) ℝ} (hF : Integrable F μ)
    (x : Fin n → Euc d × Euc d) : Integrable (fun w => F w x) μ :=
  (ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => Euc d × Euc d) ℝ x).integrable_comp hF

lemma near_val_any (hd : 2 ≤ d) {σ : ℝ} (hσ0 : 0 ≤ σ) (b m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {g : Euc d × Euc d → ℝ} {A : ℝ} (_h : SrcCls d σ b m A g), 0 ≤ A →
      ∀ {a c : ℕ}, a + c ≤ m → ∀ {r : ℝ}, 0 < r → r < 1 / 8 → ∀ (X0 z0 : Euc d), ‖z0‖ = r →
      ∀ (u : Fin a → Euc d) (v : Fin c → Euc d),
      |∫ x, Ln d (Ekap d r) (r / 8) x * iteratedFDeriv ℝ (a + c) g (X0, z0 - x) (pat u v)| ≤
        C * A * (r ^ (-(σ + c)) * lw r ^ b) * r ^ (2 : ℝ) * ((∏ i, ‖u i‖) * ∏ j, ‖v j‖) := by
  by_cases h2 : d = 2
  · subst h2
    exact SrcCls.near_val_two hσ0
  · obtain ⟨C, hC0, hC⟩ := SrcCls.near_val_zero (d := d) (σ := σ) (b := b) (m := m) hd hσ0
    refine ⟨C, hC0, fun {g} {A} h hA a c hac r hr hr1 X0 z0 hz0 u v => ?_⟩
    have e : Ekap d r = 0 := by simp [Ekap, h2]
    rw [e]
    refine (hC h hA hac hr hr1 X0 z0 hz0 u v).trans (le_of_eq ?_)
    rw [if_neg h2, pow_zero, mul_one]

set_option maxHeartbeats 1600000 in
/-- Base estimate (`c ≥ 1`, `0 ≤ σ < d`). -/
lemma base_pos (hd : 2 ≤ d) {σ : ℝ} (hσ0 : 0 ≤ σ) (hσ : σ < d) (b m : ℕ) {c : ℕ} (hc : 1 ≤ c) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {g : Euc d × Euc d → ℝ} {A : ℝ} (_h : SrcCls d σ b m A g), 0 ≤ A →
      ∀ {a : ℕ}, a + c ≤ m → ∀ {r : ℝ}, 0 < r → r < 1 / 8 → ∀ (X0 z0 : Euc d), ‖z0‖ = r →
      ∀ (u : Fin a → Euc d) (v : Fin c → Euc d),
      |iteratedFDeriv ℝ (a + c) (newtonPot d g) (X0, z0) (pat u v)| ≤
        C * A * (1 + r ^ (-(σ - 2 + c)) * lw r ^ (b + if σ - 2 + (c : ℝ) = 0 then 1 else 0)) *
          ((∏ i, ‖u i‖) * ∏ j, ‖v j‖) := by
  obtain ⟨Cn, hCn0, hCn⟩ := near_val_any hd hσ0 b m
  obtain ⟨Ck, hCk0, hCk⟩ := far_kernel_bound hd hc
  obtain ⟨C1, C2, hC10, hC20, hfe⟩ := far_estimate hd hσ (σ + c + ((d : ℝ) - 2)) b
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hc1 : (1 : ℝ) ≤ c := by exact_mod_cast hc
  have he0n : (2 : ℝ) - d - c < 0 := by linarith
  set e0 : ℝ := (2 : ℝ) - d - c with he0
  set K1 : ℝ := (1 / 16 : ℝ) ^ e0 with hK1
  set K2 : ℝ := (2 : ℝ) ^ (-e0) with hK2
  have hK10 : 0 ≤ K1 := Real.rpow_nonneg (by norm_num) _
  have hK20 : 0 ≤ K2 := Real.rpow_nonneg (by norm_num) _
  refine ⟨Cn + 2 * C1 * Ck * K1 + 2 * C2 * Ck * K2, by positivity, fun {g} {A} h hA a hac r hr hr1 X0 z0 hz0 u v => ?_⟩
  set P : ℝ := (∏ i, ‖u i‖) * ∏ j, ‖v j‖ with hP
  have hP0 : 0 ≤ P :=
    mul_nonneg (Finset.prod_nonneg fun i _ => norm_nonneg _) (Finset.prod_nonneg fun i _ => norm_nonneg _)
  have hρ : 0 < r / 8 := by positivity
  -- decomposition
  rw [newtonPot_pat_eq hd hσ hA h hac hc hr hr1 X0 z0 hz0 (Ekap d r) u v]
  have hnear := hCn h hA hac hr hr1 X0 z0 hz0 u v
  -- far
  obtain ⟨hp1, hp2, hp3⟩ := far_pointwise hd hσ0 h hA hac hr hr1 X0 z0 hz0 u v hCk0 (hCk r hr) he0n
  have hint : Integrable (fun w => farPsi d g (Ekap d r) (r / 8) X0 z0 u v w) := by
    obtain ⟨-, -, hi⟩ := newtonPot_FL hd hσ hA h hr hr1 hz0 (Ekap d r)
    have hp0 : ((X0, z0) : Euc d × Euc d) ∈ {p : Euc d × Euc d | ‖p.2 - z0‖ < r / 16} := by
      show ‖z0 - z0‖ < r / 16
      simp; positivity
    exact integrable_eval (hi (a + c) hac (X0, z0) hp0).2 (pat u v)
  set M1 : ℝ := Ck * (r / 16) ^ e0 * (2 * A * P) with hM1
  set M2 : ℝ := Ck * K2 * (2 * A * P) with hM2
  have hM10 : 0 ≤ M1 := mul_nonneg (mul_nonneg hCk0 (Real.rpow_nonneg (by positivity) _))
    (mul_nonneg (mul_nonneg (by norm_num) hA) hP0)
  have hM20 : 0 ≤ M2 := mul_nonneg (mul_nonneg hCk0 hK20) (mul_nonneg (mul_nonneg (by norm_num) hA) hP0)
  have hfar := hfe r M1 M2 hr hr1 hM10 hM20 _ hint hp1 hp2 hp3
  -- arithmetic
  set W : ℝ := r ^ (-(σ - 2 + c)) with hW
  have hW0 : 0 ≤ W := Real.rpow_nonneg hr.le _
  have hexp1 : r ^ (-(σ + c)) * r ^ (2 : ℝ) = W := by
    rw [← Real.rpow_add hr]; congr 1; ring
  have hexp2 : (r / 16) ^ e0 * r ^ ((d : ℝ) - σ) = K1 * W := by
    rw [show r / 16 = (1 / 16 : ℝ) * r by ring, Real.mul_rpow (by norm_num) hr.le, hK1, mul_assoc,
      ← Real.rpow_add hr]
    congr 2
    rw [he0]; ring
  have hexp3 : (d : ℝ) - (σ + c + ((d : ℝ) - 2)) = -(σ - 2 + c) := by ring
  rw [hexp3] at hfar
  have hif : (-(σ - 2 + (c : ℝ)) = 0) ↔ (σ - 2 + (c : ℝ) = 0) := neg_eq_zero
  simp only [hif] at hfar
  set ε : ℕ := if σ - 2 + (c : ℝ) = 0 then 1 else 0 with hε
  set Lb : ℝ := lw r ^ b with hLb
  set L' : ℝ := lw r ^ (b + ε) with hL'
  have hLb0 : 0 ≤ Lb := pow_nonneg (lw_pos _).le b
  have hLL : Lb ≤ L' := pow_le_pow_right₀ (one_le_lw r) (by omega)
  set T : ℝ := 1 + W * L' with hT
  have hT1 : W * Lb ≤ T := by
    have : W * Lb ≤ W * L' := mul_le_mul_of_nonneg_left hLL hW0
    linarith
  have hT2 : 0 ≤ T := by
    have : 0 ≤ W * L' := mul_nonneg hW0 (hLb0.trans hLL)
    linarith
  have hX : 0 ≤ A * P := mul_nonneg hA hP0
  -- term 1
  have t1 : Cn * A * (r ^ (-(σ + c)) * Lb) * r ^ (2 : ℝ) * P = (Cn * (A * P)) * (W * Lb) := by
    calc _ = Cn * (A * P) * ((r ^ (-(σ + c)) * r ^ (2 : ℝ)) * Lb) := by ring
      _ = _ := by rw [hexp1]
  have t2 : C1 * M1 * (r ^ ((d : ℝ) - σ) * Lb) = (2 * C1 * Ck * K1 * (A * P)) * (W * Lb) := by
    calc _ = 2 * C1 * Ck * (A * P) * (((r / 16) ^ e0 * r ^ ((d : ℝ) - σ)) * Lb) := by rw [hM1]; ring
      _ = _ := by rw [hexp2]; ring
  have t3 : C2 * M2 * (1 + W * L') = (2 * C2 * Ck * K2 * (A * P)) * T := by
    rw [hM2, hT]; ring
  have hsum : |(∫ x, Ln d (Ekap d r) (r / 8) x * iteratedFDeriv ℝ (a + c) g (X0, z0 - x) (pat u v)) +
      ∫ w, farPsi d g (Ekap d r) (r / 8) X0 z0 u v w| ≤
      (Cn * (A * P)) * (W * Lb) + (2 * C1 * Ck * K1 * (A * P)) * (W * Lb) +
        (2 * C2 * Ck * K2 * (A * P)) * T := by
    refine (abs_add_le _ _).trans ?_
    have e1 := hnear.trans_eq t1
    have e2 : |∫ w, farPsi d g (Ekap d r) (r / 8) X0 z0 u v w| ≤
        (2 * C1 * Ck * K1 * (A * P)) * (W * Lb) + (2 * C2 * Ck * K2 * (A * P)) * T := by
      rw [← Real.norm_eq_abs]
      exact hfar.trans_eq (by rw [t2, t3])
    linarith
  have a1 : (Cn * (A * P)) * (W * Lb) ≤ (Cn * (A * P)) * T :=
    mul_le_mul_of_nonneg_left hT1 (mul_nonneg hCn0 hX)
  have a2 : (2 * C1 * Ck * K1 * (A * P)) * (W * Lb) ≤ (2 * C1 * Ck * K1 * (A * P)) * T :=
    mul_le_mul_of_nonneg_left hT1 (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hC10) hCk0) hK10) hX)
  refine hsum.trans ?_
  calc _ ≤ (Cn * (A * P)) * T + (2 * C1 * Ck * K1 * (A * P)) * T + (2 * C2 * Ck * K2 * (A * P)) * T := by
        linarith
    _ = _ := by ring

lemma Lf_zero_abs_le {ρ : ℝ} (y : Euc d) : |Lf d 0 ρ y| ≤ |Efund d y| := by
  unfold Lf
  rw [sub_zero, abs_mul, abs_mul]
  have h1 : |1 - px3a_zeta d ρ y| ≤ 1 := by
    rw [abs_of_nonneg (by linarith [px3a_zeta_le_one (d := d) ρ y])]
    linarith [px3a_zeta_nonneg (d := d) ρ y]
  have h2 : |px3a_zeta d 1 y| ≤ 1 := by
    rw [abs_of_nonneg (px3a_zeta_nonneg 1 y)]; exact px3a_zeta_le_one 1 y
  calc |1 - px3a_zeta d ρ y| * |px3a_zeta d 1 y| * |Efund d y| ≤ 1 * 1 * |Efund d y| := by
        gcongr
    _ = _ := by ring

lemma Lf_zero_eq_zero {ρ : ℝ} (hρ : 0 < ρ) {y : Euc d} (hy : ‖y‖ ≤ ρ / 2) : Lf d 0 ρ y = 0 := by
  simp [Lf, px3a_zeta_eq_one hρ hy]

set_option maxHeartbeats 1600000 in
lemma far_pointwise_zero (hd : 2 ≤ d) {σ : ℝ} (hσ0 : 0 ≤ σ) (b m : ℕ) :
    ∃ K1 K2 : ℝ, 0 ≤ K1 ∧ 0 ≤ K2 ∧ ∀ {g : Euc d × Euc d → ℝ} {A : ℝ} (h : SrcCls d σ b m A g), 0 ≤ A →
      ∀ {a : ℕ}, a + 0 ≤ m → ∀ {r : ℝ}, 0 < r → r < 1 / 8 → ∀ (X0 z0 : Euc d), ‖z0‖ = r →
      ∀ (u : Fin a → Euc d) (v : Fin 0 → Euc d),
    (∀ᵐ w : Euc d ∂volume, ‖w‖ < 2 * r → ‖farPsi d g 0 (r / 8) X0 z0 u v w‖ ≤
      (K1 * r ^ (-((d : ℝ) - 2)) * (2 * A * ((∏ i, ‖u i‖) * ∏ j, ‖v j‖))) *
        (‖w‖ ^ (-σ) * lw ‖w‖ ^ (b + if d = 2 then 1 else 0))) ∧
    (∀ᵐ w : Euc d ∂volume, 2 * r ≤ ‖w‖ → ‖w‖ < 1 / 16 → ‖farPsi d g 0 (r / 8) X0 z0 u v w‖ ≤
      (K2 * (2 * A * ((∏ i, ‖u i‖) * ∏ j, ‖v j‖))) *
        (‖w‖ ^ (-(σ + ((d : ℝ) - 2))) * lw ‖w‖ ^ (b + if d = 2 then 1 else 0))) ∧
    (∀ᵐ w : Euc d ∂volume, 1 / 16 ≤ ‖w‖ → farPsi d g 0 (r / 8) X0 z0 u v w = 0) := by
  obtain ⟨c0, hc0, hE⟩ := Efund_abs_le hd
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  set ε : ℕ := if d = 2 then 1 else 0 with hε
  have hlw32 : 0 ≤ lw (1 / 32 : ℝ) ^ ε := pow_nonneg (lw_pos _).le _
  refine ⟨c0 * (16 : ℝ) ^ ((d : ℝ) - 2) * lw (1 / 32 : ℝ) ^ ε, c0 * (2 : ℝ) ^ ((d : ℝ) - 2) * 2 ^ ε,
    mul_nonneg (mul_nonneg hc0 (Real.rpow_nonneg (by norm_num) _)) hlw32,
    mul_nonneg (mul_nonneg hc0 (Real.rpow_nonneg (by norm_num) _)) (pow_nonneg (by norm_num) _),
    fun {g} {A} h hA a hac r hr hr1 X0 z0 hz0 u v => ?_⟩
  have hρ : 0 < r / 8 := by positivity
  have hae0 := ae_ne_zero_euc (d := d) (by omega)
  have hae16 := ae_norm_ne_sixteenth (d := d) (by omega)
  have hP0 : 0 ≤ (∏ i, ‖u i‖) * ∏ j, ‖v j‖ :=
    mul_nonneg (Finset.prod_nonneg fun i _ => norm_nonneg _) (Finset.prod_nonneg fun i _ => norm_nonneg _)
  have hPu : 0 ≤ ∏ i, ‖u i‖ := Finset.prod_nonneg fun i _ => norm_nonneg _
  have hPv : 0 ≤ ∏ j, ‖v j‖ := Finset.prod_nonneg fun i _ => norm_nonneg _
  have hnorm0 : ∀ y : Euc d, ‖iteratedFDeriv ℝ 0 (Lf d 0 (r / 8)) y‖ = |Lf d 0 (r / 8) y| := by
    intro y; rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs]
  -- common: pointwise farPsi bound
  have key : ∀ w : Euc d, w ≠ 0 → ‖w‖ ≤ 1 / 16 →
      |farPsi d g 0 (r / 8) X0 z0 u v w| ≤
        |Lf d 0 (r / 8) (z0 - w)| * (2 * A * (‖w‖ ^ (-σ) * lw ‖w‖ ^ b)) * ((∏ i, ‖u i‖) * ∏ j, ‖v j‖) := by
    intro w hw0 hw1
    refine (farPsi_bound h hσ0 hρ 0 hac X0 z0 u v hw0 hw1).trans ?_
    rw [hnorm0]
    have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hw0
    have hs := SrcCls.weight_pure hσ0 b hwpos (by linarith)
    have hs' : A * (1 + ‖w‖ ^ (-σ) * lw ‖w‖ ^ b) ≤ 2 * A * (‖w‖ ^ (-σ) * lw ‖w‖ ^ b) := by nlinarith
    have hwl : 0 ≤ ‖w‖ ^ (-σ) * lw ‖w‖ ^ b :=
      mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (pow_nonneg (lw_pos _).le b)
    have hL0 : 0 ≤ |Lf d 0 (r / 8) (z0 - w)| := abs_nonneg _
    calc |Lf d 0 (r / 8) (z0 - w)| * (∏ j, ‖v j‖) * ((A * (1 + ‖w‖ ^ (-σ) * lw ‖w‖ ^ b)) * ∏ i, ‖u i‖)
        ≤ |Lf d 0 (r / 8) (z0 - w)| * (∏ j, ‖v j‖) * ((2 * A * (‖w‖ ^ (-σ) * lw ‖w‖ ^ b)) * ∏ i, ‖u i‖) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hs' hPu) (mul_nonneg hL0 hPv)
      _ = _ := by ring
  refine ⟨?_, ?_, ?_⟩
  · filter_upwards [hae0] with w hw0 hw2
    rw [Real.norm_eq_abs]
    have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hw0
    have hnn : 0 ≤ ((c0 * (16 : ℝ) ^ ((d : ℝ) - 2) * lw (1 / 32 : ℝ) ^ ε) * r ^ (-((d : ℝ) - 2)) *
        (2 * A * ((∏ i, ‖u i‖) * ∏ j, ‖v j‖))) * (‖w‖ ^ (-σ) * lw ‖w‖ ^ (b + ε)) := by
      have h2 : 0 ≤ ‖w‖ ^ (-σ) := Real.rpow_nonneg (norm_nonneg _) _
      have h3 : 0 ≤ lw ‖w‖ ^ (b + ε) := pow_nonneg (lw_pos _).le _
      have h1 : 0 ≤ r ^ (-((d : ℝ) - 2)) := Real.rpow_nonneg hr.le _
      exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hc0 (Real.rpow_nonneg (by norm_num) _)) hlw32) h1)
        (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hA) hP0)) (mul_nonneg h2 h3)
    by_cases hw1 : ‖w‖ ≤ 1 / 16
    · refine (key w hw0 hw1).trans ?_
      have hy : ‖z0 - w‖ ≤ 3 * r := by have := norm_sub_le z0 w; linarith
      have hLf : |Lf d 0 (r / 8) (z0 - w)| ≤
          (c0 * (16 : ℝ) ^ ((d : ℝ) - 2) * lw (1 / 32 : ℝ) ^ ε) * r ^ (-((d : ℝ) - 2)) * lw ‖w‖ ^ ε := by
        by_cases hc : ‖z0 - w‖ ≤ r / 16
        · rw [Lf_zero_eq_zero hρ (by linarith)]
          rw [abs_zero]
          have h1 : 0 ≤ r ^ (-((d : ℝ) - 2)) := Real.rpow_nonneg hr.le _
          have : 0 ≤ lw ‖w‖ ^ ε := pow_nonneg (lw_pos _).le _
          exact mul_nonneg (mul_nonneg (mul_nonneg hc0 (Real.rpow_nonneg (by norm_num) _)) hlw32) h1 |> fun h' => mul_nonneg h' this
        · have hc' : r / 16 < ‖z0 - w‖ := not_le.mp hc
          have hy0 : z0 - w ≠ 0 := norm_pos_iff.mp (lt_trans (by positivity) hc')
          refine (Lf_zero_abs_le _).trans ((hE _ hy0).trans ?_)
          have e1 : ‖z0 - w‖ ^ (-((d : ℝ) - 2)) ≤ (16 : ℝ) ^ ((d : ℝ) - 2) * r ^ (-((d : ℝ) - 2)) := by
            have h3 : ‖z0 - w‖ ^ (-((d : ℝ) - 2)) ≤ (r / 16) ^ (-((d : ℝ) - 2)) :=
              Real.rpow_le_rpow_of_nonpos (by positivity) hc'.le (by linarith)
            refine h3.trans (le_of_eq ?_)
            rw [show r / 16 = (1 / 16 : ℝ) * r by ring, Real.mul_rpow (by norm_num) hr.le,
              Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 1 / 16)]
            rw [one_div, Real.inv_rpow (by norm_num), inv_inv]
          have e2 : lw ‖z0 - w‖ ≤ lw (1 / 32 : ℝ) * lw ‖w‖ := by
            calc lw ‖z0 - w‖ ≤ lw (r / 16) := lw_anti (by positivity) hc'.le (by linarith)
              _ = lw (2 * r * (1 / 32)) := by congr 1; ring
              _ ≤ lw (2 * r) * lw (1 / 32) := lw_mul_le (by positivity) (by norm_num)
              _ ≤ lw ‖w‖ * lw (1 / 32) :=
                mul_le_mul_of_nonneg_right (lw_anti hwpos hw2.le (by linarith)) (lw_pos _).le
              _ = _ := by ring
          have e3 : lw ‖z0 - w‖ ^ ε ≤ lw (1 / 32 : ℝ) ^ ε * lw ‖w‖ ^ ε := by
            rw [← mul_pow]; exact pow_le_pow_left₀ (lw_pos _).le e2 ε
          have hp1 : 0 ≤ ‖z0 - w‖ ^ (-((d : ℝ) - 2)) := Real.rpow_nonneg (norm_nonneg _) _
          calc c0 * (‖z0 - w‖ ^ (-((d : ℝ) - 2)) * lw ‖z0 - w‖ ^ ε)
              ≤ c0 * (((16 : ℝ) ^ ((d : ℝ) - 2) * r ^ (-((d : ℝ) - 2))) * (lw (1 / 32 : ℝ) ^ ε * lw ‖w‖ ^ ε)) :=
                mul_le_mul_of_nonneg_left (mul_le_mul e1 e3 (pow_nonneg (lw_pos _).le _)
                  (mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.rpow_nonneg hr.le _))) hc0
            _ = _ := by ring
      calc |Lf d 0 (r / 8) (z0 - w)| * (2 * A * (‖w‖ ^ (-σ) * lw ‖w‖ ^ b)) * ((∏ i, ‖u i‖) * ∏ j, ‖v j‖)
          ≤ ((c0 * (16 : ℝ) ^ ((d : ℝ) - 2) * lw (1 / 32 : ℝ) ^ ε) * r ^ (-((d : ℝ) - 2)) * lw ‖w‖ ^ ε) *
              (2 * A * (‖w‖ ^ (-σ) * lw ‖w‖ ^ b)) * ((∏ i, ‖u i‖) * ∏ j, ‖v j‖) := by
            refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hLf ?_) hP0
            exact mul_nonneg (mul_nonneg (by norm_num) hA)
              (mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (pow_nonneg (lw_pos _).le b))
        _ = _ := by rw [pow_add]; ring
    · rw [farPsi_zero_of_gt h hρ 0 hac X0 z0 u v (not_le.mp hw1), abs_zero]
      exact hnn
  · filter_upwards [hae0] with w hw0 hw2 hw3
    rw [Real.norm_eq_abs]
    have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hw0
    refine (key w hw0 hw3.le).trans ?_
    have hyl : ‖w‖ / 2 ≤ ‖z0 - w‖ := by
      have := norm_sub_norm_le w z0
      rw [norm_sub_rev] at this
      linarith
    have hyu : ‖z0 - w‖ ≤ 2 * ‖w‖ := by have := norm_sub_le z0 w; linarith
    have hy0 : z0 - w ≠ 0 := norm_pos_iff.mp (by linarith)
    have hLf : |Lf d 0 (r / 8) (z0 - w)| ≤
        (c0 * (2 : ℝ) ^ ((d : ℝ) - 2) * 2 ^ ε) * (‖w‖ ^ (-((d : ℝ) - 2)) * lw ‖w‖ ^ ε) := by
      refine (Lf_zero_abs_le _).trans ((hE _ hy0).trans ?_)
      have e1 : ‖z0 - w‖ ^ (-((d : ℝ) - 2)) ≤ (2 : ℝ) ^ ((d : ℝ) - 2) * ‖w‖ ^ (-((d : ℝ) - 2)) := by
        have h3 : ‖z0 - w‖ ^ (-((d : ℝ) - 2)) ≤ (‖w‖ / 2) ^ (-((d : ℝ) - 2)) :=
          Real.rpow_le_rpow_of_nonpos (by positivity) hyl (by linarith)
        refine h3.trans (le_of_eq ?_)
        rw [Real.div_rpow hwpos.le (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
        rw [div_inv_eq_mul]; ring
      have e3 : lw ‖z0 - w‖ ^ ε ≤ 2 ^ ε * lw ‖w‖ ^ ε := by
        rw [← mul_pow]; exact pow_le_pow_left₀ (lw_pos _).le (lw_le_two_mul hwpos hyl hyu) ε
      calc c0 * (‖z0 - w‖ ^ (-((d : ℝ) - 2)) * lw ‖z0 - w‖ ^ ε)
          ≤ c0 * (((2 : ℝ) ^ ((d : ℝ) - 2) * ‖w‖ ^ (-((d : ℝ) - 2))) * (2 ^ ε * lw ‖w‖ ^ ε)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul e1 e3 (pow_nonneg (lw_pos _).le _)
              (mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.rpow_nonneg (norm_nonneg _) _))) hc0
        _ = _ := by ring
    have hexp : ‖w‖ ^ (-((d : ℝ) - 2)) * ‖w‖ ^ (-σ) = ‖w‖ ^ (-(σ + ((d : ℝ) - 2))) := by
      rw [← Real.rpow_add hwpos]; congr 1; ring
    calc |Lf d 0 (r / 8) (z0 - w)| * (2 * A * (‖w‖ ^ (-σ) * lw ‖w‖ ^ b)) * ((∏ i, ‖u i‖) * ∏ j, ‖v j‖)
        ≤ ((c0 * (2 : ℝ) ^ ((d : ℝ) - 2) * 2 ^ ε) * (‖w‖ ^ (-((d : ℝ) - 2)) * lw ‖w‖ ^ ε)) *
            (2 * A * (‖w‖ ^ (-σ) * lw ‖w‖ ^ b)) * ((∏ i, ‖u i‖) * ∏ j, ‖v j‖) := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hLf ?_) hP0
          exact mul_nonneg (mul_nonneg (by norm_num) hA)
            (mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (pow_nonneg (lw_pos _).le b))
      _ = (c0 * (2 : ℝ) ^ ((d : ℝ) - 2) * 2 ^ ε * (2 * A * ((∏ i, ‖u i‖) * ∏ j, ‖v j‖))) *
          ((‖w‖ ^ (-((d : ℝ) - 2)) * ‖w‖ ^ (-σ)) * lw ‖w‖ ^ (b + ε)) := by rw [pow_add]; ring
      _ = _ := by rw [hexp]
  · filter_upwards [hae16] with w hw hw1
    exact farPsi_zero_of_gt h hρ 0 hac X0 z0 u v (lt_of_le_of_ne hw1 (Ne.symm hw))

lemma newtonPot_pat_eq0 (hd : 2 ≤ d) {σ : ℝ} (hσ : σ < d) {b m : ℕ} {A : ℝ} (hA : 0 ≤ A)
    {g : Euc d × Euc d → ℝ} (h : SrcCls d σ b m A g) {a c : ℕ} (hac : a + c ≤ m)
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1 / 8) (X0 z0 : Euc d) (hz0 : ‖z0‖ = r)
    (u : Fin a → Euc d) (v : Fin c → Euc d) :
    iteratedFDeriv ℝ (a + c) (newtonPot d g) (X0, z0) (pat u v) =
      (∫ x, Ln d 0 (r / 8) x * iteratedFDeriv ℝ (a + c) g (X0, z0 - x) (pat u v)) +
        ∫ w, farPsi d g 0 (r / 8) X0 z0 u v w := by
  obtain ⟨hs, hform, hint⟩ := newtonPot_FL hd hσ hA h hr hr1 hz0 0
  have hU : IsOpen {p : Euc d × Euc d | ‖p.2 - z0‖ < r / 16} := isOpen_near z0 _
  have hp0 : ((X0, z0) : Euc d × Euc d) ∈ {p : Euc d × Euc d | ‖p.2 - z0‖ < r / 16} := by
    show ‖z0 - z0‖ < r / 16
    simp; positivity
  have e : newtonPot d g = fun p : Euc d × Euc d => newtonPot d g p - 0 * ∫ w, g (p.1, w) := by
    funext p; simp
  conv_lhs => rw [e]
  obtain ⟨hi1, hi2⟩ := hint (a + c) hac (X0, z0) hp0
  rw [hform (a + c) hac (X0, z0) hp0, ContinuousMultilinearMap.add_apply,
    eval_integral hi1, eval_integral hi2]
  rfl

lemma wl_aux (hd : 2 ≤ d) {σ : ℝ} (hσ : σ < d) (b : ℕ) :
    ∃ C3 : ℝ, 0 ≤ C3 ∧ ∀ r : ℝ, 0 < r → r < 1 / 8 →
      (r ^ (-(σ - 2)) * lw r ^ (b + if d = 2 then 1 else 0) ≤
        C3 * (1 + r ^ (-(σ - 2)) * lw r ^ (b + if σ - 2 = 0 then 1 else 0))) ∧
      (r ^ (-(σ - 2)) * lw r ^ ((b + if d = 2 then 1 else 0) + if -(σ - 2) = 0 then 1 else 0) ≤
        C3 * (1 + r ^ (-(σ - 2)) * lw r ^ (b + if σ - 2 = 0 then 1 else 0))) := by
  by_cases hd2 : d = 2
  · subst hd2
    have hσ2 : σ < 2 := by exact_mod_cast hσ
    obtain ⟨C, hC0, hC⟩ := rpow_log_pow_le (-(σ - 2)) (by linarith) (b + 1)
    refine ⟨C, hC0, fun r hr hr1 => ?_⟩
    have hne : ¬ (-(σ - 2) = 0) := by intro h0; linarith
    have hne' : ¬ (σ - 2 = 0) := by intro h0; linarith
    have hT : 0 ≤ r ^ (-(σ - 2)) * lw r ^ b :=
      mul_nonneg (Real.rpow_nonneg hr.le _) (pow_nonneg (lw_pos _).le _)
    have h1 := hC r hr (by linarith)
    have h1' : r ^ (-(σ - 2)) * lw r ^ (b + 1) ≤ C := h1
    simp only [if_true, if_neg hne, if_neg hne', add_zero]
    refine ⟨h1'.trans ?_, h1'.trans ?_⟩ <;> nlinarith [mul_nonneg hC0 hT]
  · refine ⟨1, zero_le_one, fun r hr hr1 => ?_⟩
    have hif : (-(σ - 2) = 0) ↔ (σ - 2 = 0) := neg_eq_zero
    simp only [hd2, if_false, add_zero, hif, one_mul]
    have hW0 : 0 ≤ r ^ (-(σ - 2)) := Real.rpow_nonneg hr.le _
    have : r ^ (-(σ - 2)) * lw r ^ b ≤ r ^ (-(σ - 2)) * lw r ^ (b + if σ - 2 = 0 then 1 else 0) :=
      mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (one_le_lw r) (by split_ifs <;> omega)) hW0
    exact ⟨by linarith, by linarith⟩

set_option maxHeartbeats 1600000 in
/-- Base estimate (`c = 0`, `0 ≤ σ < d`). -/
lemma base_zero (hd : 2 ≤ d) {σ : ℝ} (hσ0 : 0 ≤ σ) (hσ : σ < d) (b m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {g : Euc d × Euc d → ℝ} {A : ℝ} (_h : SrcCls d σ b m A g), 0 ≤ A →
      ∀ {a : ℕ}, a + 0 ≤ m → ∀ {r : ℝ}, 0 < r → r < 1 / 8 → ∀ (X0 z0 : Euc d), ‖z0‖ = r →
      ∀ (u : Fin a → Euc d) (v : Fin 0 → Euc d),
      |iteratedFDeriv ℝ (a + 0) (newtonPot d g) (X0, z0) (pat u v)| ≤
        C * A * (1 + r ^ (-(σ - 2)) * lw r ^ (b + if σ - 2 = 0 then 1 else 0)) *
          ((∏ i, ‖u i‖) * ∏ j, ‖v j‖) := by
  obtain ⟨Cn, hCn0, hCn⟩ := SrcCls.near_val_zero (d := d) (σ := σ) (b := b) (m := m) hd hσ0
  obtain ⟨K1, K2, hK10, hK20, hKK⟩ := far_pointwise_zero hd hσ0 b m
  set ε : ℕ := if d = 2 then 1 else 0 with hε
  obtain ⟨C1, C2, hC10, hC20, hfe⟩ := far_estimate hd hσ (σ + ((d : ℝ) - 2)) (b + ε)
  obtain ⟨C3, hC30, hC3⟩ := wl_aux hd hσ b
  refine ⟨Cn * C3 + 2 * C1 * K1 * C3 + 2 * C2 * K2 * (1 + C3), by positivity,
    fun {g} {A} h hA a hac r hr hr1 X0 z0 hz0 u v => ?_⟩
  set P : ℝ := (∏ i, ‖u i‖) * ∏ j, ‖v j‖ with hP
  have hP0 : 0 ≤ P :=
    mul_nonneg (Finset.prod_nonneg fun i _ => norm_nonneg _) (Finset.prod_nonneg fun i _ => norm_nonneg _)
  rw [newtonPot_pat_eq0 hd hσ hA h hac hr hr1 X0 z0 hz0 u v]
  have hnear := hCn h hA hac hr hr1 X0 z0 hz0 u v
  obtain ⟨hp1, hp2, hp3⟩ := hKK h hA hac hr hr1 X0 z0 hz0 u v
  have hint : Integrable (fun w => farPsi d g 0 (r / 8) X0 z0 u v w) := by
    obtain ⟨-, -, hi⟩ := newtonPot_FL hd hσ hA h hr hr1 hz0 0
    have hp0 : ((X0, z0) : Euc d × Euc d) ∈ {p : Euc d × Euc d | ‖p.2 - z0‖ < r / 16} := by
      show ‖z0 - z0‖ < r / 16
      simp; positivity
    exact integrable_eval (hi (a + 0) hac (X0, z0) hp0).2 (pat u v)
  set M1 : ℝ := K1 * r ^ (-((d : ℝ) - 2)) * (2 * A * P) with hM1
  set M2 : ℝ := K2 * (2 * A * P) with hM2
  have hM10 : 0 ≤ M1 := mul_nonneg (mul_nonneg hK10 (Real.rpow_nonneg hr.le _))
    (mul_nonneg (mul_nonneg (by norm_num) hA) hP0)
  have hM20 : 0 ≤ M2 := mul_nonneg hK20 (mul_nonneg (mul_nonneg (by norm_num) hA) hP0)
  have hfar := hfe r M1 M2 hr hr1 hM10 hM20 _ hint hp1 hp2 hp3
  set W : ℝ := r ^ (-(σ - 2)) with hW
  have hW0 : 0 ≤ W := Real.rpow_nonneg hr.le _
  have hexp1 : r ^ (-(σ + ((0 : ℕ) : ℝ))) * r ^ (2 : ℝ) = W := by
    rw [← Real.rpow_add hr]; congr 1; push_cast; ring
  have hexp2 : r ^ (-((d : ℝ) - 2)) * r ^ ((d : ℝ) - σ) = W := by
    rw [← Real.rpow_add hr]; congr 1; ring
  have hexp3 : (d : ℝ) - (σ + ((d : ℝ) - 2)) = -(σ - 2) := by ring
  rw [hexp3] at hfar
  obtain ⟨hw1, hw2⟩ := hC3 r hr hr1
  set T : ℝ := 1 + W * lw r ^ (b + if σ - 2 = 0 then 1 else 0) with hT
  have hT1 : 1 ≤ T := by
    have : 0 ≤ W * lw r ^ (b + if σ - 2 = 0 then 1 else 0) :=
      mul_nonneg hW0 (pow_nonneg (lw_pos _).le _)
    linarith
  have hX : 0 ≤ A * P := mul_nonneg hA hP0
  have t1 : Cn * A * (r ^ (-(σ + ((0 : ℕ) : ℝ))) * lw r ^ b) * (r ^ (2 : ℝ) * lw r ^ (if d = 2 then 1 else 0)) * P =
      (Cn * (A * P)) * (W * lw r ^ (b + ε)) := by
    calc _ = Cn * (A * P) * ((r ^ (-(σ + ((0 : ℕ) : ℝ))) * r ^ (2 : ℝ)) * (lw r ^ b * lw r ^ ε)) := by
          rw [hε]; ring
      _ = _ := by rw [hexp1, pow_add]
  have t2 : C1 * M1 * (r ^ ((d : ℝ) - σ) * lw r ^ (b + ε)) = (2 * C1 * K1 * (A * P)) * (W * lw r ^ (b + ε)) := by
    calc _ = 2 * C1 * K1 * (A * P) * ((r ^ (-((d : ℝ) - 2)) * r ^ ((d : ℝ) - σ)) * lw r ^ (b + ε)) := by
          rw [hM1]; ring
      _ = _ := by rw [hexp2]
  have t3 : C2 * M2 * (1 + W * lw r ^ ((b + ε) + if -(σ - 2) = 0 then 1 else 0)) =
      (2 * C2 * K2 * (A * P)) * (1 + W * lw r ^ ((b + ε) + if -(σ - 2) = 0 then 1 else 0)) := by
    rw [hM2]; ring
  have hsum : |(∫ x, Ln d 0 (r / 8) x * iteratedFDeriv ℝ (a + 0) g (X0, z0 - x) (pat u v)) +
      ∫ w, farPsi d g 0 (r / 8) X0 z0 u v w| ≤
      (Cn * (A * P)) * (W * lw r ^ (b + ε)) + ((2 * C1 * K1 * (A * P)) * (W * lw r ^ (b + ε)) +
        (2 * C2 * K2 * (A * P)) * (1 + W * lw r ^ ((b + ε) + if -(σ - 2) = 0 then 1 else 0))) := by
    refine (abs_add_le _ _).trans ?_
    have e1 := hnear.trans_eq t1
    have e2 : |∫ w, farPsi d g 0 (r / 8) X0 z0 u v w| ≤
        (2 * C1 * K1 * (A * P)) * (W * lw r ^ (b + ε)) +
          (2 * C2 * K2 * (A * P)) * (1 + W * lw r ^ ((b + ε) + if -(σ - 2) = 0 then 1 else 0)) := by
      rw [← Real.norm_eq_abs]
      refine hfar.trans_eq ?_
      rw [← t2, ← t3]
    linarith
  refine hsum.trans ?_
  have a1 : (Cn * (A * P)) * (W * lw r ^ (b + ε)) ≤ (Cn * (A * P)) * (C3 * T) :=
    mul_le_mul_of_nonneg_left hw1 (mul_nonneg hCn0 hX)
  have a2 : (2 * C1 * K1 * (A * P)) * (W * lw r ^ (b + ε)) ≤ (2 * C1 * K1 * (A * P)) * (C3 * T) :=
    mul_le_mul_of_nonneg_left hw1 (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hC10) hK10) hX)
  have a3 : (2 * C2 * K2 * (A * P)) * (1 + W * lw r ^ ((b + ε) + if -(σ - 2) = 0 then 1 else 0)) ≤
      (2 * C2 * K2 * (A * P)) * ((1 + C3) * T) := by
    refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hC20) hK20) hX)
    nlinarith [hw2, hT1, hC30]
  calc _ ≤ (Cn * (A * P)) * (C3 * T) + ((2 * C1 * K1 * (A * P)) * (C3 * T) +
        (2 * C2 * K2 * (A * P)) * ((1 + C3) * T)) := by linarith
    _ = _ := by ring

end HRS.Parx

end
