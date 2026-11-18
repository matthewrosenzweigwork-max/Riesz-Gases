import HRS.Equilibrium.Parametrix.PX4aAuxC

/-!
# Packet PX4a auxiliaries D: moving a derivative onto the source; the potential bound for all `σ < d`

`kPot_dirD`: `∂_z ∫ k(z-w) g(X,w) dw = ∫ k(z-w) ∂_w g(X,w) dw` for `σ < d - 1` (singular integration by
parts on the far kernel, `ibp_sing`), the induction `kpot_bound` over the `z`-derivative order.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.Parx

variable {d : ℕ}

local notation "∞'" => ((⊤ : ℕ∞) : WithTop ℕ∞)

section Dir

variable {s : ℝ} {k : Euc d → ℝ}

lemma kPot_contDiffOn (hd : 1 ≤ d) (hk : LocKer d s k) {σ : ℝ} (hσ : σ < d) {b m : ℕ} {A : ℝ}
    (hA : 0 ≤ A) {g : Euc d × Euc d → ℝ} (h : SrcCls d σ b m A g) :
    ContDiffOn ℝ (m : WithTop ℕ∞) (kPot d k g)
      {p : Euc d × Euc d | 0 < ‖p.2‖ ∧ ‖p.2‖ < 1 / 8} := by
  intro p hp
  obtain ⟨hp1, hp2⟩ := hp
  have hs := (kPot_FL hd hk hσ hA h hp1 hp2 (z0 := p.2) rfl).1
  have hU : IsOpen {q : Euc d × Euc d | ‖q.2 - p.2‖ < ‖p.2‖ / 16} := isOpen_near p.2 _
  have hp0 : p ∈ {q : Euc d × Euc d | ‖q.2 - p.2‖ < ‖p.2‖ / 16} := by
    show ‖p.2 - p.2‖ < ‖p.2‖ / 16
    rw [sub_self, norm_zero]; linarith
  exact (hs.contDiffAt (hU.mem_nhds hp0)).contDiffWithinAt

set_option maxHeartbeats 1600000 in
lemma kPot_dirD (hd : 2 ≤ d) (hk : LocKer d s k) {σ : ℝ} (hσ : σ < (d : ℝ) - 1) {b m : ℕ} {A : ℝ}
    (hA : 0 ≤ A) {g : Euc d × Euc d → ℝ} (h : SrcCls d σ b (m + 1) A g) {r : ℝ} (hr : 0 < r)
    (hr1 : r < 1 / 8) (X z : Euc d) (hz : ‖z‖ = r) (e : Euc d) :
    dirD ((0 : Euc d), e) (kPot d k g) (X, z) = kPot d k (dirD ((0 : Euc d), e) g) (X, z) := by
  have hσd : σ < d := by linarith
  have h' := h.dirD_snd hA e
  have hρ : 0 < r / 8 := by positivity
  have hd1 : 1 ≤ d := by omega
  obtain ⟨-, -, hs⟩ := kPot_split hd1 hk (σ := σ + 1) (by linarith) (mul_nonneg hA (norm_nonneg e)) h'
    hr hr1 hz (p := (X, z)) (by simp; positivity)
  have hL := kpot_pat_eq hd1 hk hσd hA h (a := 0) (c := 1) (by omega) hr hr1 X z hz
    Fin.elim0 (fun _ => e)
  rw [iteratedFDeriv_one_pat] at hL
  simp only [iteratedFDeriv_one_pat] at hL
  rw [hL, hs]
  congr 1
  -- far parts
  obtain ⟨C, hC0, hC⟩ := (hk.kF_hasCompactSupport (r / 8)).exists_bound_iteratedFDeriv
    (hk.kF_contDiff hρ (⊤ : ℕ∞)) 1
  set φ : Euc d → ℝ := fun w => kF k (r / 8) (z - w) with hφ
  have hLf1 : ContDiff ℝ 1 (kF k (r / 8)) := by exact_mod_cast hk.kF_contDiff hρ 1
  have hφ1 : ContDiff ℝ 1 φ := hLf1.comp (contDiff_const.sub contDiff_id)
  have hφd : ∀ w, HasFDerivAt φ ((fderiv ℝ (kF k (r / 8)) (z - w)).comp
      (-(ContinuousLinearMap.id ℝ (Euc d)))) w := by
    intro w
    have h1 : HasFDerivAt (fun w : Euc d => z - w) (-(ContinuousLinearMap.id ℝ (Euc d))) w :=
      (hasFDerivAt_id w).const_sub z
    exact ((hLf1.differentiable (by simp)) (z - w)).hasFDerivAt.comp w h1
  have hM : ∀ y, ‖φ y‖ ≤ C := fun y => by
    have := hC 0 (by norm_num) (z - y)
    rwa [norm_iteratedFDeriv_zero] at this
  have hM' : ∀ y, ‖fderiv ℝ φ y‖ ≤ C := fun y => by
    rw [(hφd y).fderiv]
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    have h1 := hC 1 le_rfl (z - y)
    rw [norm_iteratedFDeriv_one] at h1
    have h2 : ‖-(ContinuousLinearMap.id ℝ (Euc d))‖ ≤ 1 := by
      rw [norm_neg]; exact ContinuousLinearMap.norm_id_le
    calc _ ≤ C * 1 := mul_le_mul h1 h2 (norm_nonneg _) hC0
      _ = C := mul_one C
  have hibp := ibp_sing hd hσ hA h X e hφ1 hM hM'
  have hfd : ∀ w, fderiv ℝ φ w e = -(fderiv ℝ (kF k (r / 8)) (z - w) e) := fun w => by
    rw [(hφd w).fderiv]; simp
  simp only [hfd] at hibp
  have hae := ae_ne_zero_euc (d := d) hd1
  have e1 : ∫ w, farKPsi d g k (r / 8) X z Fin.elim0 (fun _ : Fin 1 => e) w =
      ∫ w, fderiv ℝ (kF k (r / 8)) (z - w) e * g (X, w) := by
    refine integral_congr_ae ?_
    filter_upwards [hae] with w hw0
    rw [farKPsi_eq hk h hρ (by omega) X z Fin.elim0 (fun _ => e) hw0]
    simp [iteratedFDeriv_one_apply, iteratedFDeriv_zero_apply]
  rw [e1]
  simp only [neg_mul, integral_neg, neg_neg] at hibp
  exact hibp.symm

set_option maxHeartbeats 1600000 in
/-- The potential bound for all `σ < d` (logarithm power `b + 1`). -/
theorem kpot_bound (hd : 2 ≤ d) (hk : LocKer d s k) : ∀ (c : ℕ) {σ : ℝ}, σ < d → ∀ (b m : ℕ),
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {g : Euc d × Euc d → ℝ} {A : ℝ} (_h : SrcCls d σ b m A g), 0 ≤ A →
      ∀ {a : ℕ}, a + c ≤ m → ∀ {r : ℝ}, 0 < r → r < 1 / 8 → ∀ (X0 z0 : Euc d), ‖z0‖ = r →
      ∀ (u : Fin a → Euc d) (v : Fin c → Euc d),
      |iteratedFDeriv ℝ (a + c) (kPot d k g) (X0, z0) (pat u v)| ≤
        C * A * (1 + r ^ (-(σ + s - d + c)) * lw r ^ (b + 1)) *
          ((∏ i, ‖u i‖) * ∏ j, ‖v j‖) := by
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hd1 : 1 ≤ d := by omega
  intro c
  induction c with
  | zero =>
    intro σ hσ b m
    by_cases hσ0 : 0 ≤ σ
    · obtain ⟨C, hC0, hC⟩ := kpot_base hd hk hσ0 hσ b m 0
      exact ⟨C, hC0, fun {g} {A} h hA a hac r hr hr1 X0 z0 hz0 u v => hC h hA hac hr hr1 X0 z0 hz0 u v⟩
    · push_neg at hσ0
      obtain ⟨C0, hC00, hC0⟩ := kpot_base hd hk (le_refl (0 : ℝ)) (by linarith) b m 0
      obtain ⟨K, hK0, hK⟩ := exists_const_rpow_lw (b + 1) (e := (d : ℝ) - s) (by linarith [hk.s_lt])
      refine ⟨C0 * (1 + K), by positivity, fun {g} {A} h hA a hac r hr hr1 X0 z0 hz0 u v => ?_⟩
      have h0 := h.mono_sigma hA hσ0.le
      have := hC0 h0 hA hac hr hr1 X0 z0 hz0 u v
      refine this.trans ?_
      have hP0 : 0 ≤ (∏ i, ‖u i‖) * ∏ j, ‖v j‖ :=
        mul_nonneg (Finset.prod_nonneg fun i _ => norm_nonneg _) (Finset.prod_nonneg fun i _ => norm_nonneg _)
      have hW0 : 0 ≤ r ^ (-(σ + s - d + ((0 : ℕ) : ℝ))) * lw r ^ (b + 1) :=
        mul_nonneg (Real.rpow_nonneg hr.le _) (pow_nonneg (lw_pos _).le _)
      have e1 : -((0 : ℝ) + s - d + ((0 : ℕ) : ℝ)) = (d : ℝ) - s := by push_cast; ring
      rw [e1]
      have h1 := hK r hr hr1
      have h2 : (1 : ℝ) + r ^ ((d : ℝ) - s) * lw r ^ (b + 1) ≤
          (1 + K) * (1 + r ^ (-(σ + s - d + ((0 : ℕ) : ℝ))) * lw r ^ (b + 1)) := by
        nlinarith
      have h3 : 0 ≤ C0 * A := mul_nonneg hC00 hA
      calc C0 * A * (1 + r ^ ((d : ℝ) - s) * lw r ^ (b + 1)) * ((∏ i, ‖u i‖) * ∏ j, ‖v j‖)
          ≤ C0 * A * ((1 + K) * (1 + r ^ (-(σ + s - d + ((0 : ℕ) : ℝ))) * lw r ^ (b + 1))) *
            ((∏ i, ‖u i‖) * ∏ j, ‖v j‖) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 h3) hP0
        _ = _ := by ring
  | succ c ih =>
    intro σ hσ b m
    rcases m with _ | m'
    · exact ⟨0, le_rfl, fun {g} {A} h hA a hac => by omega⟩
    by_cases hσ0 : 0 ≤ σ
    · obtain ⟨C, hC0, hC⟩ := kpot_base hd hk hσ0 hσ b (m' + 1) (c + 1)
      exact ⟨C, hC0, fun {g} {A} h hA a hac r hr hr1 X0 z0 hz0 u v => hC h hA hac hr hr1 X0 z0 hz0 u v⟩
    · push_neg at hσ0
      obtain ⟨C', hC'0, hC'⟩ := ih (σ := σ + 1) (by linarith) b m'
      refine ⟨C', hC'0, fun {g} {A} h hA a hac r hr hr1 X0 z0 hz0 u v => ?_⟩
      set e : Euc d := v (Fin.last c) with he
      set v' : Fin c → Euc d := Fin.init v with hv'
      have hv : v = Fin.snoc v' e := (Fin.snoc_init_self v).symm
      have h' := h.dirD_snd hA e
      have hpat : pat u v = (Fin.snoc (pat u v') ((0 : Euc d), e) : Fin (a + c + 1) → Euc d × Euc d) := by
        conv_lhs => rw [hv]
        exact pat_snoc_right u v' e
      have hU : IsOpen {p : Euc d × Euc d | 0 < ‖p.2‖ ∧ ‖p.2‖ < 1 / 8} :=
        (isOpen_lt continuous_const (continuous_norm.comp continuous_snd)).inter
          (isOpen_lt (continuous_norm.comp continuous_snd) continuous_const)
      have hq : ((X0, z0) : Euc d × Euc d) ∈ {p : Euc d × Euc d | 0 < ‖p.2‖ ∧ ‖p.2‖ < 1 / 8} :=
        ⟨by simpa [hz0] using hr, by simpa [hz0] using hr1⟩
      have hcd := kPot_contDiffOn hd1 hk (by linarith) hA h
      have hcdat : ContDiffAt ℝ ((a + c + 1 : ℕ) : WithTop ℕ∞) (kPot d k g) (X0, z0) :=
        (hcd.contDiffAt (hU.mem_nhds hq)).of_le (by exact_mod_cast (by omega : a + c + 1 ≤ m' + 1))
      have heq : dirD ((0 : Euc d), e) (kPot d k g) =ᶠ[𝓝 (X0, z0)] kPot d k (dirD ((0 : Euc d), e) g) := by
        filter_upwards [hU.mem_nhds hq] with p hp
        exact kPot_dirD hd hk (by linarith) hA h hp.1 (by linarith [hp.2]) p.1 p.2 rfl e
      have hstep : iteratedFDeriv ℝ (a + (c + 1)) (kPot d k g) (X0, z0) (pat u v) =
          iteratedFDeriv ℝ (a + c) (dirD ((0 : Euc d), e) (kPot d k g)) (X0, z0) (pat u v') := by
        rw [hpat]; exact (iteratedFDeriv_dirD hcdat ((0 : Euc d), e) (pat u v')).symm
      rw [hstep, (heq.iteratedFDeriv ℝ (a + c)).eq_of_nhds]
      have key := hC' h' (mul_nonneg hA (norm_nonneg e)) (a := a) (by omega) hr hr1 X0 z0 hz0 u v'
      have hexpo : σ + 1 + s - d + (c : ℝ) = σ + s - d + ((c + 1 : ℕ) : ℝ) := by push_cast; ring
      rw [hexpo] at key
      refine key.trans (le_of_eq ?_)
      rw [prod_norm_init v]
      simp only [hv', he]
      ring

end Dir

end HRS.Parx

end
