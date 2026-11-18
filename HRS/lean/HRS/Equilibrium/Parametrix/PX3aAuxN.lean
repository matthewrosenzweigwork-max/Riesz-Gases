import HRS.Equilibrium.Parametrix.PX3aAuxM

/-!
# Packet PX3a auxiliaries N: the Newton potential bound for all `σ < d`
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.Parx

variable {d : ℕ}

local notation "∞'" => ((⊤ : ℕ∞) : WithTop ℕ∞)

lemma newtonPot_contDiffOn (hd : 2 ≤ d) {σ : ℝ} (hσ : σ < d) {b m : ℕ} {A : ℝ} (hA : 0 ≤ A)
    {g : Euc d × Euc d → ℝ} (h : SrcCls d σ b m A g) :
    ContDiffOn ℝ (m : WithTop ℕ∞) (newtonPot d g)
      {p : Euc d × Euc d | 0 < ‖p.2‖ ∧ ‖p.2‖ < 1 / 8} := by
  intro p hp
  obtain ⟨hp1, hp2⟩ := hp
  have hs := (newtonPot_FL hd hσ hA h hp1 hp2 (z0 := p.2) rfl 0).1
  have hU : IsOpen {q : Euc d × Euc d | ‖q.2 - p.2‖ < ‖p.2‖ / 16} := isOpen_near p.2 _
  have hp0 : p ∈ {q : Euc d × Euc d | ‖q.2 - p.2‖ < ‖p.2‖ / 16} := by
    show ‖p.2 - p.2‖ < ‖p.2‖ / 16
    rw [sub_self, norm_zero]; linarith
  have h2 : ContDiffAt ℝ (m : WithTop ℕ∞) (newtonPot d g) p := by
    have h3 := hs.contDiffAt (hU.mem_nhds hp0)
    refine h3.congr_of_eventuallyEq ?_
    exact Eventually.of_forall fun q => by simp
  exact h2.contDiffWithinAt

lemma exists_const_rpow_lw (b : ℕ) {e : ℝ} (he : 0 < e) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ r : ℝ, 0 < r → r < 1 / 8 → r ^ e * lw r ^ b ≤ K := by
  obtain ⟨C, hC0, hC⟩ := rpow_log_pow_le e he b
  exact ⟨C, hC0, fun r hr hr1 => hC r hr (by linarith)⟩

set_option maxHeartbeats 1600000 in
/-- The Newton potential bound for all `σ < d` (no symmetry). -/
theorem newtonPot_bound (hd : 2 ≤ d) : ∀ (c : ℕ) {σ : ℝ}, σ < d → ∀ (b m : ℕ),
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {g : Euc d × Euc d → ℝ} {A : ℝ} (_h : SrcCls d σ b m A g), 0 ≤ A →
      ∀ {a : ℕ}, a + c ≤ m → ∀ {r : ℝ}, 0 < r → r < 1 / 8 → ∀ (X0 z0 : Euc d), ‖z0‖ = r →
      ∀ (u : Fin a → Euc d) (v : Fin c → Euc d),
      |iteratedFDeriv ℝ (a + c) (newtonPot d g) (X0, z0) (pat u v)| ≤
        C * A * (1 + r ^ (-(σ - 2 + c)) * lw r ^ (b + if σ - 2 + (c : ℝ) = 0 then 1 else 0)) *
          ((∏ i, ‖u i‖) * ∏ j, ‖v j‖) := by
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  intro c
  induction c with
  | zero =>
    intro σ hσ b m
    by_cases hσ0 : 0 ≤ σ
    · obtain ⟨C, hC0, hC⟩ := base_zero hd hσ0 hσ b m
      refine ⟨C, hC0, fun {g} {A} h hA a hac r hr hr1 X0 z0 hz0 u v => ?_⟩
      have := hC h hA hac hr hr1 X0 z0 hz0 u v
      simpa using this
    · push_neg at hσ0
      obtain ⟨C0, hC00, hC0⟩ := base_zero hd (le_refl (0 : ℝ)) (by linarith) b m
      obtain ⟨K, hK0, hK⟩ := exists_const_rpow_lw b (e := 2) (by norm_num)
      refine ⟨C0 * (1 + K), by positivity, fun {g} {A} h hA a hac r hr hr1 X0 z0 hz0 u v => ?_⟩
      have h0 := h.mono_sigma hA hσ0.le
      have := hC0 h0 hA hac hr hr1 X0 z0 hz0 u v
      refine this.trans ?_
      have hne : ¬ ((0 : ℝ) - 2 = 0) := by norm_num
      have hne' : ¬ (σ - 2 + ((0 : ℕ) : ℝ) = 0) := by push_cast; intro h0; linarith
      have hne'' : ¬ (σ - 2 = 0) := by intro h0; linarith
      simp only [hne, hne', hne'', if_false, add_zero, Nat.cast_zero]
      have e2 : -((0 : ℝ) - 2) = 2 := by norm_num
      rw [e2]
      have hP0 : 0 ≤ (∏ i, ‖u i‖) * ∏ j, ‖v j‖ :=
        mul_nonneg (Finset.prod_nonneg fun i _ => norm_nonneg _) (Finset.prod_nonneg fun i _ => norm_nonneg _)
      have hW0 : 0 ≤ r ^ (-(σ - 2)) * lw r ^ b :=
        mul_nonneg (Real.rpow_nonneg hr.le _) (pow_nonneg (lw_pos _).le _)
      have h1 := hK r hr hr1
      have h2 : (1 : ℝ) + r ^ (2 : ℝ) * lw r ^ b ≤ (1 + K) * (1 + r ^ (-(σ - 2)) * lw r ^ b) := by
        nlinarith
      have h3 : 0 ≤ C0 * A := mul_nonneg hC00 hA
      calc C0 * A * (1 + r ^ (2 : ℝ) * lw r ^ b) * ((∏ i, ‖u i‖) * ∏ j, ‖v j‖)
          ≤ C0 * A * ((1 + K) * (1 + r ^ (-(σ - 2)) * lw r ^ b)) * ((∏ i, ‖u i‖) * ∏ j, ‖v j‖) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 h3) hP0
        _ = _ := by ring
  | succ c ih =>
    intro σ hσ b m
    rcases m with _ | m'
    · exact ⟨0, le_rfl, fun {g} {A} h hA a hac => by omega⟩
    by_cases hσ0 : 0 ≤ σ
    · obtain ⟨C, hC0, hC⟩ := base_pos hd hσ0 hσ b (m' + 1) (c := c + 1) (by omega)
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
      have hcd := newtonPot_contDiffOn hd (by linarith) hA h
      have hcdat : ContDiffAt ℝ ((a + c + 1 : ℕ) : WithTop ℕ∞) (newtonPot d g) (X0, z0) :=
        (hcd.contDiffAt (hU.mem_nhds hq)).of_le (by exact_mod_cast (by omega : a + c + 1 ≤ m' + 1))
      have heq : dirD ((0 : Euc d), e) (newtonPot d g) =ᶠ[𝓝 (X0, z0)] newtonPot d (dirD ((0 : Euc d), e) g) := by
        filter_upwards [hU.mem_nhds hq] with p hp
        exact newtonPot_dirD hd (by linarith) hA h hp.1 (by linarith [hp.2]) p.1 p.2 rfl e
      have hstep : iteratedFDeriv ℝ (a + (c + 1)) (newtonPot d g) (X0, z0) (pat u v) =
          iteratedFDeriv ℝ (a + c) (dirD ((0 : Euc d), e) (newtonPot d g)) (X0, z0) (pat u v') := by
        rw [hpat]; exact (iteratedFDeriv_dirD hcdat ((0 : Euc d), e) (pat u v')).symm
      rw [hstep, (heq.iteratedFDeriv ℝ (a + c)).eq_of_nhds]
      have key := hC' h' (mul_nonneg hA (norm_nonneg e)) (a := a) (by omega) hr hr1 X0 z0 hz0 u v'
      have hexpo : σ + 1 - 2 + (c : ℝ) = σ - 2 + ((c + 1 : ℕ) : ℝ) := by push_cast; ring
      rw [hexpo] at key
      refine key.trans (le_of_eq ?_)
      rw [prod_norm_init v]
      simp only [hv', he]
      ring

end HRS.Parx

end
