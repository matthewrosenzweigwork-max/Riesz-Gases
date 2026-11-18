import HRS.Equilibrium.Parametrix.PX3aAuxN

/-!
# Packet PX3a auxiliaries O: transfer from torus kernels to chart sources
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.Parx

variable {d : ℕ}

local notation "∞'" => ((⊤ : ℕ∞) : WithTop ℕ∞)

lemma chi_snd_bound (m : ℕ) : ∃ α : ℝ, 0 ≤ α ∧ ∀ k ≤ m, ∀ q : Euc d × Euc d,
    ‖iteratedFDeriv ℝ k (fun p : Euc d × Euc d => chi d p.2) q‖ ≤ α := by
  obtain ⟨C, hC0, hC⟩ := (chi_hasCompactSupport (d := d)).exists_bound_iteratedFDeriv
    (chi_contDiff (d := d) ⊤) m
  refine ⟨C, hC0, fun k hk q => ?_⟩
  have := norm_iteratedFDeriv_comp_clm_le (ContinuousLinearMap.snd ℝ (Euc d) (Euc d))
    (ContinuousLinearMap.norm_snd_le ℝ (Euc d) (Euc d)) (chi_contDiff (d := d) ⊤)
    (i := k) (by exact_mod_cast le_top) q
  exact this.trans (hC k hk _)

lemma iteratedFDeriv_zero_fun (k : ℕ) (p : Euc d × Euc d) :
    iteratedFDeriv ℝ k (fun _ : Euc d × Euc d => (0 : ℝ)) p = 0 := by
  rcases k with _ | k
  · ext v; simp [iteratedFDeriv_zero_eq_comp]
  · have := iteratedFDeriv_const_of_ne (𝕜 := ℝ) (E := Euc d × Euc d) (by omega : k + 1 ≠ 0) (0 : ℝ)
    exact congrFun this p

lemma isOpen_chartU : IsOpen {p : Euc d × Euc d | 0 < ‖p.2‖ ∧ ‖p.2‖ < 1 / 8} :=
  (isOpen_lt continuous_const (continuous_norm.comp continuous_snd)).inter
    (isOpen_lt (continuous_norm.comp continuous_snd) continuous_const)

lemma chartU_subset_Uc : {p : Euc d × Euc d | 0 < ‖p.2‖ ∧ ‖p.2‖ < 1 / 8} ⊆ Uc d := by
  intro p hp
  exact mem_Uc (norm_pos_iff.mp hp.1) (by unfold r0; exact hp.2)

lemma toChart_contDiffOn_chartU {σ : ℝ} {b : ℕ → ℕ} {m : ℕ} {B : ℝ} {F : Torus d → Torus d → ℝ}
    (hF : ConormalL σ b m B F) :
    ContDiffOn ℝ (m : WithTop ℕ∞) (toChart F) {p : Euc d × Euc d | 0 < ‖p.2‖ ∧ ‖p.2‖ < 1 / 8} :=
  (toChart_contDiffOn hF.smooth).mono chartU_subset_Uc

set_option maxHeartbeats 1600000 in
lemma srcCls_chart (σ : ℝ) (b m : ℕ) : ∃ K : ℝ, 0 ≤ K ∧ ∀ (B : ℝ) (F : Torus d → Torus d → ℝ), 0 ≤ B →
    Conormal σ b m B F → SrcCls d σ b m (K * B) (fun p => chi d p.2 * toChart F p) := by
  obtain ⟨α, hα0, hα⟩ := chi_snd_bound (d := d) m
  refine ⟨2 ^ m * α * ((m : ℝ) + 1) ^ 2, by positivity, fun B F hB hF => ?_⟩
  have hcd := toChart_contDiffOn_chartU hF
  have hχ : ContDiff ℝ (m : WithTop ℕ∞) (fun p : Euc d × Euc d => chi d p.2) :=
    ((chi_contDiff (d := d) ⊤).comp contDiff_snd).of_le (by exact_mod_cast le_top)
  have hzero : ∀ p : Euc d × Euc d, 1 / 8 ≤ ‖p.2‖ →
      (fun p : Euc d × Euc d => chi d p.2 * toChart F p) =ᶠ[𝓝 p] fun _ => (0 : ℝ) := by
    intro p hp
    filter_upwards [(isOpen_lt continuous_const (continuous_norm.comp continuous_snd)).mem_nhds
      (show (1 / 16 : ℝ) < ‖p.2‖ by linarith)] with p' hp'
    simp [chi_eq_zero hp'.le]
  have hsm : ContDiffOn ℝ (m : WithTop ℕ∞) (fun p : Euc d × Euc d => chi d p.2 * toChart F p)
      {p : Euc d × Euc d | p.2 ≠ 0} := by
    intro p hp
    by_cases h8 : ‖p.2‖ < 1 / 8
    · have hpU : p ∈ {p : Euc d × Euc d | 0 < ‖p.2‖ ∧ ‖p.2‖ < 1 / 8} := ⟨norm_pos_iff.mpr hp, h8⟩
      exact (hχ.contDiffAt.mul (hcd.contDiffAt (isOpen_chartU.mem_nhds hpU))).contDiffWithinAt
    · exact ((contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq (hzero p (not_lt.mp h8))).contDiffWithinAt
  refine ⟨hsm, fun X w hw => by simp [chi_eq_zero hw.le], ?_⟩
  intro a c hac X w hw0
  have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hw0
  by_cases h8 : ‖w‖ < 1 / 8
  · have hq : ((X, w) : Euc d × Euc d) ∈ {p : Euc d × Euc d | 0 < ‖p.2‖ ∧ ‖p.2‖ < 1 / 8} := ⟨hwpos, h8⟩
    set Tw : ℝ := 1 + ‖w‖ ^ (-(σ + c)) * (1 + |Real.log ‖w‖|) ^ b with hTw
    set W : ℕ → ℕ → ℝ := fun _ j => B * (1 + ‖w‖ ^ (-(σ + (j : ℝ))) * (1 + |Real.log ‖w‖|) ^ b) with hW
    have hW0 : ∀ i j, 0 ≤ W i j := fun i j =>
      mul_nonneg hB (by have : 0 ≤ ‖w‖ ^ (-(σ + (j : ℝ))) * (1 + |Real.log ‖w‖|) ^ b :=
                          mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (pow_nonneg (by positivity) _)
                        linarith)
    have hTB := leibniz_TB isOpen_chartU hq (a + c) a c rfl (fun p : Euc d × Euc d => chi d p.2)
      (toChart F) α W hα0 hW0 (hχ.contDiffOn.of_le (by exact_mod_cast hac))
      (hcd.of_le (by exact_mod_cast hac)) (fun k hk => hα k (by omega) (X, w))
      (fun i hi j hj => tb_of_norm_le isOpen_chartU
        (hcd.of_le (by exact_mod_cast (by omega : i + j ≤ m))) hq
        (hF.near i j (by omega) X w hw0 h8))
    set Ssum : ℝ := ∑ j ∈ Finset.range (c + 1), ∑ i ∈ Finset.range (a + 1), W i j with hSdef
    have hSle : Ssum ≤ ((c : ℝ) + 1) * (((a : ℝ) + 1) * (B * Tw)) := by
      have : ∀ j ∈ Finset.range (c + 1), ∑ i ∈ Finset.range (a + 1), W i j ≤ ((a : ℝ) + 1) * (B * Tw) := by
        intro j hj
        have hjc : j ≤ c := by have := Finset.mem_range.mp hj; omega
        have h1 : ‖w‖ ^ (-(σ + (j : ℝ))) ≤ ‖w‖ ^ (-(σ + (c : ℝ))) :=
          Real.rpow_le_rpow_of_exponent_ge hwpos (by linarith) (by
            have : (j : ℝ) ≤ c := by exact_mod_cast hjc
            linarith)
        have h2 : W 0 j ≤ B * Tw := by
          simp only [hW, hTw]
          refine mul_le_mul_of_nonneg_left ?_ hB
          have : 0 ≤ (1 + |Real.log ‖w‖|) ^ b := pow_nonneg (by positivity) _
          nlinarith
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast
        exact mul_le_mul_of_nonneg_left h2 (by positivity)
      calc Ssum ≤ ∑ j ∈ Finset.range (c + 1), ((a : ℝ) + 1) * (B * Tw) := Finset.sum_le_sum this
        _ = _ := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring
    have hTw0 : 0 ≤ Tw := by
      have : 0 ≤ ‖w‖ ^ (-(σ + (c : ℝ))) * (1 + |Real.log ‖w‖|) ^ b :=
        mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (pow_nonneg (by positivity) _)
      simp only [hTw]; linarith
    have hS0 : 0 ≤ Ssum := Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun i _ => hW0 i j
    have hnorm := norm_le_of_tb isOpen_chartU (hsm.mono (fun p hp => (norm_pos_iff.mp hp.1 : p.2 ≠ 0))
      |>.of_le (by exact_mod_cast hac)) hq (mul_nonneg (mul_nonneg (by positivity) hα0) hS0) hTB
    refine hnorm.trans ?_
    have h2m : (2 : ℝ) ^ (a + c) ≤ 2 ^ m := pow_le_pow_right₀ (by norm_num) hac
    have hac' : ((c : ℝ) + 1) * ((a : ℝ) + 1) ≤ ((m : ℝ) + 1) ^ 2 := by
      have h1 : (c : ℝ) + 1 ≤ m + 1 := by have : (c : ℝ) ≤ m := by exact_mod_cast (by omega : c ≤ m)
                                          linarith
      have h2 : (a : ℝ) + 1 ≤ m + 1 := by have : (a : ℝ) ≤ m := by exact_mod_cast (by omega : a ≤ m)
                                          linarith
      nlinarith [Nat.cast_nonneg (α := ℝ) a, Nat.cast_nonneg (α := ℝ) c]
    calc 2 ^ (a + c) * α * Ssum ≤ 2 ^ m * α * (((c : ℝ) + 1) * (((a : ℝ) + 1) * (B * Tw))) :=
          mul_le_mul (mul_le_mul_of_nonneg_right h2m hα0) hSle hS0 (by positivity)
      _ = (2 ^ m * α * (((c : ℝ) + 1) * ((a : ℝ) + 1))) * (B * Tw) := by ring
      _ ≤ (2 ^ m * α * ((m : ℝ) + 1) ^ 2) * (B * Tw) := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hac' (by positivity)) (mul_nonneg hB hTw0)
      _ = _ := by ring
  · have hq : ((X, w) : Euc d × Euc d) ∈ {p : Euc d × Euc d | p.2 ≠ 0} := hw0
    have hT : TB (fun p : Euc d × Euc d => chi d p.2 * toChart F p) (X, w) a c 0 := fun u v => by
      rw [(((hzero (X, w) (not_lt.mp h8)).iteratedFDeriv ℝ (a + c)).eq_of_nhds), iteratedFDeriv_zero_fun]
      simp
    have := norm_le_of_tb isOpen_ne_snd (hsm.of_le (by exact_mod_cast hac)) hq le_rfl hT
    refine this.trans ?_
    have : 0 ≤ ‖w‖ ^ (-(σ + (c : ℝ))) * (1 + |Real.log ‖w‖|) ^ b :=
      mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (pow_nonneg (by positivity) _)
    have hK : 0 ≤ 2 ^ m * α * ((m : ℝ) + 1) ^ 2 := by positivity
    exact mul_nonneg (mul_nonneg hK hB) (by linarith)

end HRS.Parx

end
