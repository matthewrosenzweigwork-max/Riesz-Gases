import HRS.Equilibrium.Parametrix.PX3aAuxP

/-!
# Packet PX3a auxiliaries Q: the Newton chart function is a conormal kernel
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.Parx

variable {d : ℕ}

local notation "∞'" => ((⊤ : ℕ∞) : WithTop ℕ∞)

lemma TB_const_mul {f : Euc d × Euc d → ℝ} {q : Euc d × Euc d} {i j : ℕ} {W : ℝ} (κ : ℝ)
    (hf : ContDiffAt ℝ ((i + j : ℕ) : WithTop ℕ∞) f q) (h : TB f q i j W) :
    TB (fun p => κ * f p) q i j (|κ| * W) := by
  intro u v
  have := iteratedFDeriv_const_smul_apply' (𝕜 := ℝ) (a := κ) hf
  simp only [smul_eq_mul] at this
  rw [this, ContinuousMultilinearMap.smul_apply, smul_eq_mul, abs_mul]
  have := h u v
  calc |κ| * |iteratedFDeriv ℝ (i + j) f q (pat u v)| ≤ |κ| * (W * (∏ i, ‖u i‖) * ∏ j, ‖v j‖) :=
        mul_le_mul_of_nonneg_left this (abs_nonneg _)
    _ = _ := by ring

lemma wt_le (b : ℕ) : ∃ K : ℝ, 0 ≤ K ∧ ∀ r : ℝ, 0 < r → r < 1 / 8 → ∀ (s s' : ℝ) (b1 b2 : ℕ),
    s + 1 ≤ s' → b1 ≤ b + 1 → b ≤ b2 →
      r ^ (-s) * lw r ^ b1 ≤ K * (r ^ (-s') * lw r ^ b2) := by
  obtain ⟨K, hK0, hK⟩ := rpow_log_pow_le 1 one_pos (b + 1)
  refine ⟨K, hK0, fun r hr hr1 s s' b1 b2 hss hb1 hb2 => ?_⟩
  have h1 : lw r ^ b1 ≤ lw r ^ (b + 1) := pow_le_pow_right₀ (one_le_lw r) hb1
  have h2 : 1 ≤ lw r ^ b2 := one_le_pow₀ (one_le_lw r)
  have hrs : r ^ (-s) = r ^ (-s') * r ^ (s' - s) := by
    rw [← Real.rpow_add hr]; congr 1; ring
  have h3 : r ^ (s' - s) ≤ r ^ (1 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_ge hr (by linarith) (by linarith)
  have h4 : r ^ (1 : ℝ) * lw r ^ (b + 1) ≤ K := hK r hr (by linarith)
  have hr0 : 0 ≤ r ^ (-s') := Real.rpow_nonneg hr.le _
  have hl0 : 0 ≤ lw r ^ (b + 1) := pow_nonneg (lw_pos _).le _
  calc r ^ (-s) * lw r ^ b1 ≤ r ^ (-s) * lw r ^ (b + 1) :=
        mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg hr.le _)
    _ = r ^ (-s') * (r ^ (s' - s) * lw r ^ (b + 1)) := by rw [hrs]; ring
    _ ≤ r ^ (-s') * (r ^ (1 : ℝ) * lw r ^ (b + 1)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h3 hl0) hr0
    _ ≤ r ^ (-s') * K := mul_le_mul_of_nonneg_left h4 hr0
    _ ≤ r ^ (-s') * (K * lw r ^ b2) := by
        refine mul_le_mul_of_nonneg_left ?_ hr0
        nlinarith
    _ = _ := by ring

lemma newtonChart_eq (d : ℕ) (ν : ℝ) (F : Torus d → Torus d → ℝ) (p : Euc d × Euc d) :
    newtonChart d ν (toChart F) p =
      chi d p.2 * ((1 / (2 * ν)) * newtonPot d (fun q => chi d q.2 * toChart F q) p) := by
  unfold newtonChart newtonPot
  congr 1
  rw [← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun w => ?_)
  simp only [newtonKernel_eq]
  ring

set_option maxHeartbeats 3200000 in
theorem newton_conormal_of_pot (hd : 2 ≤ d) {ν : ℝ} (hν : 0 < ν) {σ : ℝ} (hσ : σ < d) (b m : ℕ)
    (b' : ℕ → ℕ) (hb1 : ∀ c, b ≤ b' c) (hb2 : ∀ c, b' c ≤ b + 1) :
    ∃ Cq : ℝ, 0 ≤ Cq ∧ ∀ (Cpot B : ℝ) (F : Torus d → Torus d → ℝ), 0 ≤ Cpot → 0 ≤ B →
      Conormal σ b m B F →
      (∀ a c : ℕ, a + c ≤ m → ∀ r : ℝ, 0 < r → r < 1 / 8 → ∀ X z : Euc d, ‖z‖ = r →
        ∀ (u : Fin a → Euc d) (v : Fin c → Euc d),
        |iteratedFDeriv ℝ (a + c) (newtonPot d (fun q => chi d q.2 * toChart F q)) (X, z) (pat u v)| ≤
          Cpot * B * (1 + r ^ (-(σ - 2 + c)) * lw r ^ b' c) * ((∏ i, ‖u i‖) * ∏ j, ‖v j‖)) →
      ConormalL (σ - 2) b' m (Cq * Cpot * B) (ofChart (newtonChart d ν (toChart F))) := by
  obtain ⟨α, hα0, hα⟩ := chi_snd_bound (d := d) m
  obtain ⟨K1, hK1, hsrc⟩ := srcCls_chart (d := d) σ b m
  obtain ⟨Kw, hKw0, hKw⟩ := wt_le b
  refine ⟨2 ^ m * α * ((m : ℝ) + 1) ^ 2 * (1 / (2 * ν)) * (1 + Kw), by positivity,
    fun Cpot B F hCp hB hF hpot => ?_⟩
  set g : Euc d × Euc d → ℝ := fun q => chi d q.2 * toChart F q with hgdef
  have hg : SrcCls d σ b m (K1 * B) g := hsrc B F hB hF
  have hA : 0 ≤ K1 * B := mul_nonneg hK1 hB
  set N : Euc d × Euc d → ℝ := newtonChart d ν (toChart F) with hNdef
  have hNfun : N = fun p => chi d p.2 * ((1 / (2 * ν)) * newtonPot d g p) :=
    funext fun p => newtonChart_eq d ν F p
  have hκ : 0 < 1 / (2 * ν) := by positivity
  have hcdP := newtonPot_contDiffOn hd hσ hA hg
  have hχ : ContDiff ℝ (m : WithTop ℕ∞) (fun p : Euc d × Euc d => chi d p.2) :=
    ((chi_contDiff (d := d) ⊤).comp contDiff_snd).of_le (by exact_mod_cast le_top)
  have hzero : ∀ p : Euc d × Euc d, 1 / 8 ≤ ‖p.2‖ → N =ᶠ[𝓝 p] fun _ => (0 : ℝ) := by
    intro p hp
    filter_upwards [(isOpen_lt continuous_const (continuous_norm.comp continuous_snd)).mem_nhds
      (show (1 / 16 : ℝ) < ‖p.2‖ by linarith)] with p' hp'
    exact px3a_newtonChart_supp F ν p'.1 p'.2 hp'.le
  have hNsm : ContDiffOn ℝ (m : WithTop ℕ∞) N {p : Euc d × Euc d | p.2 ≠ 0} := by
    intro p hp
    by_cases h8 : ‖p.2‖ < 1 / 8
    · have hpU : p ∈ {p : Euc d × Euc d | 0 < ‖p.2‖ ∧ ‖p.2‖ < 1 / 8} := ⟨norm_pos_iff.mpr hp, h8⟩
      rw [hNfun]
      exact (hχ.contDiffAt.mul (contDiffAt_const.mul (hcdP.contDiffAt (isOpen_chartU.mem_nhds hpU)))).contDiffWithinAt
    · exact ((contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq (hzero p (not_lt.mp h8))).contDiffWithinAt
  refine conormalL_ofChart (mul_nonneg (mul_nonneg (by positivity) hCp) hB) hNsm
    (fun X z k hk => px3a_newtonChart_periodic F ν X z k hk)
    (fun X w hw => px3a_newtonChart_supp F ν X w hw) ?_
  intro a c hac X z hz0 hzr
  have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  have hzr' : ‖z‖ < 1 / 8 := by unfold r0 at hzr; exact hzr
  have hq : ((X, z) : Euc d × Euc d) ∈ {p : Euc d × Euc d | 0 < ‖p.2‖ ∧ ‖p.2‖ < 1 / 8} := ⟨hzpos, hzr'⟩
  set r : ℝ := ‖z‖ with hr
  set T : ℕ → ℝ := fun j => 1 + r ^ (-(σ - 2 + (j : ℝ))) * lw r ^ b' j with hT
  have hT0 : ∀ j, 0 ≤ T j := fun j => by
    have : 0 ≤ r ^ (-(σ - 2 + (j : ℝ))) * lw r ^ b' j :=
      mul_nonneg (Real.rpow_nonneg hzpos.le _) (pow_nonneg (lw_pos _).le _)
    simp only [hT]; linarith
  have hT1 : ∀ j, 1 ≤ T j := fun j => by
    have : 0 ≤ r ^ (-(σ - 2 + (j : ℝ))) * lw r ^ b' j :=
      mul_nonneg (Real.rpow_nonneg hzpos.le _) (pow_nonneg (lw_pos _).le _)
    simp only [hT]; linarith
  have hTj : ∀ j ≤ c, T j ≤ (1 + Kw) * T c := by
    intro j hj
    have hX : r ^ (-(σ - 2 + (j : ℝ))) * lw r ^ b' j ≤ (1 + Kw) * (r ^ (-(σ - 2 + (c : ℝ))) * lw r ^ b' c) := by
      have hX0 : 0 ≤ r ^ (-(σ - 2 + (c : ℝ))) * lw r ^ b' c :=
        mul_nonneg (Real.rpow_nonneg hzpos.le _) (pow_nonneg (lw_pos _).le _)
      by_cases hjc : j = c
      · subst hjc; nlinarith
      · have hjc' : j + 1 ≤ c := by omega
        have := hKw r hzpos hzr' (σ - 2 + (j : ℝ)) (σ - 2 + (c : ℝ)) (b' j) (b' c)
          (by have : ((j : ℝ) + 1) ≤ c := by exact_mod_cast hjc'
              linarith) (hb2 j) (hb1 c)
        nlinarith
    have hX0 : 0 ≤ r ^ (-(σ - 2 + (c : ℝ))) * lw r ^ b' c :=
      mul_nonneg (Real.rpow_nonneg hzpos.le _) (pow_nonneg (lw_pos _).le _)
    simp only [hT]
    nlinarith
  -- TB for the scaled potential
  set Wf : ℕ → ℕ → ℝ := fun _ j => (1 / (2 * ν)) * (Cpot * B * T j) with hWf
  have hWf0 : ∀ i j, 0 ≤ Wf i j := fun i j => by
    simp only [hWf]; exact mul_nonneg hκ.le (mul_nonneg (mul_nonneg hCp hB) (hT0 j))
  have hPd : ∀ k ≤ m, ContDiffAt ℝ (k : WithTop ℕ∞) (newtonPot d g) (X, z) := fun k hk =>
    (hcdP.contDiffAt (isOpen_chartU.mem_nhds hq)).of_le (by exact_mod_cast hk)
  have hTBP : ∀ i ≤ a, ∀ j ≤ c, TB (fun p => (1 / (2 * ν)) * newtonPot d g p) (X, z) i j (Wf i j) := by
    intro i hi j hj
    have h1 : TB (newtonPot d g) (X, z) i j (Cpot * B * T j) := by
      intro u v
      have := hpot i j (by omega) r hzpos hzr' X z rfl u v
      calc _ ≤ Cpot * B * (1 + r ^ (-(σ - 2 + (j : ℝ))) * lw r ^ b' j) * ((∏ i, ‖u i‖) * ∏ j, ‖v j‖) := this
        _ = _ := by simp only [hT]; ring
    have := TB_const_mul (1 / (2 * ν)) (hPd (i + j) (by omega)) h1
    rwa [abs_of_pos hκ] at this
  have hTBN := leibniz_TB isOpen_chartU hq (a + c) a c rfl (fun p : Euc d × Euc d => chi d p.2)
    (fun p => (1 / (2 * ν)) * newtonPot d g p) α Wf hα0 hWf0 (hχ.contDiffOn.of_le (by exact_mod_cast hac))
    (contDiffOn_const.mul (hcdP.of_le (by exact_mod_cast hac))) (fun k hk => hα k (by omega) (X, z)) hTBP
  set Ssum : ℝ := ∑ j ∈ Finset.range (c + 1), ∑ i ∈ Finset.range (a + 1), Wf i j with hSdef
  have hS0 : 0 ≤ Ssum := Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun i _ => hWf0 i j
  have hSle : Ssum ≤ ((c : ℝ) + 1) * (((a : ℝ) + 1) * ((1 / (2 * ν)) * (Cpot * B * ((1 + Kw) * T c)))) := by
    have : ∀ j ∈ Finset.range (c + 1), ∑ i ∈ Finset.range (a + 1), Wf i j ≤
        ((a : ℝ) + 1) * ((1 / (2 * ν)) * (Cpot * B * ((1 + Kw) * T c))) := by
      intro j hj
      have hjc : j ≤ c := by have := Finset.mem_range.mp hj; omega
      have h2 : Wf 0 j ≤ (1 / (2 * ν)) * (Cpot * B * ((1 + Kw) * T c)) := by
        simp only [hWf]
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hTj j hjc) (mul_nonneg hCp hB)) hκ.le
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      push_cast
      exact mul_le_mul_of_nonneg_left h2 (by positivity)
    calc Ssum ≤ ∑ j ∈ Finset.range (c + 1), ((a : ℝ) + 1) * ((1 / (2 * ν)) * (Cpot * B * ((1 + Kw) * T c))) :=
          Finset.sum_le_sum this
      _ = _ := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring
  have hNsm' : ContDiffOn ℝ ((a + c : ℕ) : WithTop ℕ∞) N {p : Euc d × Euc d | 0 < ‖p.2‖ ∧ ‖p.2‖ < 1 / 8} :=
    (hNsm.mono (fun p hp => (norm_pos_iff.mp hp.1 : p.2 ≠ 0))).of_le (by exact_mod_cast hac)
  have hnorm := norm_le_of_tb isOpen_chartU hNsm' hq (W := 2 ^ (a + c) * α * Ssum)
    (mul_nonneg (mul_nonneg (by positivity) hα0) hS0) (by rw [hNfun]; exact hTBN)
  refine hnorm.trans ?_
  have h2m : (2 : ℝ) ^ (a + c) ≤ 2 ^ m := pow_le_pow_right₀ (by norm_num) hac
  have hac' : ((c : ℝ) + 1) * ((a : ℝ) + 1) ≤ ((m : ℝ) + 1) ^ 2 := by
    have h1 : (c : ℝ) + 1 ≤ m + 1 := by
      have : (c : ℝ) ≤ m := by exact_mod_cast (by omega : c ≤ m)
      linarith
    have h2 : (a : ℝ) + 1 ≤ m + 1 := by
      have : (a : ℝ) ≤ m := by exact_mod_cast (by omega : a ≤ m)
      linarith
    nlinarith [Nat.cast_nonneg (α := ℝ) a, Nat.cast_nonneg (α := ℝ) c]
  have hRHS0 : 0 ≤ (1 / (2 * ν)) * (Cpot * B * ((1 + Kw) * T c)) :=
    mul_nonneg hκ.le (mul_nonneg (mul_nonneg hCp hB) (mul_nonneg (by positivity) (hT0 c)))
  calc 2 ^ (a + c) * α * Ssum ≤ 2 ^ m * α * (((c : ℝ) + 1) * (((a : ℝ) + 1) * ((1 / (2 * ν)) * (Cpot * B * ((1 + Kw) * T c))))) :=
        mul_le_mul (mul_le_mul_of_nonneg_right h2m hα0) hSle hS0 (by positivity)
    _ = (2 ^ m * α * (((c : ℝ) + 1) * ((a : ℝ) + 1))) * ((1 / (2 * ν)) * (Cpot * B * ((1 + Kw) * T c))) := by ring
    _ ≤ (2 ^ m * α * ((m : ℝ) + 1) ^ 2) * ((1 / (2 * ν)) * (Cpot * B * ((1 + Kw) * T c))) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hac' (by positivity)) hRHS0
    _ = _ := by simp only [hT, hr, lw]; ring

end HRS.Parx

end
