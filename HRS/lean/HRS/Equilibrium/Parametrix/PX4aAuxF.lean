import HRS.Equilibrium.Parametrix.PX4aAuxE

/-!
# Packet PX4a auxiliaries F: chart sources with the cutoff `ζ_{1/32}`

`srcCls_chart'`: a conormal kernel cut off at `‖w‖ < 1/32` is a chart source of class `SrcCls`;
`SrcCls.shear`: the shear `(Y, w) ↦ (Y + λ w, w)` preserves `SrcCls`; sums and derivatives.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.Parx

variable {d : ℕ}

local notation "∞'" => ((⊤ : ℕ∞) : WithTop ℕ∞)

lemma zeta_snd_bound (m : ℕ) : ∃ α : ℝ, 0 ≤ α ∧ ∀ k ≤ m, ∀ q : Euc d × Euc d,
    ‖iteratedFDeriv ℝ k (fun p : Euc d × Euc d => px3a_zeta d (1 / 32) p.2) q‖ ≤ α := by
  obtain ⟨S, hS0, hS⟩ := px3a_zeta_deriv_bound (d := d) m
  refine ⟨S * 32 ^ m, by positivity, fun k hk q => ?_⟩
  have := norm_iteratedFDeriv_comp_clm_le (ContinuousLinearMap.snd ℝ (Euc d) (Euc d))
    (ContinuousLinearMap.norm_snd_le ℝ (Euc d) (Euc d)) (px3a_zeta_contDiff (d := d) (1 / 32) ⊤)
    (i := k) (by exact_mod_cast le_top) q
  refine this.trans ?_
  have h1 := hS (1 / 32) (by norm_num) k hk q.2
  refine h1.trans ?_
  have : ((1 / 32 : ℝ)⁻¹) ^ k ≤ 32 ^ m := by
    have e : ((1 / 32 : ℝ)⁻¹) = 32 := by norm_num
    rw [e]; exact pow_le_pow_right₀ (by norm_num) hk
  exact mul_le_mul_of_nonneg_left this hS0

set_option maxHeartbeats 1600000 in
lemma srcCls_chart' (σ : ℝ) (b m : ℕ) : ∃ K : ℝ, 0 ≤ K ∧ ∀ (B : ℝ) (F : Torus d → Torus d → ℝ), 0 ≤ B →
    Conormal σ b m B F → SrcCls d σ b m (K * B) (fun p => px3a_zeta d (1 / 32) p.2 * toChart F p) := by
  obtain ⟨α, hα0, hα⟩ := zeta_snd_bound (d := d) m
  refine ⟨2 ^ m * α * ((m : ℝ) + 1) ^ 2, by positivity, fun B F hB hF => ?_⟩
  have hcd := toChart_contDiffOn_chartU hF
  have hχ : ContDiff ℝ (m : WithTop ℕ∞) (fun p : Euc d × Euc d => px3a_zeta d (1 / 32) p.2) :=
    ((px3a_zeta_contDiff (d := d) (1 / 32) ⊤).comp contDiff_snd).of_le (by exact_mod_cast le_top)
  have hzero : ∀ p : Euc d × Euc d, 1 / 8 ≤ ‖p.2‖ →
      (fun p : Euc d × Euc d => px3a_zeta d (1 / 32) p.2 * toChart F p) =ᶠ[𝓝 p] fun _ => (0 : ℝ) := by
    intro p hp
    filter_upwards [(isOpen_lt continuous_const (continuous_norm.comp continuous_snd)).mem_nhds
      (show (1 / 32 : ℝ) < ‖p.2‖ by linarith)] with p' hp'
    show px3a_zeta d (1 / 32) p'.2 * toChart F p' = 0
    rw [px3a_zeta_eq_zero (by norm_num : (0 : ℝ) < 1 / 32) (by simpa using hp'.le), zero_mul]
  have hsm : ContDiffOn ℝ (m : WithTop ℕ∞) (fun p : Euc d × Euc d => px3a_zeta d (1 / 32) p.2 * toChart F p)
      {p : Euc d × Euc d | p.2 ≠ 0} := by
    intro p hp
    by_cases h8 : ‖p.2‖ < 1 / 8
    · have hpU : p ∈ {p : Euc d × Euc d | 0 < ‖p.2‖ ∧ ‖p.2‖ < 1 / 8} := ⟨norm_pos_iff.mpr hp, h8⟩
      exact (hχ.contDiffAt.mul (hcd.contDiffAt (isOpen_chartU.mem_nhds hpU))).contDiffWithinAt
    · exact ((contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq (hzero p (not_lt.mp h8))).contDiffWithinAt
  refine ⟨hsm, fun X w hw => by rw [px3a_zeta_eq_zero (by norm_num : (0 : ℝ) < 1 / 32) (by linarith [hw] : 1 / 32 ≤ ‖w‖), zero_mul], ?_⟩
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
    have hTB := leibniz_TB isOpen_chartU hq (a + c) a c rfl (fun p : Euc d × Euc d => px3a_zeta d (1 / 32) p.2)
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
    have hT : TB (fun p : Euc d × Euc d => px3a_zeta d (1 / 32) p.2 * toChart F p) (X, w) a c 0 := fun u v => by
      rw [(((hzero (X, w) (not_lt.mp h8)).iteratedFDeriv ℝ (a + c)).eq_of_nhds), iteratedFDeriv_zero_fun]
      simp
    have := norm_le_of_tb isOpen_ne_snd (hsm.of_le (by exact_mod_cast hac)) hq le_rfl hT
    refine this.trans ?_
    have : 0 ≤ ‖w‖ ^ (-(σ + (c : ℝ))) * (1 + |Real.log ‖w‖|) ^ b :=
      mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (pow_nonneg (by positivity) _)
    have hK : 0 ≤ 2 ^ m * α * ((m : ℝ) + 1) ^ 2 := by positivity
    exact mul_nonneg (mul_nonneg hK hB) (by linarith)


lemma srcCls_chart'_zero (F : Torus d → Torus d → ℝ) (X w : Euc d) (hw : 1 / 32 ≤ ‖w‖) :
    px3a_zeta d (1 / 32) w * toChart F (X, w) = 0 := by
  rw [px3a_zeta_eq_zero (by norm_num : (0 : ℝ) < 1 / 32) hw, zero_mul]

namespace SrcCls

variable {σ : ℝ} {b m : ℕ} {A : ℝ} {g : Euc d × Euc d → ℝ}

set_option maxHeartbeats 1600000 in
/-- The shear `(Y, w) ↦ (Y + λ w, w)` preserves the class (with the loss `(1 + |λ|)^m`). -/
lemma shear (h : SrcCls d σ b m A g) (hA : 0 ≤ A) (hz : ∀ X w : Euc d, 1 / 32 ≤ ‖w‖ → g (X, w) = 0)
    (lam : ℝ) : SrcCls d σ b m ((1 + |lam|) ^ m * A) (fun p => g (shearCLM d lam p)) where
  smooth := h.smooth.comp (shearCLM d lam).contDiff.contDiffOn (fun p hp => by
    simpa [shearCLM_apply] using hp)
  supp X w hw := by
    simpa [shearCLM_apply] using h.supp (X + lam • w) w hw
  bound a c hac X w hw0 := by
    have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hw0
    have hq : ((X, w) : Euc d × Euc d) ∈ {p : Euc d × Euc d | p.2 ≠ 0} := hw0
    have hcomp : ContDiffOn ℝ ((a + c : ℕ) : WithTop ℕ∞) (fun p => g (shearCLM d lam p))
        {p : Euc d × Euc d | p.2 ≠ 0} :=
      (h.smooth.of_le (by exact_mod_cast hac)).comp (shearCLM d lam).contDiff.contDiffOn
        (fun p hp => by simpa [shearCLM_apply] using hp)
    have hW0 : 0 ≤ 1 + ‖w‖ ^ (-(σ + (c : ℝ))) * (1 + |Real.log ‖w‖|) ^ b := by
      have : 0 ≤ ‖w‖ ^ (-(σ + (c : ℝ))) * (1 + |Real.log ‖w‖|) ^ b :=
        mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (pow_nonneg (by positivity) _)
      linarith
    by_cases hbig : ‖w‖ ≤ 1
    · set W : ℕ → ℝ := fun j' => A * (1 + ‖w‖ ^ (-(σ + (j' : ℝ))) * (1 + |Real.log ‖w‖|) ^ b) with hW
      have hWmono : ∀ j', W j' ≤ W (j' + 1) := by
        intro j'
        simp only [hW]
        refine mul_le_mul_of_nonneg_left ?_ hA
        have h1 : ‖w‖ ^ (-(σ + (j' : ℝ))) ≤ ‖w‖ ^ (-(σ + ((j' + 1 : ℕ) : ℝ))) :=
          Real.rpow_le_rpow_of_exponent_ge hwpos hbig (by push_cast; linarith)
        have h2 : 0 ≤ (1 + |Real.log ‖w‖|) ^ b := pow_nonneg (by positivity) _
        nlinarith
      have hmem : shearCLM d lam (X, w) ∈ {p : Euc d × Euc d | p.2 ≠ 0} := by
        simpa [shearCLM_apply] using hw0
      have hTB := tb_shear lam isOpen_ne_snd c a g W hWmono (h.smooth.of_le (by exact_mod_cast hac))
        (X, w) hmem (fun i' j' hij => by
          have hmem' : ((X + lam • w, w) : Euc d × Euc d) ∈ {p : Euc d × Euc d | p.2 ≠ 0} := hw0
          rw [show shearCLM d lam (X, w) = (X + lam • w, w) from rfl]
          exact tb_of_norm_le isOpen_ne_snd (h.smooth.of_le (by exact_mod_cast (by omega : i' + j' ≤ m))) hmem'
            (h.bound i' j' (by omega) (X + lam • w) w hw0))
      have hWc : 0 ≤ (1 + |lam|) ^ c * W c := by
        simp only [hW]; positivity
      have hn := norm_le_of_tb isOpen_ne_snd hcomp hq hWc hTB
      refine hn.trans ?_
      have h1 : (1 + |lam|) ^ c ≤ (1 + |lam|) ^ m :=
        pow_le_pow_right₀ (by linarith [abs_nonneg lam]) (by omega)
      simp only [hW]
      calc (1 + |lam|) ^ c * (A * (1 + ‖w‖ ^ (-(σ + (c : ℝ))) * (1 + |Real.log ‖w‖|) ^ b))
          ≤ (1 + |lam|) ^ m * (A * (1 + ‖w‖ ^ (-(σ + (c : ℝ))) * (1 + |Real.log ‖w‖|) ^ b)) := by
            refine mul_le_mul_of_nonneg_right h1 (mul_nonneg hA hW0)
        _ = _ := by ring
    · push_neg at hbig
      have hev : (fun p : Euc d × Euc d => g (shearCLM d lam p)) =ᶠ[𝓝 (X, w)] fun _ => (0 : ℝ) := by
        filter_upwards [(isOpen_lt continuous_const (continuous_norm.comp continuous_snd)).mem_nhds
          (show (1 : ℝ) < ‖((X, w) : Euc d × Euc d).2‖ from hbig)] with p hp
        have hp' : (1 : ℝ) < ‖p.2‖ := hp
        simp only [shearCLM_apply]
        exact hz _ _ (by linarith)
      have hT : TB (fun p : Euc d × Euc d => g (shearCLM d lam p)) (X, w) a c 0 := fun u v => by
        rw [(hev.iteratedFDeriv ℝ (a + c)).eq_of_nhds, iteratedFDeriv_zero_fun]
        simp
      have := norm_le_of_tb isOpen_ne_snd hcomp hq le_rfl hT
      refine this.trans ?_
      have hK : 0 ≤ (1 + |lam|) ^ m * A := by positivity
      exact mul_nonneg hK hW0

lemma zero (σ : ℝ) (b m : ℕ) : SrcCls d σ b m 0 (fun _ : Euc d × Euc d => (0 : ℝ)) where
  smooth := contDiffOn_const
  supp _ _ _ := rfl
  bound a c hac X w hw0 := by
    have hq : ((X, w) : Euc d × Euc d) ∈ {p : Euc d × Euc d | p.2 ≠ 0} := hw0
    have hT : TB (fun _ : Euc d × Euc d => (0 : ℝ)) (X, w) a c 0 := fun u v => by
      rw [iteratedFDeriv_zero_fun]; simp
    have hc : ContDiffOn ℝ ((a + c : ℕ) : WithTop ℕ∞) (fun _ : Euc d × Euc d => (0 : ℝ))
        {p : Euc d × Euc d | p.2 ≠ 0} := contDiffOn_const
    have := norm_le_of_tb isOpen_ne_snd hc hq le_rfl hT
    simpa using this

lemma add {A₁ A₂ : ℝ} {g₁ g₂ : Euc d × Euc d → ℝ} (h₁ : SrcCls d σ b m A₁ g₁)
    (h₂ : SrcCls d σ b m A₂ g₂) (hA₁ : 0 ≤ A₁) (hA₂ : 0 ≤ A₂) :
    SrcCls d σ b m (A₁ + A₂) (fun p => g₁ p + g₂ p) where
  smooth := h₁.smooth.add h₂.smooth
  supp X w hw := by simp [h₁.supp X w hw, h₂.supp X w hw]
  bound a c hac X w hw0 := by
    have hq : ((X, w) : Euc d × Euc d) ∈ {p : Euc d × Euc d | p.2 ≠ 0} := hw0
    rw [mixedDeriv_add isOpen_ne_snd (h₁.smooth.of_le (by exact_mod_cast hac))
      (h₂.smooth.of_le (by exact_mod_cast hac)) hq]
    refine (norm_add_le (mixedDeriv a c g₁ X w) (mixedDeriv a c g₂ X w)).trans ?_
    have e1 := h₁.bound a c hac X w hw0
    have e2 := h₂.bound a c hac X w hw0
    have : 0 ≤ 1 + ‖w‖ ^ (-(σ + (c : ℝ))) * (1 + |Real.log ‖w‖|) ^ b := by
      have : 0 ≤ ‖w‖ ^ (-(σ + (c : ℝ))) * (1 + |Real.log ‖w‖|) ^ b :=
        mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (pow_nonneg (by positivity) _)
      linarith
    nlinarith

lemma sum {ι : Type*} (s : Finset ι) (A : ι → ℝ) (g : ι → Euc d × Euc d → ℝ)
    (h : ∀ i ∈ s, SrcCls d σ b m (A i) (g i)) (hA : ∀ i ∈ s, 0 ≤ A i) :
    SrcCls d σ b m (∑ i ∈ s, A i) (fun p => ∑ i ∈ s, g i p) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using SrcCls.zero (d := d) σ b m
  | insert a s ha ih =>
    have h1 := ih (fun i hi => h i (Finset.mem_insert_of_mem hi)) (fun i hi => hA i (Finset.mem_insert_of_mem hi))
    have h2 := (h a (Finset.mem_insert_self a s)).add h1 (hA a (Finset.mem_insert_self a s))
      (Finset.sum_nonneg fun i hi => hA i (Finset.mem_insert_of_mem hi))
    simpa [Finset.sum_insert ha] using h2

end SrcCls

end HRS.Parx

end
