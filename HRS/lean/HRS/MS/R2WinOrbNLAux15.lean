import HRS.MS.R2WinOrbNLAux14

/-!
# S10.3 (nonlinear branch), part 15: pointwise time continuity of the trajectory, and the right derivative of the cancellation convolution

Prefix `s103n_`, namespace `HRS.MS.R2WinOrbNL`.

* `s103n_cont_time`: for a trajectory of the small class, `τ ↦ ρ_τ(y)` is continuous on `[0,∞)` (the class is continuous into `Σ^m`, `m > d/2`, and `Σ^m` controls
  the supremum norm, `mn_force_bound`).
* `s103n_ultK_hasDeriv`: the right derivative at `t` of `τ ↦ ultK κ (ρ_τ w) x` is `ultK κ (ρ'_t w) x`.  The difference quotients are uniformly Lipschitz
  and uniformly dominated (mean value inequality for right derivatives of the continuous functions `τ ↦ ρ_τ(a) - ρ_τ(b)`), so `s103n_ultK_tendsto` applies.
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory Metric
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace

namespace HRS.MS.R2WinOrbNL

open HRS HRS.Whole HRS.MS.Ul HRS.MS.MovLin HRS.MS.MovOsc HRS.MS.Mov63 HRS.MS.Who

variable {d : ℕ}

theorem s103n_cont_time {s a β : ℝ} {ρβ : Euc d → ℝ} (H : Mov2dTh d s β a ρβ) {m : ℕ}
    (hm : (d : ℝ) / 2 + 2 < m) {R0 c0 : ℝ} {f0 : Euc d → ℝ} {ρ : ℝ → Euc d → ℝ}
    (hρ : MovInSmallClass d s a β ρβ m R0 c0 f0 ρ) (y : Euc d) :
    ContinuousOn (fun τ => ρ τ y) (Set.Ici 0) := by
  obtain ⟨C0, hC0, hC⟩ := mn_force_bound H.hd H.hs0 H.hsd β a H.hβ H.hq ρβ H.hρ 0 m (by linarith)
  obtain ⟨hρsm, hρpos⟩ := mov2d_rho_data H
  have hvc : ∀ τ, 0 ≤ τ → Continuous (movV ρβ ρ τ) := fun τ hτ => by
    show Continuous (fun x => (ρ τ x - ρβ x) / Real.sqrt (ρβ x))
    obtain ⟨ψs, hψs⟩ := mov2d_sqrt_schwartz H
    have hsq : Continuous (fun x => Real.sqrt (ρβ x)) := by rw [← hψs]; exact ψs.continuous
    exact ((hρ.regular τ hτ).sub hρsm.continuous).div hsq (fun x => (Real.sqrt_pos.2 (hρpos x)).ne')
  intro σ hσ
  have hσ0 : 0 ≤ σ := hσ
  have hct := hρ.cont σ hσ
  have h0 : Tendsto (fun τ => dist (OscSpace.ofFun (d := d) (m : ℝ) (movV ρβ ρ τ))
      (OscSpace.ofFun (d := d) (m : ℝ) (movV ρβ ρ σ))) (𝓝[Set.Ici 0] σ) (𝓝 0) := by
    have := hct.tendsto.dist (tendsto_const_nhds (x := OscSpace.ofFun (d := d) (m : ℝ) (movV ρβ ρ σ)))
    simpa using this
  refine tendsto_iff_norm_sub_tendsto_zero.2 ?_
  have h0' := h0.const_mul (Real.sqrt (ρβ y) * C0)
  rw [mul_zero] at h0'
  refine squeeze_zero_norm' ?_ h0'
  filter_upwards [self_mem_nhdsWithin] with τ hτ
  have hτ0 : 0 ≤ τ := hτ
  have hmem : MemOsc (m : ℝ) (fun z => movV ρβ ρ τ z - movV ρβ ρ σ z) :=
    mov2d_memOsc_sub (hρ.weighted τ hτ0).1 (hρ.weighted σ hσ0).1
  have h1 := (hC _ ((hvc τ hτ0).sub (hvc σ hσ0)) hmem).2.1 0 (by norm_num) y
  rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at h1
  have hd : dist (OscSpace.ofFun (d := d) (m : ℝ) (movV ρβ ρ τ))
      (OscSpace.ofFun (d := d) (m : ℝ) (movV ρβ ρ σ)) = oscNorm (m : ℝ)
      (fun z => movV ρβ ρ τ z - movV ρβ ρ σ z) := by
    rw [dist_eq_norm, ← mov2d_ofFun_sub (hρ.weighted τ hτ0).1 (hρ.weighted σ hσ0).1,
      OscSpace.norm_ofFun _ hmem]
  rw [hd]
  have hdiff : ρ τ y - ρ σ y = Real.sqrt (ρβ y) * (movV ρβ ρ τ y - movV ρβ ρ σ y) := by
    rw [s103n_density_split H hρ hτ0 y, s103n_density_split H hρ hσ0 y]; ring
  rw [norm_norm, Real.norm_eq_abs, hdiff, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
  calc Real.sqrt (ρβ y) * |movV ρβ ρ τ y - movV ρβ ρ σ y| ≤ Real.sqrt (ρβ y) *
        (C0 * oscNorm (m : ℝ) (fun z => movV ρβ ρ τ z - movV ρβ ρ σ z)) :=
      mul_le_mul_of_nonneg_left h1 (Real.sqrt_nonneg _)
    _ = _ := by ring

theorem s103n_u2dec_smul {k : ℕ} {L A : ℝ} {f : Euc d → ℝ} (hf : U2Dec k L A f) (c : ℝ) :
    U2Dec k L (|c| * A) (fun y => c * f y) := by
  refine ⟨contDiff_const.mul hf.1, fun m hm y => ?_⟩
  have e : (fun y => c * f y) = c • f := by funext y; simp
  rw [e, iteratedFDeriv_const_smul_apply (hf.1.of_le (by exact_mod_cast hm)).contDiffAt, norm_smul,
    Real.norm_eq_abs]
  calc |c| * ‖iteratedFDeriv ℝ m f y‖ ≤ |c| * (A * u2Wt L y) :=
        mul_le_mul_of_nonneg_left (hf.2 m hm y) (abs_nonneg _)
    _ = _ := by ring

theorem s103n_ultK_smul (hd : 1 ≤ d) {κ : Euc d → ℝ} {s : ℝ} (hK : UlKer κ s) {L A : ℝ}
    (hL : (d : ℝ) < L) (hA : 0 ≤ A) {g : Euc d → ℝ} (hg : U2Dec 1 L A g) (c : ℝ) (x : Euc d) :
    ultK κ (fun y => c * g y) x = c * ultK κ g x := by
  obtain ⟨hn, hf⟩ := ult_K_integrable hd hK hL hA hg x
  have := ult_K_clm (c • ContinuousLinearMap.id ℝ ℝ) κ g x hn hf
  simpa using this.symm

set_option maxHeartbeats 3200000 in
theorem s103n_ultK_hasDeriv (hd : 1 ≤ d) {κ : Euc d → ℝ} {s : ℝ} (hK : UlKer κ s) {L Aρ Ad Bw : ℝ}
    (hL : (d : ℝ) < L) (hAρ : 0 ≤ Aρ) (hAd : 0 ≤ Ad)
    (ρ ρ' : ℝ → Euc d → ℝ) (t : ℝ) (ht : 0 ≤ t)
    (hρ : ∀ τ, 0 ≤ τ → U2Dec 1 L Aρ (ρ τ)) (hρ' : ∀ τ, 0 ≤ τ → U2Dec 1 L Ad (ρ' τ))
    (hder : ∀ τ, 0 ≤ τ → ∀ y, HasDerivWithinAt (fun σ => ρ σ y) (ρ' τ y) (Set.Ici τ) τ)
    (hcont : ∀ y, ContinuousOn (fun τ => ρ τ y) (Set.Ici 0))
    (w : Euc d → ℝ) (hw : Bd 1 Bw w) (x : Euc d) :
    HasDerivWithinAt (fun τ => ultK κ (fun y => ρ τ y * w y) x)
      (ultK κ (fun y => ρ' t y * w y) x) (Set.Ici t) t := by
  have hBw : 0 ≤ Bw := hw.nonneg
  have hL0 : 0 ≤ L := by
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  have hwj : ∀ i ≤ 1, ∀ y, ‖iteratedFDeriv ℝ i w y‖ ≤ Bw := hw.2
  have hfU : ∀ τ, 0 ≤ τ → U2Dec 1 L (Aρ * Bw * 2 ^ 1) (fun y => ρ τ y * w y) := fun τ hτ =>
    who_u2dec_mul (hρ τ hτ) hw.1 hwj
  have hwlip : ∀ a b, |w a - w b| ≤ Bw * ‖a - b‖ := by
    intro a b
    have := ult_lip_of_fderiv (hw.1.differentiable one_ne_zero) (B := Bw) (fun y => by
      have := hw.2 1 le_rfl y
      rwa [norm_iteratedFDeriv_one] at this) a b
    simpa [Real.norm_eq_abs] using this
  -- mean value inequalities for the right derivative
  have mv1 : ∀ τ, t < τ → ∀ y, |ρ τ y - ρ t y| ≤ Ad * u2Wt L y * (τ - t) := by
    intro τ hτ y
    have := norm_image_sub_le_of_norm_deriv_right_le_segment (f := fun σ => ρ σ y)
      (f' := fun σ => ρ' σ y) (C := Ad * u2Wt L y) (a := t) (b := τ)
      ((hcont y).mono (fun σ hσ => le_trans ht hσ.1)) (fun σ hσ => hder σ (ht.trans hσ.1) y)
      (fun σ hσ => by
        have h0 := (hρ' σ (ht.trans hσ.1)).2 0 (Nat.zero_le _) y
        rwa [norm_iteratedFDeriv_zero] at h0) τ ⟨hτ.le, le_rfl⟩
    simpa [Real.norm_eq_abs] using this
  have mv2 : ∀ τ, t < τ → ∀ a b, |(ρ τ a - ρ t a) - (ρ τ b - ρ t b)| ≤ Ad * ‖a - b‖ * (τ - t) := by
    intro τ hτ a b
    have := norm_image_sub_le_of_norm_deriv_right_le_segment (f := fun σ => ρ σ a - ρ σ b)
      (f' := fun σ => ρ' σ a - ρ' σ b) (C := Ad * ‖a - b‖) (a := t) (b := τ)
      (((hcont a).sub (hcont b)).mono (fun σ hσ => le_trans ht hσ.1))
      (fun σ hσ => (hder σ (ht.trans hσ.1) a).sub (hder σ (ht.trans hσ.1) b))
      (fun σ hσ => by
        have := ult_lip0 hL0 hAd (hρ' σ (ht.trans hσ.1)) a b
        simpa [Real.norm_eq_abs] using this) τ ⟨hτ.le, le_rfl⟩
    have e : (ρ τ a - ρ τ b) - (ρ t a - ρ t b) = (ρ τ a - ρ t a) - (ρ τ b - ρ t b) := by ring
    simpa [Real.norm_eq_abs, e] using this
  -- the difference quotients
  set u : ℝ → Euc d → ℝ := fun τ y => (τ - t)⁻¹ * (ρ τ y * w y - ρ t y * w y) with hu
  have hpos : ∀ᶠ τ in 𝓝[>] t, t < τ := self_mem_nhdsWithin
  have hdom : ∀ τ, t < τ → ∀ y, ‖u τ y‖ ≤ (Ad * Bw) * u2Wt L y := by
    intro τ hτ y
    have hτt : 0 < τ - t := sub_pos.2 hτ
    have e : u τ y = (τ - t)⁻¹ * ((ρ τ y - ρ t y) * w y) := by simp only [hu]; ring
    rw [e, Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (inv_pos.2 hτt)]
    have h1 := mv1 τ hτ y
    have h2 := hw.2 0 (Nat.zero_le _) y
    rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at h2
    have hW := (u2Wt_pos (d := d) L y).le
    calc (τ - t)⁻¹ * (|ρ τ y - ρ t y| * |w y|) ≤ (τ - t)⁻¹ * ((Ad * u2Wt L y * (τ - t)) * Bw) :=
          mul_le_mul_of_nonneg_left (mul_le_mul h1 h2 (abs_nonneg _) (by positivity)) (inv_pos.2 hτt).le
      _ = (Ad * Bw) * u2Wt L y := by field_simp
  have hlip : ∀ τ, t < τ → ∀ a b, ‖u τ a - u τ b‖ ≤ (2 * Ad * Bw) * ‖a - b‖ := by
    intro τ hτ a b
    have hτt : 0 < τ - t := sub_pos.2 hτ
    have e : u τ a - u τ b = (τ - t)⁻¹ * (((ρ τ a - ρ t a) - (ρ τ b - ρ t b)) * w a +
        (ρ τ b - ρ t b) * (w a - w b)) := by simp only [hu]; ring
    rw [e, Real.norm_eq_abs, abs_mul, abs_of_pos (inv_pos.2 hτt)]
    have h1 := mv2 τ hτ a b
    have h2 := hw.2 0 (Nat.zero_le _) a
    rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at h2
    have h3 := mv1 τ hτ b
    have h4 := hwlip a b
    have hW : u2Wt (d := d) L b ≤ 1 := u2Wt_le_one hL0 b
    have hn : 0 ≤ ‖a - b‖ := norm_nonneg _
    have hA1 : |((ρ τ a - ρ t a) - (ρ τ b - ρ t b)) * w a| ≤ (Ad * ‖a - b‖ * (τ - t)) * Bw := by
      rw [abs_mul]; exact mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
    have hA2 : |(ρ τ b - ρ t b) * (w a - w b)| ≤ (Ad * 1 * (τ - t)) * (Bw * ‖a - b‖) := by
      rw [abs_mul]
      refine mul_le_mul ?_ h4 (abs_nonneg _) (by positivity)
      refine h3.trans ?_
      have := mul_le_mul_of_nonneg_left hW hAd
      nlinarith
    calc (τ - t)⁻¹ * |((ρ τ a - ρ t a) - (ρ τ b - ρ t b)) * w a + (ρ τ b - ρ t b) * (w a - w b)|
        ≤ (τ - t)⁻¹ * (((Ad * ‖a - b‖ * (τ - t)) * Bw) + ((Ad * 1 * (τ - t)) * (Bw * ‖a - b‖))) :=
          mul_le_mul_of_nonneg_left ((abs_add_le _ _).trans (add_le_add hA1 hA2)) (inv_pos.2 hτt).le
      _ = (2 * Ad * Bw) * ‖a - b‖ := by field_simp; ring
  have hlimy : ∀ y, Tendsto (fun τ => u τ y) (𝓝[>] t) (𝓝 (ρ' t y * w y)) := by
    intro y
    have h1 := (hasDerivWithinAt_iff_tendsto_slope' (s := Set.Ioi t) (by simp)).1
      ((hasDerivWithinAt_Ioi_iff_Ici.2 (hder t ht y)))
    have h2 := h1.mul_const (w y)
    refine h2.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with τ hτ
    simp only [slope_def_field, hu, smul_eq_mul]
    ring
  have hcu : ∀ τ, t < τ → Continuous (u τ) := fun τ hτ => by
    have h1 := (hfU τ (ht.trans hτ.le)).1.continuous
    have h2 := (hfU t ht).1.continuous
    exact continuous_const.mul (h1.sub h2)
  have hT := s103n_ultK_tendsto hd hK hL (mul_nonneg hAd hBw) (by positivity : 0 ≤ 2 * Ad * Bw)
    (l := 𝓝[>] t) u (fun y => ρ' t y * w y) x
    (by filter_upwards [hpos] with τ hτ using hcu τ hτ)
    (by filter_upwards [hpos] with τ hτ using hlip τ hτ)
    (by filter_upwards [hpos] with τ hτ using fun y => hdom τ hτ y) hlimy
  -- relate to the slope
  rw [← hasDerivWithinAt_Ioi_iff_Ici, hasDerivWithinAt_iff_tendsto_slope' (by simp)]
  refine hT.congr' ?_
  filter_upwards [hpos] with τ hτ
  have hτ0 : 0 ≤ τ := ht.trans hτ.le
  have e : u τ = fun y => (τ - t)⁻¹ * (ρ τ y * w y) - (τ - t)⁻¹ * (ρ t y * w y) := by
    funext y; simp only [hu]; ring
  have hc1 := s103n_u2dec_smul (hfU τ hτ0) (τ - t)⁻¹
  have hc2 := s103n_u2dec_smul (hfU t ht) (τ - t)⁻¹
  rw [e, ult_K_sub hd hK hL (by positivity) (by positivity) hc1 hc2 x,
    s103n_ultK_smul hd hK hL (by positivity) (hfU τ hτ0) _ x,
    s103n_ultK_smul hd hK hL (by positivity) (hfU t ht) _ x]
  simp only [slope_def_field, smul_eq_mul]
  ring

end HRS.MS.R2WinOrbNL

end
