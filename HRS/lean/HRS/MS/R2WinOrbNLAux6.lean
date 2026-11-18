import HRS.MS.R2WinOrbNLAux5

/-!
# S10.3 (nonlinear branch), part 6: data of the orbit tests `φ_α` and of `L_t φ_α` along a small-class trajectory

Prefix `s103n_`, namespace `HRS.MS.R2WinOrbNL`.

* `s103n_phi_in`: the hypotheses of `s103n_P_data` for `u = φ_α` (jets up to order `4d+46` and the `Σ^{8d+82}` norm of `√ρ_β Πφ_α`,
  both `≤ K b_α`), from the explicit-order Schwartz bounds `s103_schwartz_S` and the multiplier theorem `mo_mult_cb`.
* `s103n_g1_data`: `g₁ = L_t φ_α = L_β φ_α + P_t φ_α` satisfies the five data bounds (`C^{4d+43}`, `‖∇g₁‖_{C_b^{4d+42}}`, `‖g₁‖_∞`,
  `‖√ρ_β Πg₁‖_{Σ^{8d+80}}`, all `≤ K₁ b_α`) uniformly in the trajectory and in `t ≥ 0`.
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace

namespace HRS.MS.R2WinOrbNL

open HRS HRS.Whole HRS.MS.BreakdownS67 HRS.MS.Mov63 HRS.MS.MovLin HRS.MS.MovAdj HRS.MS.MovOsc
open HRS.MS.MovForce HRS.MS.MovC2 HRS.MS.R2WinOrb

variable {d : ℕ}

theorem s103n_nstar_le {s : ℝ} (hsd : s < d) (hs0 : 0 ≤ s) :
    s103_nstar d s (8 * d + 82) ≤ 18 * d + 180 := by
  unfold s103_nstar
  have hc : ⌈s + 1⌉₊ ≤ d + 1 := by
    refine Nat.ceil_le.2 ?_
    push_cast; linarith
  have hfl : (⌊((8 * d + 82 : ℕ) : ℝ) + (d : ℝ) / 2⌋₊ : ℝ) ≤ ((8 * d + 82 : ℕ) : ℝ) + (d : ℝ) / 2 :=
    Nat.floor_le (by positivity)
  have hfl' : ⌊((8 * d + 82 : ℕ) : ℝ) + (d : ℝ) / 2⌋₊ ≤ 8 * d + 82 + d / 2 + 1 := by
    have h3 : ((⌊((8 * d + 82 : ℕ) : ℝ) + (d : ℝ) / 2⌋₊ : ℕ) : ℝ) ≤ ((8 * d + 82 + d / 2 + 1 : ℕ) : ℝ) := by
      refine hfl.trans ?_
      push_cast
      have hd2 : (d : ℝ) / 2 ≤ ((d / 2 : ℕ) : ℝ) + 1 := by
        have := Nat.lt_div_mul_add (a := d) (b := 2) (by norm_num)
        have h4 : (d : ℝ) < ((d / 2 : ℕ) : ℝ) * 2 + 2 := by exact_mod_cast this
        linarith
      linarith
    exact_mod_cast h3
  omega

theorem s103n_phi_in {s q β : ℝ} (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hq : 0 < q) (hβ : 0 < β)
    {ρβ : Euc d → ℝ} (hρ : IsThermalEquilibrium d s q β ρβ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ α : MultiIndex d,
      ContDiff ℝ ((4 * d + 46 : ℕ) : WithTop ℕ∞) (oscTestFun ((24 * d + 240 : ℕ) : ℝ) α) ∧
      (∀ l ≤ 4 * d + 46, ∀ x, ‖iteratedFDeriv ℝ l (oscTestFun ((24 * d + 240 : ℕ) : ℝ) α) x‖ ≤
        K * s103_b d α) ∧
      MemOsc ((8 * d + 82 : ℕ) : ℝ) (s67psi ρβ (oscTestFun ((24 * d + 240 : ℕ) : ℝ) α)) ∧
      oscNorm ((8 * d + 82 : ℕ) : ℝ) (s67psi ρβ (oscTestFun ((24 * d + 240 : ℕ) : ℝ) α)) ≤
        K * s103_b d α := by
  obtain ⟨B0, -, hR, -⟩ := HRS.MS.Mov0.mv0_gapref hd hs0 hsd hq hβ hρ
  obtain ⟨hsq, -, cη, hcη, hkη⟩ := HRS.MS.Mov0.mv0_sqrt_gauss_thermal hd hs0 hsd hq hβ hρ
  obtain ⟨φη, hφη⟩ := HRS.MS.MovC1.movc1_G_schwartz
    (⟨hsq, cη, hcη, hkη⟩ : HRS.MS.MovC1.MovcG (fun x => Real.sqrt (ρβ x)))
  have hηm : MemOsc ((8 * d + 82 : ℕ) : ℝ) (fun x => Real.sqrt (ρβ x)) := by
    rw [← hφη]; exact memOsc_schwartz _ φη
  obtain ⟨Cm, hCm0, hCm⟩ := mo_mult_cb (d := d) ((8 * d + 82 : ℕ) : ℝ) (8 * d + 82)
    (le_of_eq (abs_of_nonneg (Nat.cast_nonneg _)))
  set Nη : ℝ := oscNorm ((8 * d + 82 : ℕ) : ℝ) (fun x => Real.sqrt (ρβ x)) with hNη
  have hNη0 : 0 ≤ Nη := Real.sqrt_nonneg _
  obtain ⟨CS, hCS0, hCS⟩ := s103_schwartz_S (d := d) s (8 * d + 82)
  refine ⟨CS * (1 + 2 * Cm * Nη), by positivity, fun α => ?_⟩
  obtain ⟨f, hf⟩ : ∃ f : SchwartzMap (Euc d) ℝ, ⇑f = oscTestFun ((24 * d + 240 : ℕ) : ℝ) α := by
    have hmem : oscTestFun ((24 * d + 240 : ℕ) : ℝ) α ∈ mo_Hspan d := by
      have : oscTestFun ((24 * d + 240 : ℕ) : ℝ) α =
          (oscEigenvalue d α ^ (-(((24 * d + 240 : ℕ) : ℝ) / 2))) • hermiteFunD α := by
        funext x; simp [oscTestFun]
      rw [this]
      exact Submodule.smul_mem _ _ (mova3_hermite_mem α)
    exact mova3c_hspan_schwartz hmem
  rw [← hf]
  set A : ℝ := CS * oscNorm (s103_nstar d s (8 * d + 82) : ℝ) f with hA
  have hA0 : 0 ≤ A := mul_nonneg hCS0 (Real.sqrt_nonneg _)
  have hS := hCS f
  have hSb : ∀ j ≤ 8 * d + 82, ∀ x, ‖iteratedFDeriv ℝ j f x‖ ≤ A := by
    intro j hj x
    refine (hS j hj x).trans ?_
    have hw : 1 ≤ 1 + ‖x‖ := by linarith [norm_nonneg x]
    have hexp : (-(s + 1) - (j : ℝ)) ≤ 0 := by
      have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
      linarith
    have := Real.rpow_le_one_of_one_le_of_nonpos hw hexp
    calc A * (1 + ‖x‖) ^ (-(s + 1) - (j : ℝ)) ≤ A * 1 := mul_le_mul_of_nonneg_left this hA0
      _ = A := mul_one A
  have hAb : A ≤ CS * s103_b d α := by
    refine mul_le_mul_of_nonneg_left ?_ hCS0
    rw [hf, s103_oscNorm_test]
    unfold s103_b
    refine Real.rpow_le_rpow_of_exponent_le (one_le_oscEigenvalue α) ?_
    have h2 : ((s103_nstar d s (8 * d + 82) : ℕ) : ℝ) ≤ ((18 * d + 180 : ℕ) : ℝ) := by
      exact_mod_cast s103n_nstar_le hsd hs0
    linarith
  have hb0 := s103_b_nonneg (d := d) α
  have hKb : A ≤ CS * (1 + 2 * Cm * Nη) * s103_b d α := by
    refine hAb.trans ?_
    have : 0 ≤ 2 * Cm * Nη := by positivity
    nlinarith [mul_nonneg hCS0 hb0, mul_nonneg (mul_nonneg hCS0 hb0) this]
  have hfsm : ContDiff ℝ ∞ f := f.smooth _
  refine ⟨hfsm.of_le (s103_cast_le_infty _), fun l hl x => (hSb l (by omega) x).trans hKb, ?_⟩
  -- the centred function and its multiplier bounds
  set c0 : ℝ := ∫ y, f y * ρβ y with hc0
  have hc0b : |c0| ≤ A := by
    rw [hc0, ← Real.norm_eq_abs]
    have hint : Integrable (fun y => A * ρβ y) := hR.integrable.const_mul A
    have hsup : ∀ x, |f x| ≤ A := fun x => by
      have := hSb 0 (Nat.zero_le _) x
      rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
    calc ‖∫ y, f y * ρβ y‖ ≤ ∫ y, A * ρβ y := by
          refine norm_integral_le_of_norm_le hint (Eventually.of_forall fun y => ?_)
          rw [norm_mul, Real.norm_eq_abs, Real.norm_of_nonneg (hR.pos y).le]
          exact mul_le_mul_of_nonneg_right (hsup y) (hR.pos y).le
      _ = A := by rw [integral_const_mul, hR.integral_one, mul_one]
  have hθsm : ContDiff ℝ ∞ (fun x => f x - c0) := hfsm.sub contDiff_const
  have hθtg : (fun x => f x - c0).HasTemperateGrowth := by
    have := f.hasTemperateGrowth.sub (Function.HasTemperateGrowth.const c0)
    exact this
  have hQ : mova3b2_Q (8 * d + 82) 0 (2 * A) (fun x => f x - c0) := by
    refine mova3b2_Q_of_iter hθsm fun k hk x => ?_
    rw [pow_zero, mul_one]
    rcases Nat.eq_zero_or_pos k with hk0 | hk0
    · subst hk0
      rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs]
      have := hSb 0 (Nat.zero_le _) x
      rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
      calc |f x - c0| ≤ |f x| + |c0| := abs_sub _ _
        _ ≤ 2 * A := by linarith
    · rw [s103_iter_sub_const hfsm c0 (by omega)]
      exact (hSb k hk x).trans (by linarith)
  obtain ⟨hm1, hm2⟩ := hCm (2 * A) (by positivity) _ hθtg hQ _ hηm
  have hpsi : s67psi ρβ f = fun x => (f x - c0) * Real.sqrt (ρβ x) := by
    funext x; unfold s67psi; rw [mul_comm]
  rw [hpsi]
  refine ⟨hm1, hm2.trans ?_⟩
  calc Cm * (2 * A) * Nη = (2 * Cm * Nη) * A := by ring
    _ ≤ (2 * Cm * Nη) * (CS * s103_b d α) := mul_le_mul_of_nonneg_left hAb (by positivity)
    _ ≤ CS * (1 + 2 * Cm * Nη) * s103_b d α := by nlinarith [mul_nonneg hCS0 hb0]

theorem s103n_psi_add {s a β : ℝ} {ρβ : Euc d → ℝ} (H : Mov2dTh d s β a ρβ) {f g : Euc d → ℝ}
    (hfc : Continuous f) (hgc : Continuous g) {Bf Bg : ℝ} (hf : ∀ x, |f x| ≤ Bf) (hg : ∀ x, |g x| ≤ Bg) :
    s67psi ρβ (fun x => f x + g x) = fun x => s67psi ρβ f x + s67psi ρβ g x := by
  have hρ0I : Integrable ρβ volume := by
    by_contra hni
    have h1 := H.hρ.2.1.integral_one
    rw [integral_undef hni] at h1
    exact zero_ne_one h1
  have hI : ∀ {w : Euc d → ℝ} {Bw : ℝ}, Continuous w → (∀ x, |w x| ≤ Bw) → Integrable (fun y => w y * ρβ y) volume :=
    fun {w} {Bw} hw hb => by
      have := hρ0I.mul_bdd hw.aestronglyMeasurable (Filter.Eventually.of_forall fun y => by
        simpa [Real.norm_eq_abs] using hb y)
      exact this.congr (Filter.Eventually.of_forall fun y => by simp [mul_comm])
  funext x
  unfold s67psi
  have : (∫ y, (f y + g y) * ρβ y) = (∫ y, f y * ρβ y) + ∫ y, g y * ρβ y := by
    rw [← integral_add (hI hfc hf) (hI hgc hg)]
    exact integral_congr_ae (Filter.Eventually.of_forall fun y => by ring)
  rw [this]; ring

set_option maxHeartbeats 3200000 in
theorem s103n_g1_data {s a β : ℝ} {ρβ : Euc d → ℝ} (H : Mov2dTh d s β a ρβ) :
    ∃ K1 : ℝ, 0 ≤ K1 ∧ ∀ (r c₁ : ℝ), 0 ≤ r → r ≤ 1 → 0 ≤ c₁ →
      ∀ (f0 : Euc d → ℝ) (ρ : ℝ → Euc d → ℝ),
      MovInSmallClass d s a β ρβ (102 * d + 1020) r c₁ f0 ρ →
      ∀ (t : ℝ), 0 ≤ t → ∀ α : MultiIndex d,
        ContDiff ℝ ((4 * d + 42 + 1 : ℕ) : WithTop ℕ∞)
          (generatorW ((quadraticGradientDyn d s a β).coeff ρ) t (oscTestFun ((24 * d + 240 : ℕ) : ℝ) α)) ∧
        cbNormVecE (4 * d + 42) (fun x => gradient
          (generatorW ((quadraticGradientDyn d s a β).coeff ρ) t (oscTestFun ((24 * d + 240 : ℕ) : ℝ) α)) x) ≤
          ENNReal.ofReal (K1 * s103_b d α) ∧
        (∀ x, |generatorW ((quadraticGradientDyn d s a β).coeff ρ) t
          (oscTestFun ((24 * d + 240 : ℕ) : ℝ) α) x| ≤ K1 * s103_b d α) ∧
        MemOsc ((8 * d + 80 : ℕ) : ℝ) (s67psi ρβ (generatorW ((quadraticGradientDyn d s a β).coeff ρ) t
          (oscTestFun ((24 * d + 240 : ℕ) : ℝ) α))) ∧
        oscNorm ((8 * d + 80 : ℕ) : ℝ) (s67psi ρβ (generatorW ((quadraticGradientDyn d s a β).coeff ρ) t
          (oscTestFun ((24 * d + 240 : ℕ) : ℝ) α))) ≤ K1 * s103_b d α := by
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  obtain ⟨Ks, hKs0, hKs⟩ := s103_data H.hd H.hs0 H.hsd H.hq H.hβ H.hρ
  obtain ⟨Kp, hKp0, hKp⟩ := s103n_phi_in H.hd H.hs0 H.hsd H.hq H.hβ H.hρ
  have hMo : (d : ℝ) / 2 + ((4 * d + 45 : ℕ) : ℝ) + 5 < ((8 * d + 80 : ℕ) : ℝ) := by
    push_cast; linarith
  have hMom : ((8 * d + 80 : ℕ) : ℝ) + 2 + 4 < ((102 * d + 1020 : ℕ) : ℝ) := by
    push_cast; linarith
  obtain ⟨CP, hCP0, hCP⟩ := s103n_P_data H (8 * d + 80) hMo hMom
  set E0 : ℝ := Ks + CP * Kp with hE0
  have hE00 : 0 ≤ E0 := by positivity
  refine ⟨((4 * d + 44 : ℕ) : ℝ) * E0, by positivity, ?_⟩
  intro r c₁ hr0 hr1 hc₁ f0 ρ hρ t ht α
  have hb0 := s103_b_nonneg (d := d) α
  set φ : Euc d → ℝ := oscTestFun ((24 * d + 240 : ℕ) : ℝ) α with hφ
  set Lb : Euc d → ℝ := generatorW ((quadraticGradientDyn d s a β).coeff (fun _ => ρβ)) t φ with hLb
  obtain ⟨h1, h2, h3, h4, h5⟩ := hKs 1 (by norm_num) α
  simp only [Function.iterate_one] at h1 h2 h3 h4 h5
  obtain ⟨hp1, hp2, hp3, hp4⟩ := hKp α
  obtain ⟨hP1, hP2, hP3, hP4⟩ := hCP r c₁ hr0 hr1 hc₁ f0 ρ hρ t ht φ (Kp * s103_b d α)
    (mul_nonneg hKp0 hb0) hp1 hp2 hp3 hp4
  set P : Euc d → ℝ := s103nP d s a β ρβ ρ t φ with hPdef
  have hg : generatorW ((quadraticGradientDyn d s a β).coeff ρ) t φ = fun x => Lb x + P x := by
    funext x; simp only [hLb, hPdef, s103nP]; ring
  rw [hg]
  have hLbsm : ContDiff ℝ ∞ Lb := h1
  have hjLb : ∀ l ≤ 4 * d + 42 + 1, ∀ x, ‖iteratedFDeriv ℝ l Lb x‖ ≤ Ks * s103_b d α := by
    intro l hl x
    rcases Nat.eq_zero_or_pos l with rfl | hl0
    · rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs]; exact h3 x
    · obtain ⟨l', rfl⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by omega⟩
      rw [← s67_norm_iter_grad (hLbsm.of_le (s103_cast_le_infty _) : ContDiff ℝ ((l' + 1 : ℕ) : WithTop ℕ∞) Lb) x]
      exact s67bd66_jet_le (mul_nonneg hKs0 hb0) h2 l' (by omega) x
  have hjg : ∀ l ≤ 4 * d + 42 + 1, ∀ x, ‖iteratedFDeriv ℝ l (fun x => Lb x + P x) x‖ ≤ E0 * s103_b d α := by
    intro l hl x
    have e : (fun x => Lb x + P x) = Lb + P := rfl
    rw [e, iteratedFDeriv_add_apply (hLbsm.of_le (s103_cast_le_infty _)).contDiffAt
      ((hP1.of_le (by exact_mod_cast (by omega : l ≤ 4 * d + 45))).contDiffAt)]
    refine (norm_add_le _ _).trans ?_
    have := hP2 l (by omega) x
    calc ‖iteratedFDeriv ℝ l Lb x‖ + ‖iteratedFDeriv ℝ l P x‖ ≤ Ks * s103_b d α + CP * (Kp * s103_b d α) :=
          add_le_add (hjLb l hl x) this
      _ = E0 * s103_b d α := by rw [hE0]; ring
  have hgsm : ContDiff ℝ ((4 * d + 42 + 1 : ℕ) : WithTop ℕ∞) (fun x => Lb x + P x) :=
    (hLbsm.of_le (s103_cast_le_infty _)).add (hP1.of_le (by exact_mod_cast (by omega : 4 * d + 42 + 1 ≤ 4 * d + 45)))
  have hcbd := s103n_cb_of_jets hgsm hjg
  have hKK : ((4 * d + 42 : ℕ) + 1 : ℝ) * (E0 * s103_b d α) ≤ ((4 * d + 44 : ℕ) : ℝ) * E0 * s103_b d α := by
    push_cast
    nlinarith [mul_nonneg hE00 hb0]
  have hKE : E0 * s103_b d α ≤ ((4 * d + 44 : ℕ) : ℝ) * E0 * s103_b d α := by
    have : (1 : ℝ) ≤ ((4 * d + 44 : ℕ) : ℝ) := by
      have : (1 : ℝ) ≤ ((4 * d + 44 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ 4 * d + 44)
      exact this
    nlinarith [mul_nonneg hE00 hb0]
  -- the weighted part
  have hLbc : Continuous Lb := hLbsm.continuous
  have hPc : Continuous P := hP1.continuous
  have hLb0 : ∀ x, |Lb x| ≤ Ks * s103_b d α := h3
  have hP0 : ∀ x, |P x| ≤ CP * (Kp * s103_b d α) := fun x => by
    have := hP2 0 (Nat.zero_le _) x
    rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
  rw [s103n_psi_add H hLbc hPc hLb0 hP0]
  obtain ⟨hm1, hm2⟩ := HRS.MS.MovC1.movc1_osc_add ((8 * d + 80 : ℕ) : ℝ) h4 hP3
  refine ⟨hgsm, hcbd.trans (ENNReal.ofReal_le_ofReal hKK), fun x => ?_, hm1, ?_⟩
  · refine (abs_add_le _ _).trans ?_
    have := add_le_add (hLb0 x) (hP0 x)
    calc |Lb x| + |P x| ≤ Ks * s103_b d α + CP * (Kp * s103_b d α) := this
      _ = E0 * s103_b d α := by rw [hE0]; ring
      _ ≤ _ := hKE
  · refine hm2.trans ?_
    calc oscNorm ((8 * d + 80 : ℕ) : ℝ) (s67psi ρβ Lb) +
          oscNorm ((8 * d + 80 : ℕ) : ℝ) (s67psi ρβ P) ≤ Ks * s103_b d α + CP * (Kp * s103_b d α) :=
          add_le_add h5 hP4
      _ = E0 * s103_b d α := by rw [hE0]; ring
      _ ≤ _ := hKE

end HRS.MS.R2WinOrbNL

end
