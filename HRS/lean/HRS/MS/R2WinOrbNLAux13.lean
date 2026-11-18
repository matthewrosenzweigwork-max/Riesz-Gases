import HRS.MS.R2WinOrbNLAux12

/-!
# S10.3 (nonlinear branch), part 13: weighted decay classes of the trajectory and of the tests

Prefix `s103n_`, namespace `HRS.MS.R2WinOrbNL`.

* `s103n_u2dec_of_bracket`: the Schwartz-time bounds `⟨x⟩^L ‖D^k f‖ ≤ C` give `U2Dec K L (2^L C) f`.
* `s103n_rho_u2dec`: `ρ_t = ρ_β + (ρ_t - ρ_β)` and `ρ'_t` are in `U2Dec K L` with constants independent of `t` and of the trajectory.
* `s103n_phi_sy`: the partial derivatives of the tests `φ_α` lie in `SyN 2 (n+1) (K b_α)` (`ul6S` bounds with explicit order, `s103_schwartz_S`).
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace

namespace HRS.MS.R2WinOrbNL

open HRS HRS.Whole HRS.MS.BreakdownS67 HRS.MS.MovLin HRS.MS.MovAdj HRS.MS.MovOsc HRS.MS.Ul HRS.MS.Who
  HRS.MS.R2WinOrb

variable {d : ℕ}

theorem s103n_bracket_ge (x : Euc d) : 1 + ‖x‖ ≤ 2 * movBracket x := by
  unfold movBracket
  have h0 : 0 ≤ 1 + ‖x‖ ^ 2 := by positivity
  have : (1 + ‖x‖) / 2 ≤ Real.sqrt (1 + ‖x‖ ^ 2) := by
    apply Real.le_sqrt_of_sq_le
    nlinarith [norm_nonneg x, sq_nonneg (‖x‖ - 1)]
  linarith

theorem s103n_bracket_pow_nonneg (x : Euc d) (L : ℕ) : 0 ≤ movBracket x ^ L :=
  pow_nonneg (by unfold movBracket; exact Real.sqrt_nonneg _) L

theorem s103n_u2dec_of_bracket {K L : ℕ} {f : Euc d → ℝ} (hf : ContDiff ℝ (K : WithTop ℕ∞) f) {C : ℝ}
    (h : ∀ k ≤ K, ∀ x, movBracket x ^ L * ‖iteratedFDeriv ℝ k f x‖ ≤ C) :
    U2Dec K (L : ℝ) (2 ^ L * C) f := by
  refine ⟨hf, fun k hk x => ?_⟩
  have hx : 0 < 1 + ‖x‖ := by linarith [norm_nonneg x]
  have hb : 0 < movBracket x := by unfold movBracket; positivity
  have h1 : (1 + ‖x‖) ^ L ≤ 2 ^ L * movBracket x ^ L := by
    rw [← mul_pow]; exact pow_le_pow_left₀ hx.le (s103n_bracket_ge x) L
  have hw : u2Wt (d := d) (L : ℝ) x = ((1 + ‖x‖) ^ L)⁻¹ := by
    unfold u2Wt; rw [Real.rpow_neg hx.le, Real.rpow_natCast]
  rw [hw]
  have hp : 0 < (1 + ‖x‖) ^ L := by positivity
  rw [← div_eq_mul_inv, le_div_iff₀ hp]
  calc ‖iteratedFDeriv ℝ k f x‖ * (1 + ‖x‖) ^ L ≤ ‖iteratedFDeriv ℝ k f x‖ * (2 ^ L * movBracket x ^ L) :=
        mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
    _ = 2 ^ L * (movBracket x ^ L * ‖iteratedFDeriv ℝ k f x‖) := by ring
    _ ≤ 2 ^ L * C := mul_le_mul_of_nonneg_left (h k hk x) (by positivity)

theorem s103n_rho_u2dec {s a β : ℝ} {ρβ : Euc d → ℝ} (H : Mov2dTh d s β a ρβ) (K L : ℕ) :
    ∃ Aβ : ℝ, 0 ≤ Aβ ∧ ∀ (CKL : ℝ) (ρ ρ' : ℝ → Euc d → ℝ) (t : ℝ), 0 ≤ t →
      ContDiff ℝ (K : WithTop ℕ∞) (ρ t) → ContDiff ℝ (K : WithTop ℕ∞) (ρ' t) →
      (∀ k : ℕ, k ≤ K → ∀ x : Euc d, movBracket x ^ L * (‖iteratedFDeriv ℝ k (fun y => ρ t y - ρβ y) x‖ +
          ‖iteratedFDeriv ℝ k (ρ' t) x‖) ≤ CKL) →
      U2Dec K (L : ℝ) (Aβ + 2 ^ L * CKL) (ρ t) ∧ U2Dec K (L : ℝ) (2 ^ L * CKL) (ρ' t) := by
  obtain ⟨hρsm, hρpos⟩ := mov2d_rho_data H
  obtain ⟨ψρ, hψρ⟩ : ∃ ψ : SchwartzMap (Euc d) ℝ, ⇑ψ = ρβ := by
    obtain ⟨B0, -, hR, -⟩ := HRS.MS.Mov0.mv0_gapref H.hd H.hs0 H.hsd H.hq H.hβ H.hρ
    have hq' : 0 < β * a := mul_pos H.hβ H.hq
    obtain ⟨hρsm', cρ, hcρ, hkρ⟩ := HRS.MS.Mov0.mv0_hgauss_gapref hq' hR
    exact HRS.MS.MovC1.movc1_G_schwartz (⟨hρsm', cρ, hcρ, hkρ⟩ : HRS.MS.MovC1.MovcG ρβ)
  obtain ⟨Aβ, hAβ0, hAβ⟩ := ult_rapid_U2Dec (ult_schwartz_rapid ψρ) K (L : ℝ)
  rw [hψρ] at hAβ
  refine ⟨Aβ, hAβ0, fun CKL ρ ρ' t ht h1 h2 hb => ?_⟩
  have hδ : ContDiff ℝ (K : WithTop ℕ∞) (fun y => ρ t y - ρβ y) :=
    h1.sub (hρsm.of_le (by exact_mod_cast le_top))
  have hCKL : ∀ k ≤ K, ∀ x, movBracket x ^ L * ‖iteratedFDeriv ℝ k (fun y => ρ t y - ρβ y) x‖ ≤ CKL := by
    intro k hk x
    exact le_trans (mul_le_mul_of_nonneg_left
      (le_add_of_nonneg_right (norm_nonneg (iteratedFDeriv ℝ k (ρ' t) x)))
      (s103n_bracket_pow_nonneg x L)) (hb k hk x)
  have hCKL' : ∀ k ≤ K, ∀ x, movBracket x ^ L * ‖iteratedFDeriv ℝ k (ρ' t) x‖ ≤ CKL := by
    intro k hk x
    exact le_trans (mul_le_mul_of_nonneg_left
      (le_add_of_nonneg_left (norm_nonneg (iteratedFDeriv ℝ k (fun y => ρ t y - ρβ y) x)))
      (s103n_bracket_pow_nonneg x L)) (hb k hk x)
  refine ⟨?_, s103n_u2dec_of_bracket h2 hCKL'⟩
  have := who_u2dec_add hAβ (s103n_u2dec_of_bracket hδ hCKL)
  have e : (fun y => ρβ y + (ρ t y - ρβ y)) = ρ t := by funext y; ring
  rw [e] at this
  exact this

theorem s103n_nstar_le84 {s : ℝ} (hsd : s < d) (hs0 : 0 ≤ s) :
    s103_nstar d s (8 * d + 84) ≤ 18 * d + 180 := by
  unfold s103_nstar
  have hc : ⌈s + 1⌉₊ ≤ d + 1 := by
    refine Nat.ceil_le.2 ?_
    push_cast; linarith
  have hfl : (⌊((8 * d + 84 : ℕ) : ℝ) + (d : ℝ) / 2⌋₊ : ℝ) ≤ ((8 * d + 84 : ℕ) : ℝ) + (d : ℝ) / 2 :=
    Nat.floor_le (by positivity)
  have hfl' : ⌊((8 * d + 84 : ℕ) : ℝ) + (d : ℝ) / 2⌋₊ ≤ 8 * d + 84 + d / 2 + 1 := by
    have h3 : ((⌊((8 * d + 84 : ℕ) : ℝ) + (d : ℝ) / 2⌋₊ : ℕ) : ℝ) ≤ ((8 * d + 84 + d / 2 + 1 : ℕ) : ℝ) := by
      refine hfl.trans ?_
      push_cast
      have hd2 : (d : ℝ) / 2 ≤ ((d / 2 : ℕ) : ℝ) + 1 := by
        have := Nat.lt_div_mul_add (a := d) (b := 2) (by norm_num)
        have h4 : (d : ℝ) < ((d / 2 : ℕ) : ℝ) * 2 + 2 := by exact_mod_cast this
        linarith
      linarith
    exact_mod_cast h3
  omega

/-- The partial derivatives of the tests `φ_α` decay like `(1+‖x‖)^{-2}`, with all jets up to order `8d+83` bounded by `K b_α`. -/
theorem s103n_phi_sy {s : ℝ} (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (α : MultiIndex d) (i : Fin d),
      SyN 2 (8 * d + 83) (K * s103_b d α)
        (fun y => fderiv ℝ (oscTestFun ((24 * d + 240 : ℕ) : ℝ) α) y (EuclideanSpace.single i (1 : ℝ))) := by
  obtain ⟨CS, hCS0, hCS⟩ := s103_schwartz_S (d := d) s (8 * d + 84)
  refine ⟨CS, hCS0, fun α i => ?_⟩
  obtain ⟨f, hf⟩ : ∃ f : SchwartzMap (Euc d) ℝ, ⇑f = oscTestFun ((24 * d + 240 : ℕ) : ℝ) α := by
    have hmem : oscTestFun ((24 * d + 240 : ℕ) : ℝ) α ∈ mo_Hspan d := by
      have : oscTestFun ((24 * d + 240 : ℕ) : ℝ) α =
          (oscEigenvalue d α ^ (-(((24 * d + 240 : ℕ) : ℝ) / 2))) • hermiteFunD α := by
        funext x; simp [oscTestFun]
      rw [this]
      exact Submodule.smul_mem _ _ (mova3_hermite_mem α)
    exact mova3c_hspan_schwartz hmem
  rw [← hf]
  set A : ℝ := CS * oscNorm (s103_nstar d s (8 * d + 84) : ℝ) f with hA
  have hA0 : 0 ≤ A := mul_nonneg hCS0 (Real.sqrt_nonneg _)
  have hS := hCS f
  have hAb : A ≤ CS * s103_b d α := by
    refine mul_le_mul_of_nonneg_left ?_ hCS0
    rw [hf, s103_oscNorm_test]
    unfold s103_b
    refine Real.rpow_le_rpow_of_exponent_le (one_le_oscEigenvalue α) ?_
    have h2 : ((s103_nstar d s (8 * d + 84) : ℕ) : ℝ) ≤ ((18 * d + 180 : ℕ) : ℝ) := by
      exact_mod_cast s103n_nstar_le84 hsd hs0
    linarith
  have hfsm : ContDiff ℝ ∞ f := f.smooth _
  set v : Euc d := EuclideanSpace.single i (1 : ℝ) with hv
  have hvn : ‖v‖ = 1 := by simp [hv]
  have hd1 : ContDiff ℝ ((8 * d + 83 : ℕ) : WithTop ℕ∞) (fderiv ℝ f) :=
    (contDiff_infty_iff_fderiv.1 hfsm).2.of_le (s103_cast_le_infty _)
  refine ⟨hd1.clm_apply contDiff_const, fun j hj x => ?_⟩
  have h1 := norm_iteratedFDeriv_clm_apply_const (N := ((8 * d + 83 : ℕ) : WithTop ℕ∞)) (c := v) (n := j)
    hd1.contDiffAt (by exact_mod_cast hj) (x := x)
  rw [norm_iteratedFDeriv_fderiv, hvn, one_mul] at h1
  have h2 := hS (j + 1) (by omega) x
  have hx : 0 < 1 + ‖x‖ := by linarith [norm_nonneg x]
  have hexp : (1 + ‖x‖) ^ (-(s + 1) - ((j + 1 : ℕ) : ℝ)) * (1 + ‖x‖) ^ 2 ≤ 1 := by
    have : ((1 + ‖x‖) ^ (2 : ℕ) : ℝ) = (1 + ‖x‖) ^ ((2 : ℕ) : ℝ) := (Real.rpow_natCast _ 2).symm
    rw [this, ← Real.rpow_add hx]
    apply Real.rpow_le_one_of_one_le_of_nonpos (by linarith [norm_nonneg x])
    push_cast
    have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    linarith
  calc ‖iteratedFDeriv ℝ j (fun y => fderiv ℝ f y v) x‖ * (1 + ‖x‖) ^ 2 ≤
      A * (1 + ‖x‖) ^ (-(s + 1) - ((j + 1 : ℕ) : ℝ)) * (1 + ‖x‖) ^ 2 :=
        mul_le_mul_of_nonneg_right (h1.trans h2) (by positivity)
    _ = A * ((1 + ‖x‖) ^ (-(s + 1) - ((j + 1 : ℕ) : ℝ)) * (1 + ‖x‖) ^ 2) := by ring
    _ ≤ A * 1 := mul_le_mul_of_nonneg_left hexp hA0
    _ ≤ CS * s103_b d α := by linarith

end HRS.MS.R2WinOrbNL

end
