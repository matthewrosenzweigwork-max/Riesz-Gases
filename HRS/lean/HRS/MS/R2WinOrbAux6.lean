import HRS.MS.R2WinOrbAux5
import HRS.MS.UlTail
import HRS.MS.MovBridgeAux7
import HRS.MS.TransOpAux23

/-!
# S10.3 (stationary half), part 6: the terminal data `L^a φ_α`, `a ≤ 2`, of the stationary coefficient

Prefix `s103_`, namespace `HRS.MS.R2WinOrb`.

* `s103_coeff_eq`: the stationary coefficient of `quadraticGradientDyn` is a `fixedViscosityCoeff` (`Q = q·1`, `c = -∇g*ρ_β`).
* `s103_data`: with `g_a = L^a φ_α` (`L = generatorW` of the stationary coefficient) and `b_α = λ_α^{(J-m)/2}`: `g_a ∈ C^∞`,
  `‖∇g_a‖_{C_b^k}, ‖g_a‖_∞, ‖√ρ_β Πg_a‖_{Σ^M} ≤ K b_α` (`k = 4d+42`, `M = 8d+80`), by the explicit-order symbol bounds `s103_chain`
  and the multiplier theorem `mo_mult_cb`.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R2WinOrb

open HRS HRS.Whole HRS.MS.MovAdj HRS.MS.Ul HRS.MS.MovOsc

variable {d : ℕ}

theorem s103_cast_le_infty (n : ℕ) : ((n : ℕ) : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) := by
  first | exact WithTop.coe_le_coe.2 le_top | (simp; done) | (norm_cast; done)

theorem s103_iter_sub_const {g : Euc d → ℝ} (hg : ContDiff ℝ ∞ g) (c0 : ℝ) {k : ℕ} (hk : k ≠ 0)
    (x : Euc d) : iteratedFDeriv ℝ k (fun y => g y - c0) x = iteratedFDeriv ℝ k g x := by
  have e : (fun y => g y - c0) = g - fun _ => c0 := rfl
  rw [e, iteratedFDeriv_sub_apply (hg.of_le (s103_cast_le_infty _)).contDiffAt
    (contDiff_const (c := c0)).contDiffAt, iteratedFDeriv_const_of_ne hk]
  simp

theorem s103_coeff_eq (s q β : ℝ) (ρ : Euc d → ℝ) :
    (quadraticGradientDyn d s q β).coeff (fun _ => ρ) =
      fixedViscosityCoeff s (-1) ((q : ℝ) • (1 : Matrix (Fin d) (Fin d) ℝ)) β⁻¹
        (fun x => (fun _ : Euc d => (0 : Euc d)) x - convGradConvW (rieszKernelGrad d s) ρ x) ρ := by
  have hM : ∀ y : Euc d, Torus.matVec (-1 : Matrix (Fin d) (Fin d) ℝ) y = -y := by
    intro y; simp [Torus.matVec]
  have hQ : ∀ y : Euc d, Torus.matVec ((q : ℝ) • (1 : Matrix (Fin d) (Fin d) ℝ)) y = q • y := by
    intro y; simp [Torus.matVec]
  unfold WholeDyn.coeff fixedViscosityCoeff
  congr 1
  funext t x
  unfold meanFieldDriftW
  have e1 : (quadraticGradientDyn d s q β).M = -1 := rfl
  have e2 : (quadraticGradientDyn d s q β).s = s := rfl
  have e3 : gradient (quadraticGradientDyn d s q β).V x = q • x := movtr_gradient_confinement q x
  rw [e1, e2, e3, hM, hQ]
  simp [sub_eq_add_neg]
  abel

theorem s103_data_of_chain {s q β : ℝ} (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hq : 0 < q) (hβ : 0 < β)
    {ρβ : Euc d → ℝ} (hρ : IsThermalEquilibrium d s q β ρβ) :
    ∃ Kd : ℝ, 0 ≤ Kd ∧ ∀ (a : ℕ), a ≤ 2 → ∀ (Ka : ℝ), 0 ≤ Ka →
      (∀ f : SchwartzMap (Euc d) ℝ, ul6S (-(s + 1)) (8 * d + 80)
        (Ka * oscNorm (s103_nstar d s (8 * d + 80 + 2 * a) : ℝ) f)
        ((fun g x => generatorW ((quadraticGradientDyn d s q β).coeff (fun _ => ρβ)) 0 g x)^[a] ⇑f)) →
      ∀ α : MultiIndex d,
        ContDiff ℝ ∞ ((fun g x => generatorW ((quadraticGradientDyn d s q β).coeff (fun _ => ρβ)) 0 g x)^[a]
          (oscTestFun ((24 * d + 240 : ℕ) : ℝ) α)) ∧
        cbNormVecE (4 * d + 42) (fun x => gradient
          ((fun g x => generatorW ((quadraticGradientDyn d s q β).coeff (fun _ => ρβ)) 0 g x)^[a]
            (oscTestFun ((24 * d + 240 : ℕ) : ℝ) α)) x) ≤ ENNReal.ofReal (Kd * Ka * s103_b d α) ∧
        (∀ x, |((fun g x => generatorW ((quadraticGradientDyn d s q β).coeff (fun _ => ρβ)) 0 g x)^[a]
          (oscTestFun ((24 * d + 240 : ℕ) : ℝ) α)) x| ≤ Kd * Ka * s103_b d α) ∧
        MemOsc ((8 * d + 80 : ℕ) : ℝ) (s67psi ρβ ((fun g x => generatorW
          ((quadraticGradientDyn d s q β).coeff (fun _ => ρβ)) 0 g x)^[a] (oscTestFun ((24 * d + 240 : ℕ) : ℝ) α))) ∧
        oscNorm ((8 * d + 80 : ℕ) : ℝ) (s67psi ρβ ((fun g x => generatorW
          ((quadraticGradientDyn d s q β).coeff (fun _ => ρβ)) 0 g x)^[a] (oscTestFun ((24 * d + 240 : ℕ) : ℝ) α))) ≤
          Kd * Ka * s103_b d α := by
  obtain ⟨B0, -, hR, -⟩ := HRS.MS.Mov0.mv0_gapref hd hs0 hsd hq hβ hρ
  have hq' : 0 < β * q := mul_pos hβ hq
  -- Schwartz data of the coefficient
  obtain ⟨hρsm, cρ, hcρ, hkρ⟩ := HRS.MS.Mov0.mv0_hgauss_gapref hq' hR
  obtain ⟨ψρ, hψρ⟩ := HRS.MS.MovC1.movc1_G_schwartz (⟨hρsm, cρ, hcρ, hkρ⟩ : HRS.MS.MovC1.MovcG ρβ)
  have hσ : ∀ i, ∃ ψ : SchwartzMap (Euc d) ℝ, ⇑ψ = fun x => (fun _ : Euc d => (0 : Euc d)) x i :=
    fun i => ⟨0, by ext x; simp⟩
  -- the Gaussian multiplier `√ρ`
  obtain ⟨hsq, -, cη, hcη, hkη⟩ := HRS.MS.Mov0.mv0_sqrt_gauss_thermal hd hs0 hsd hq hβ hρ
  obtain ⟨φη, hφη⟩ := HRS.MS.MovC1.movc1_G_schwartz
    (⟨hsq, cη, hcη, hkη⟩ : HRS.MS.MovC1.MovcG (fun x => Real.sqrt (ρβ x)))
  have hηm : MemOsc ((8 * d + 80 : ℕ) : ℝ) (fun x => Real.sqrt (ρβ x)) := by
    rw [← hφη]; exact memOsc_schwartz _ φη
  obtain ⟨Cm, hCm0, hCm⟩ := mo_mult_cb (d := d) ((8 * d + 80 : ℕ) : ℝ) (8 * d + 80) (le_of_eq (abs_of_nonneg (Nat.cast_nonneg _)))
  set Nη : ℝ := oscNorm ((8 * d + 80 : ℕ) : ℝ) (fun x => Real.sqrt (ρβ x)) with hNη
  have hNη0 : 0 ≤ Nη := Real.sqrt_nonneg _
  refine ⟨((4 * d + 42 : ℕ) + 1 : ℝ) + 1 + 2 * Cm * Nη, by positivity, ?_⟩
  intro a ha Ka hKa0 hchain α
  set Kd : ℝ := ((4 * d + 42 : ℕ) + 1 : ℝ) + 1 + 2 * Cm * Nη with hKd
  have hKd0 : 0 ≤ Kd := by positivity
  -- the Schwartz representative of `φ_α`
  obtain ⟨f, hf⟩ : ∃ f : SchwartzMap (Euc d) ℝ, ⇑f = oscTestFun ((24 * d + 240 : ℕ) : ℝ) α := by
    have hmem : oscTestFun ((24 * d + 240 : ℕ) : ℝ) α ∈ mo_Hspan d := by
      have : oscTestFun ((24 * d + 240 : ℕ) : ℝ) α =
          (oscEigenvalue d α ^ (-(((24 * d + 240 : ℕ) : ℝ) / 2))) • hermiteFunD α := by
        funext x; simp [oscTestFun]
      rw [this]
      exact Submodule.smul_mem _ _ (mova3_hermite_mem α)
    exact mova3c_hspan_schwartz hmem
  rw [← hf]
  set g := (fun g x => generatorW ((quadraticGradientDyn d s q β).coeff (fun _ => ρβ)) 0 g x)^[a] ⇑f with hg
  have hCfeq := s103_coeff_eq s q β ρβ
  have hgfix : g = (fun g x => generatorW (fixedViscosityCoeff s (-1) ((q : ℝ) • (1 : Matrix (Fin d) (Fin d) ℝ))
      β⁻¹ (fun x => (fun _ : Euc d => (0 : Euc d)) x - convGradConvW (rieszKernelGrad d s) ρβ x) ρβ) 0 g x)^[a] ⇑f := by
    rw [hg, hCfeq]
  obtain ⟨hgsm, hgdec, -⟩ := orbitData_decay hd hs0 hsd β⁻¹ ((q : ℝ) • (1 : Matrix (Fin d) (Fin d) ℝ)) ρβ
    ⟨ψρ, hψρ⟩ (fun _ => 0) hσ _ rfl f a
  rw [← hgfix] at hgsm hgdec
  have hS := hchain f
  rw [← hCfeq] at hgfix
  -- the symbol bound
  set A : ℝ := Ka * oscNorm (s103_nstar d s (8 * d + 80 + 2 * a) : ℝ) f with hA
  have hA0 : 0 ≤ A := mul_nonneg hKa0 (Real.sqrt_nonneg _)
  have hSb : ∀ j ≤ 8 * d + 80, ∀ x, ‖iteratedFDeriv ℝ j g x‖ ≤ A := by
    intro j hj x
    refine (hS j hj x).trans ?_
    have hw : 1 ≤ 1 + ‖x‖ := by linarith [norm_nonneg x]
    have hexp : (-(s + 1) - (j : ℝ)) ≤ 0 := by
      have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
      linarith
    have := Real.rpow_le_one_of_one_le_of_nonpos hw hexp
    calc A * (1 + ‖x‖) ^ (-(s + 1) - (j : ℝ)) ≤ A * 1 := mul_le_mul_of_nonneg_left this hA0
      _ = A := mul_one A
  -- the size of `A`
  have hAb : A ≤ Ka * s103_b d α := by
    refine mul_le_mul_of_nonneg_left ?_ hKa0
    rw [hf, s103_oscNorm_test]
    unfold s103_b
    refine Real.rpow_le_rpow_of_exponent_le (one_le_oscEigenvalue α) ?_
    have h1 : s103_nstar d s (8 * d + 80 + 2 * a) ≤ 18 * d + 180 := by
      unfold s103_nstar
      have hc : ⌈s + 1⌉₊ ≤ d + 1 := by
        refine Nat.ceil_le.2 ?_
        push_cast; linarith
      have hfl : (⌊((8 * d + 80 + 2 * a : ℕ) : ℝ) + (d : ℝ) / 2⌋₊ : ℝ) ≤
          ((8 * d + 80 + 2 * a : ℕ) : ℝ) + (d : ℝ) / 2 := Nat.floor_le (by positivity)
      have hfl' : ⌊((8 * d + 80 + 2 * a : ℕ) : ℝ) + (d : ℝ) / 2⌋₊ ≤ 8 * d + 84 + d / 2 + 1 := by
        have h3 : ((⌊((8 * d + 80 + 2 * a : ℕ) : ℝ) + (d : ℝ) / 2⌋₊ : ℕ) : ℝ) ≤
            ((8 * d + 84 + d / 2 + 1 : ℕ) : ℝ) := by
          refine hfl.trans ?_
          push_cast
          have hh : ((a : ℕ) : ℝ) ≤ 2 := by exact_mod_cast ha
          have hd2 : (d : ℝ) / 2 ≤ ((d / 2 : ℕ) : ℝ) + 1 := by
            have := Nat.lt_div_mul_add (a := d) (b := 2) (by norm_num)
            have h4 : (d : ℝ) < ((d / 2 : ℕ) : ℝ) * 2 + 2 := by exact_mod_cast this
            linarith
          linarith
        exact_mod_cast h3
      omega
    have h2 : ((s103_nstar d s (8 * d + 80 + 2 * a) : ℕ) : ℝ) ≤ ((18 * d + 180 : ℕ) : ℝ) := by
      exact_mod_cast h1
    linarith
  -- consequences
  have hcb : cbNormVecE (4 * d + 42) (fun x => gradient g x) ≤ ENNReal.ofReal (((4 * d + 42 : ℕ) + 1 : ℝ) * A) := by
    unfold cbNormVecE
    calc ∑ j ∈ Finset.range (4 * d + 42 + 1), ⨆ x : Euc d, ENNReal.ofReal ‖iteratedFDeriv ℝ j (fun y => gradient g y) x‖
        ≤ ∑ j ∈ Finset.range (4 * d + 42 + 1), ENNReal.ofReal A := by
          refine Finset.sum_le_sum fun j hj => iSup_le fun x => ENNReal.ofReal_le_ofReal ?_
          have hj' : j + 1 ≤ 8 * d + 80 := by have := Finset.mem_range.1 hj; omega
          rw [s67_norm_iter_grad (hgsm.of_le (s103_cast_le_infty _) : ContDiff ℝ ((j + 1 : ℕ) : WithTop ℕ∞) g) x]
          exact hSb (j + 1) hj' x
      _ = ENNReal.ofReal (((4 * d + 42 : ℕ) + 1 : ℝ) * A) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
            ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
          congr 1; push_cast; ring
  have hsup : ∀ x, |g x| ≤ A := by
    intro x
    have := hSb 0 (Nat.zero_le _) x
    rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
  -- the centred function and its multiplier bounds
  set c0 : ℝ := ∫ y, g y * ρβ y with hc0
  have hc0b : |c0| ≤ A := by
    rw [hc0, ← Real.norm_eq_abs]
    have hint : Integrable (fun y => A * ρβ y) := hR.integrable.const_mul A
    calc ‖∫ y, g y * ρβ y‖ ≤ ∫ y, A * ρβ y := by
          refine norm_integral_le_of_norm_le hint (Eventually.of_forall fun y => ?_)
          rw [norm_mul, Real.norm_eq_abs, Real.norm_of_nonneg (hR.pos y).le]
          exact mul_le_mul_of_nonneg_right (hsup y) (hR.pos y).le
      _ = A := by rw [integral_const_mul, hR.integral_one, mul_one]
  have hθsm : ContDiff ℝ ∞ (fun x => g x - c0) := hgsm.sub contDiff_const
  have hθtg : (fun x => g x - c0).HasTemperateGrowth := by
    refine ⟨hθsm, fun n => ?_⟩
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      refine ⟨0, |c0| + A, fun x => ?_⟩
      rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs, pow_zero, mul_one]
      calc |g x - c0| ≤ |g x| + |c0| := abs_sub _ _
        _ ≤ |c0| + A := by linarith [hsup x]
    · obtain ⟨C, -, hC⟩ := hgdec n
      refine ⟨0, C, fun x => ?_⟩
      rw [s103_iter_sub_const hgsm c0 (by omega)]
      simp only [pow_zero, mul_one]
      refine (hC x).trans ?_
      have hw : 1 ≤ 1 + ‖x‖ := by linarith [norm_nonneg x]
      have := Real.rpow_le_one_of_one_le_of_nonpos hw (by
        have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        linarith : -(s + 1 + (n : ℝ)) ≤ 0)
      calc C * (1 + ‖x‖) ^ (-(s + 1 + (n : ℝ))) ≤ C * 1 := by
            refine mul_le_mul_of_nonneg_left this ?_
            exact (by simpa using (hC 0).trans' (by positivity : (0:ℝ) ≤ _) : 0 ≤ C)
        _ = C := mul_one C
  have hQ : mova3b2_Q (8 * d + 80) 0 (2 * A) (fun x => g x - c0) := by
    refine mova3b2_Q_of_iter hθsm fun k hk x => ?_
    rw [pow_zero, mul_one]
    rcases Nat.eq_zero_or_pos k with hk0 | hk0
    · subst hk0
      rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs]
      calc |g x - c0| ≤ |g x| + |c0| := abs_sub _ _
        _ ≤ 2 * A := by linarith [hsup x]
    · rw [s103_iter_sub_const hgsm c0 (by omega)]
      exact (hSb k hk x).trans (by linarith)
  obtain ⟨hm1, hm2⟩ := hCm (2 * A) (by positivity) _ hθtg hQ _ hηm
  have hpsi : s67psi ρβ g = fun x => (g x - c0) * Real.sqrt (ρβ x) := by
    funext x; unfold s67psi; rw [mul_comm]
  rw [hpsi]
  refine ⟨hgsm, ?_, ?_, hm1, ?_⟩
  · refine hcb.trans (ENNReal.ofReal_le_ofReal ?_)
    have : ((4 * d + 42 : ℕ) + 1 : ℝ) * A ≤ Kd * Ka * s103_b d α := by
      calc ((4 * d + 42 : ℕ) + 1 : ℝ) * A ≤ Kd * A := by
            refine mul_le_mul_of_nonneg_right ?_ hA0
            rw [hKd]; nlinarith [mul_nonneg (mul_nonneg hCm0 hNη0) (by norm_num : (0:ℝ) ≤ 2)]
        _ ≤ Kd * (Ka * s103_b d α) := mul_le_mul_of_nonneg_left hAb hKd0
        _ = _ := by ring
    exact this
  · intro x
    refine (hsup x).trans ?_
    calc A ≤ Kd * A := by
          have : 1 ≤ Kd := by
            rw [hKd]; nlinarith [mul_nonneg (mul_nonneg hCm0 hNη0) (by norm_num : (0:ℝ) ≤ 2),
              (Nat.cast_nonneg (4 * d + 42) : (0:ℝ) ≤ ((4 * d + 42 : ℕ) : ℝ))]
          nlinarith
      _ ≤ Kd * (Ka * s103_b d α) := mul_le_mul_of_nonneg_left hAb hKd0
      _ = _ := by ring
  · refine hm2.trans ?_
    calc Cm * (2 * A) * Nη ≤ Kd * A := by
          rw [hKd]; nlinarith [mul_nonneg (mul_nonneg hCm0 hNη0) hA0,
            mul_nonneg (Nat.cast_nonneg (4 * d + 42) : (0:ℝ) ≤ ((4 * d + 42 : ℕ) : ℝ)) hA0]
      _ ≤ Kd * (Ka * s103_b d α) := mul_le_mul_of_nonneg_left hAb hKd0
      _ = _ := by ring

end HRS.MS.R2WinOrb

end
