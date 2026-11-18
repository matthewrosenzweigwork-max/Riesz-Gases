import HRS.MS.R2WinOrbAux12

/-!
# S10.3 (stationary half), part 13: the window tests of the stationary coefficient

Prefix `s103_`, namespace `HRS.MS.R2WinOrb`.  `s103_window_tests`: for the stationary coefficient, the window tests `f_{b,n,α}` are `C_b^k` with
`‖f_{b,n,α}‖_{C_b^k} ≤ C_w (1+n)^{-5/4} b_α`, uniformly in `b ≥ 0`, `n`, `α` (orbit family of `s103_family`, bounds of `s103_orbit_claims`,
cosine coefficient bound of `s103_window_core`).
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R2WinOrb

open HRS HRS.Whole

variable {d : ℕ}

theorem s103_cb_of_E {k : ℕ} {g : Euc d → ℝ} {A : ℝ} (hA : 0 ≤ A) (h : r2CbNormE k g ≤ ENNReal.ofReal A) :
    ∀ j ≤ k, ∀ x, ‖iteratedFDeriv ℝ j g x‖ ≤ A := by
  intro j hj x
  have h1 : ENNReal.ofReal ‖iteratedFDeriv ℝ j g x‖ ≤ ENNReal.ofReal A := by
    refine le_trans ?_ h
    unfold r2CbNormE
    refine le_trans (le_iSup (fun x : Euc d => ENNReal.ofReal ‖iteratedFDeriv ℝ j g x‖) x) ?_
    exact Finset.single_le_sum (f := fun j => ⨆ x : Euc d, ENNReal.ofReal ‖iteratedFDeriv ℝ j g x‖)
      (fun _ _ => zero_le) (Finset.mem_range.2 (Nat.lt_succ_of_le hj))
  exact (ENNReal.ofReal_le_ofReal_iff hA).1 h1

theorem s103_orbit_iter {s q β : ℝ} (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hq : 0 < q) (hβ : 0 < β)
    {ρβ : Euc d → ℝ} (hρ : IsThermalEquilibrium d s q β ρβ) :
    ∃ C c : ℝ, 0 ≤ C ∧ 0 < c ∧ ∀ α : MultiIndex d, ∀ t : ℝ, 0 ≤ t → ∀ a : ℕ, a ≤ 2 →
      R2OrbitSup ((quadraticGradientDyn d s q β).coeff (fun _ => ρβ)) (4 * d + 42) t
        ((fun g x => generatorW ((quadraticGradientDyn d s q β).coeff (fun _ => ρβ)) 0 g x)^[a]
          (oscTestFun ((24 * d + 240 : ℕ) : ℝ) α)) (C * s103_b d α) := by
  obtain ⟨C, c, hc, hcl⟩ := s103_orbit_claims hd hs0 hsd hq hβ hρ
  refine ⟨max C 0, c, le_max_right _ _, hc, fun α t ht a ha => ?_⟩
  obtain ⟨s0, g0, s1, g1, s2⟩ := hcl α t ht
  have hb0 := s103_b_nonneg α
  have hm : C * s103_b d α ≤ max C 0 * s103_b d α := mul_le_mul_of_nonneg_right (le_max_left _ _) hb0
  set Cf := (quadraticGradientDyn d s q β).coeff (fun _ => ρβ) with hCf
  set φ := oscTestFun ((24 * d + 240 : ℕ) : ℝ) α with hφ
  interval_cases a
  · exact s103_orbitSup_mono s0 hm
  · exact s103_orbitSup_mono s1 hm
  · have e2 : (fun g x => generatorW Cf 0 g x)^[2] φ = fun x => generatorW Cf t (generatorW Cf t φ) x +
        deriv (fun t' => generatorW Cf t' φ x) t := by
      funext x
      have : (fun t' => generatorW Cf t' φ x) = fun _ => generatorW Cf 0 φ x := rfl
      rw [this, deriv_const]
      simp only [add_zero]
      rfl
    rw [e2]
    exact s103_orbitSup_mono s2 hm

theorem s103_cosBound_mul (T A bα : ℝ) (n : ℕ) :
    s103_cosBound T (A * bα) n = bα * s103_cosBound T A n := by
  unfold s103_cosBound
  split_ifs
  · ring
  · ring

theorem s103_cosBound_arith {T : ℝ} (hT : 0 < T) {Cp : ℝ} (hCp : 0 ≤ Cp) (n : ℕ) :
    (1 + (n : ℝ) ^ 2) ^ ((3 : ℝ) / 8) * s103_cosBound T Cp n ≤
      max (T * (1 / Real.sqrt T) * Cp) (4 * (Real.sqrt (2 / T) * ((2 * Cp + T * Cp) * T ^ 2 / Real.pi ^ 2))) *
        (1 + (n : ℝ)) ^ (-(5 : ℝ) / 4) := by
  by_cases hn : n = 0
  · subst hn
    simp only [s103_cosBound, if_true]
    simp
  · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hn
    have hn0 : (0 : ℝ) < n := by linarith
    simp only [s103_cosBound, hn, if_false]
    have h1 : (1 + (n : ℝ) ^ 2) ^ ((3 : ℝ) / 8) ≤ (1 + (n : ℝ)) ^ ((3 : ℝ) / 4) := by
      calc (1 + (n : ℝ) ^ 2) ^ ((3 : ℝ) / 8) ≤ ((1 + (n : ℝ)) ^ 2) ^ ((3 : ℝ) / 8) :=
            Real.rpow_le_rpow (by positivity) (by nlinarith) (by norm_num)
        _ = (1 + (n : ℝ)) ^ ((3 : ℝ) / 4) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; norm_num
    have hcb : Real.sqrt (2 / T) * ((2 * Cp + T * Cp) / ((n : ℝ) * Real.pi / T) ^ 2) =
        (Real.sqrt (2 / T) * ((2 * Cp + T * Cp) * T ^ 2 / Real.pi ^ 2)) / (n : ℝ) ^ 2 := by
      field_simp
    rw [hcb]
    set K1 : ℝ := Real.sqrt (2 / T) * ((2 * Cp + T * Cp) * T ^ 2 / Real.pi ^ 2) with hK1
    have hK10 : 0 ≤ K1 := by positivity
    have h2 : 1 / (n : ℝ) ^ 2 ≤ 4 * ((1 + (n : ℝ)) ^ (-(2 : ℝ))) := by
      rw [Real.rpow_neg (by positivity), Real.rpow_two]
      have : (1 + (n : ℝ)) ^ 2 ≤ 4 * (n : ℝ) ^ 2 := by nlinarith
      rw [div_le_iff₀ (by positivity)]
      have h3 : 0 < (1 + (n : ℝ)) ^ 2 := by positivity
      calc 1 = ((1 + (n : ℝ)) ^ 2)⁻¹ * (1 + (n : ℝ)) ^ 2 := by field_simp
        _ ≤ ((1 + (n : ℝ)) ^ 2)⁻¹ * (4 * (n : ℝ) ^ 2) := by gcongr
        _ = 4 * ((1 + (n : ℝ)) ^ 2)⁻¹ * (n : ℝ) ^ 2 := by ring
    have h4 : (1 + (n : ℝ)) ^ ((3 : ℝ) / 4) * (1 + (n : ℝ)) ^ (-(2 : ℝ)) = (1 + (n : ℝ)) ^ (-(5 : ℝ) / 4) := by
      rw [← Real.rpow_add (by positivity)]; norm_num
    calc (1 + (n : ℝ) ^ 2) ^ ((3 : ℝ) / 8) * (K1 / (n : ℝ) ^ 2)
        ≤ (1 + (n : ℝ)) ^ ((3 : ℝ) / 4) * (K1 * (4 * (1 + (n : ℝ)) ^ (-(2 : ℝ)))) := by
          rw [div_eq_mul_inv]
          exact mul_le_mul h1 (mul_le_mul_of_nonneg_left (by simpa [one_div] using h2) hK10) (by positivity) (by positivity)
      _ = (4 * K1) * ((1 + (n : ℝ)) ^ ((3 : ℝ) / 4) * (1 + (n : ℝ)) ^ (-(2 : ℝ))) := by ring
      _ = (4 * K1) * (1 + (n : ℝ)) ^ (-(5 : ℝ) / 4) := by rw [h4]
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)

end HRS.MS.R2WinOrb

end
