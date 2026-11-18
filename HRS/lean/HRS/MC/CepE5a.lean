import HRS.MC.CepaDefs

/-!
# Packet CEPE5A: pathwise Yosida-Gronwall estimate (`cep_E5a_pathwise_yosida`)

Deterministic: the noise cancels in the difference `D = Z^m - Z^n`, which is `C¹` with
`D' = -(G_m(Z^m) - G_n(Z^n)) + (F(Z^m) - F(Z^n))`; the Yosida inequality and the Lipschitz bound on `F` give
`(|D|²)' ≤ 2L |D|² + 2(1/m+1/n)|⟨G_m, G_n⟩|`, and Gronwall finishes.
-/

open Set Filter Topology MeasureTheory
open scoped NNReal RealInnerProductSpace

noncomputable section

namespace HRS.MC.CepE5a

open HRS.MC.Cepa

variable {N : ℕ}

theorem cep_E5a_pathwise_yosida_proof {a : ℝ} {J : ℝ → Ch N → Ch N} (hJ : cep_Yosida a N J)
    {F : Ch N → Ch N} {L : ℝ≥0} (hF : LipschitzWith L F) {m n : ℝ} (hm : 0 < m) (hn : 0 < n)
    {z₀ : Ch N} {Zm Zn : ℝ → Ch N} {noise : ℝ → Ch N} (hZm : Continuous Zm) (hZn : Continuous Zn)
    (hm_eq : ∀ t, 0 ≤ t → Zm t = z₀ + (∫ s in (0 : ℝ)..t, (-(m • (Zm s - J m (Zm s))) + F (Zm s))) + noise t)
    (hn_eq : ∀ t, 0 ≤ t → Zn t = z₀ + (∫ s in (0 : ℝ)..t, (-(n • (Zn s - J n (Zn s))) + F (Zn s))) + noise t) :
    ∀ t, 0 ≤ t → ‖Zm t - Zn t‖ ^ 2 ≤ Real.exp (2 * L * t) * (2 * (1 / m + 1 / n)) *
      ∫ s in (0 : ℝ)..t, |inner ℝ (m • (Zm s - J m (Zm s))) (n • (Zn s - J n (Zn s)))| := by
  have hGm : Continuous fun z : Ch N => m • (z - J m z) := (hJ.lip m hm).continuous
  have hGn : Continuous fun z : Ch N => n • (z - J n z) := (hJ.lip n hn).continuous
  have hFc : Continuous F := hF.continuous
  set Gm : ℝ → Ch N := fun s => m • (Zm s - J m (Zm s)) with hGm_def
  set Gn : ℝ → Ch N := fun s => n • (Zn s - J n (Zn s)) with hGn_def
  have hGmc : Continuous Gm := hGm.comp hZm
  have hGnc : Continuous Gn := hGn.comp hZn
  have hFm : Continuous fun s => F (Zm s) := hFc.comp hZm
  have hFn : Continuous fun s => F (Zn s) := hFc.comp hZn
  set g : ℝ → Ch N := fun s => (-(Gm s) + F (Zm s)) - (-(Gn s) + F (Zn s)) with hg_def
  have hgc : Continuous g := ((hGmc.neg.add hFm).sub (hGnc.neg.add hFn))
  set D : ℝ → Ch N := fun t => ∫ s in (0 : ℝ)..t, g s with hD_def
  have hDeq : ∀ t, 0 ≤ t → Zm t - Zn t = D t := by
    intro t ht
    have h1 : IntervalIntegrable (fun s => -(Gm s) + F (Zm s)) volume 0 t :=
      (hGmc.neg.add hFm).intervalIntegrable _ _
    have h2 : IntervalIntegrable (fun s => -(Gn s) + F (Zn s)) volume 0 t :=
      (hGnc.neg.add hFn).intervalIntegrable _ _
    simp only [hD_def, hg_def]
    rw [intervalIntegral.integral_sub h1 h2, hm_eq t ht, hn_eq t ht]
    abel
  have hDd : ∀ t, HasDerivAt D (g t) t := fun t => (hgc.integral_hasStrictDerivAt 0 t).hasDerivAt
  set c : ℝ → ℝ := fun s => 2 * (1 / m + 1 / n) * |inner ℝ (Gm s) (Gn s)| with hc_def
  have hcc : Continuous c := by
    simp only [hc_def]
    exact continuous_const.mul (hGmc.inner hGnc).abs
  set h : ℝ → ℝ := fun t => ‖D t‖ ^ 2 with hh_def
  have hhd : ∀ t, HasDerivAt h (2 * inner ℝ (D t) (g t)) t := fun t => (hDd t).norm_sq
  have hLn : (0 : ℝ) ≤ L := L.2
  -- key differential inequality for t ≥ 0
  have hkey : ∀ t, 0 ≤ t → 2 * inner ℝ (D t) (g t) ≤ 2 * L * h t + c t := by
    intro t ht
    have hDt := hDeq t ht
    have hy := hJ.yosida m n (Zm t) (Zn t) hm hn
    have hsplit : g t = -(Gm t - Gn t) + (F (Zm t) - F (Zn t)) := by
      simp only [hg_def]; abel
    have hI1 : inner ℝ (D t) (-(Gm t - Gn t)) ≤ (1 / m + 1 / n) * inner ℝ (Gm t) (Gn t) := by
      rw [inner_neg_right, real_inner_comm, ← hDt]
      have : inner ℝ (Gm t - Gn t) (Zm t - Zn t) = inner ℝ (m • (Zm t - J m (Zm t)) - n • (Zn t - J n (Zn t))) (Zm t - Zn t) := rfl
      rw [this]
      linarith
    have hI2 : inner ℝ (D t) (F (Zm t) - F (Zn t)) ≤ L * h t := by
      calc inner ℝ (D t) (F (Zm t) - F (Zn t)) ≤ ‖D t‖ * ‖F (Zm t) - F (Zn t)‖ := real_inner_le_norm _ _
        _ ≤ ‖D t‖ * (L * ‖Zm t - Zn t‖) := by
            gcongr
            rw [← dist_eq_norm, ← dist_eq_norm]
            exact hF.dist_le_mul _ _
        _ = L * h t := by rw [← hDt]; simp only [hh_def, ← hDt]; ring
    have hI3 : (1 / m + 1 / n) * inner ℝ (Gm t) (Gn t) ≤ (1 / m + 1 / n) * |inner ℝ (Gm t) (Gn t)| := by
      exact mul_le_mul_of_nonneg_left (le_abs_self _) (by positivity)
    rw [hsplit, inner_add_right]
    simp only [hc_def]
    nlinarith [hI1, hI2, hI3]
  set k : ℝ → ℝ := fun t => Real.exp (-(2 * L * t)) * h t - ∫ s in (0 : ℝ)..t, c s with hk_def
  have hkd : ∀ t, HasDerivAt k (Real.exp (-(2 * L * t)) * (2 * inner ℝ (D t) (g t) - 2 * L * h t) - c t) t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => Real.exp (-(2 * L * t))) (Real.exp (-(2 * L * t)) * (-(2 * L))) t := by
      have := ((hasDerivAt_id t).const_mul (2 * (L : ℝ))).neg.exp
      simpa using this
    have h2 := h1.mul (hhd t)
    have h3 : HasDerivAt (fun t => ∫ s in (0 : ℝ)..t, c s) (c t) t :=
      (hcc.integral_hasStrictDerivAt 0 t).hasDerivAt
    have h4 := h2.sub h3
    convert h4 using 1
    ring
  have hanti : AntitoneOn k (Ici 0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici 0)
    · exact fun t _ => (hkd t).continuousAt.continuousWithinAt
    · exact fun t _ => (hkd t).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Ici] at ht
      have ht0 : 0 ≤ t := le_of_lt ht
      rw [(hkd t).deriv]
      have hk := hkey t ht0
      have he : Real.exp (-(2 * L * t)) ≤ 1 := by
        apply Real.exp_le_one_iff.mpr
        nlinarith
      have hc0 : 0 ≤ c t := by
        simp only [hc_def]; positivity
      have hep := Real.exp_pos (-(2 * L * t))
      nlinarith
  intro t ht
  have hk0 : k 0 = 0 := by
    simp [hk_def, hh_def, hD_def]
  have hkt : k t ≤ 0 := by
    have := hanti (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr ht) ht
    linarith
  have hkt' : Real.exp (-(2 * L * t)) * h t ≤ ∫ s in (0 : ℝ)..t, c s := by
    simp only [hk_def] at hkt; linarith
  have hct : ∫ s in (0 : ℝ)..t, c s = (2 * (1 / m + 1 / n)) * ∫ s in (0 : ℝ)..t, |inner ℝ (Gm s) (Gn s)| := by
    simp only [hc_def]
    exact intervalIntegral.integral_const_mul _ _
  have hht : h t = ‖Zm t - Zn t‖ ^ 2 := by simp only [hh_def, ← hDeq t ht]
  rw [← hht]
  have hexp : Real.exp (2 * L * t) * Real.exp (-(2 * L * t)) = 1 := by
    rw [← Real.exp_add]; simp
  calc h t = Real.exp (2 * L * t) * (Real.exp (-(2 * L * t)) * h t) := by
        rw [← mul_assoc, hexp, one_mul]
    _ ≤ Real.exp (2 * L * t) * ∫ s in (0 : ℝ)..t, c s := by gcongr
    _ = _ := by rw [hct]; ring

end HRS.MC.CepE5a
