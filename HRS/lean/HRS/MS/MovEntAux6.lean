import HRS.MS.MovEntAux5

/-!
# S6.6, packet P6 (part 1): regularity and Lipschitz data of the S6.3 trajectories for the S.B.1 hypotheses

* `s66_poly_gauss`: `⟨x⟩^n e^{-c|x|²}` is bounded.
* `s66_isRegular_of_bounds`: weighted derivative bounds `⟨x⟩^{d+3}‖D^k f‖ ≤ B`, `k ≤ 3`, give `IsRegularDensityW 3 Λ f`.
* `s66_lip_of_decay`: the velocity bound of S6.3 gives `HasLipBoundW (mfeTransportW D ρ) K` for `D = quadraticGradientDyn`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MovEnt

open HRS.Whole

variable {d : ℕ}

theorem s66_bracket_le (x : Euc d) : movBracket x ≤ 1 + ‖x‖ := by
  unfold movBracket
  rw [Real.sqrt_le_left (by positivity)]
  nlinarith [norm_nonneg x]

theorem s66_one_le_bracket (x : Euc d) : 1 ≤ movBracket x := by
  unfold movBracket
  rw [Real.one_le_sqrt]
  nlinarith [sq_nonneg ‖x‖]

theorem s66_poly_gauss {c : ℝ} (hc : 0 < c) (n : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x : Euc d, movBracket x ^ n * Real.exp (-c * ‖x‖ ^ 2) ≤ B := by
  refine ⟨(n.factorial : ℝ) * Real.exp (1 + (0 + 1) ^ 2 / (2 * c)), by positivity, fun x => ?_⟩
  have h := HRS.MS.Mov0.mov0_pow_exp_bound (a := 2 * c) (M := 0) (by positivity) n ‖x‖ (norm_nonneg x)
  have h1 : movBracket x ^ n ≤ (1 + ‖x‖) ^ n :=
    pow_le_pow_left₀ (by unfold movBracket; positivity) (s66_bracket_le x) n
  have h2 : Real.exp (-c * ‖x‖ ^ 2) = Real.exp (-(2 * c * ‖x‖ ^ 2 / 2) + 0 * ‖x‖) := by
    congr 1; ring
  calc movBracket x ^ n * Real.exp (-c * ‖x‖ ^ 2)
      ≤ (1 + ‖x‖) ^ n * Real.exp (-c * ‖x‖ ^ 2) :=
        mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    _ = (1 + ‖x‖) ^ n * Real.exp (-(2 * c * ‖x‖ ^ 2 / 2) + 0 * ‖x‖) := by rw [h2]
    _ ≤ (n.factorial : ℝ) * Real.exp (1 + (0 + 1) ^ 2 / (2 * c)) * Real.exp (-(2 * c / 4) * ‖x‖ ^ 2) := h
    _ ≤ (n.factorial : ℝ) * Real.exp (1 + (0 + 1) ^ 2 / (2 * c)) * 1 := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        rw [Real.exp_le_one_iff]
        nlinarith [sq_nonneg ‖x‖]
    _ = _ := mul_one _

theorem s66_partial_le {j : ℕ} (i : Fin j → Fin d) (f : Euc d → ℝ) (x : Euc d) :
    |partialDeriv i f x| ≤ ‖iteratedFDeriv ℝ j f x‖ := by
  unfold partialDeriv
  have h := (iteratedFDeriv ℝ j f x).le_opNorm (fun l => (EuclideanSpace.single (i l) (1 : ℝ) : Euc d))
  have h1 : ∏ l : Fin j, ‖(EuclideanSpace.single (i l) (1 : ℝ) : Euc d)‖ = 1 := by
    simp
  rw [h1, mul_one] at h
  simpa [Real.norm_eq_abs] using h

theorem s66_dse_le {k : ℕ} {w : ℕ → ℝ} {Λ : ℝ} {f : Euc d → ℝ}
    (h : ∀ j ≤ k, ∀ (i : Fin j → Fin d) (x : Euc d), jbracket x ^ w j * |partialDeriv i f x| ≤ Λ) :
    derivSupE k w f ≤ ENNReal.ofReal Λ := by
  unfold derivSupE
  refine iSup_le fun j => iSup_le fun i => iSup_le fun x => ENNReal.ofReal_le_ofReal ?_
  exact h j.1 (by omega) i x

/-- Weighted derivative bounds give `IsRegularDensityW 3 Λ`. -/
theorem s66_isRegular_of_bounds {f : Euc d → ℝ} (hf : ContDiff ℝ 3 f) {B : ℝ}
    (hB : ∀ k : ℕ, k ≤ 3 → ∀ x : Euc d, movBracket x ^ (d + 3) * ‖iteratedFDeriv ℝ k f x‖ ≤ B)
    {Λ : ℝ} (hΛ : 5 * B ≤ Λ) : IsRegularDensityW 3 Λ f := by
  have hB0 : 0 ≤ B := by
    have := hB 0 (by norm_num) 0
    have h1 : 0 ≤ movBracket (0 : Euc d) ^ (d + 3) * ‖iteratedFDeriv ℝ 0 f 0‖ := by
      have := s66_one_le_bracket (0 : Euc d)
      positivity
    linarith
  have hk : ∀ k : ℕ, k ≤ 3 → ∀ x : Euc d, ‖iteratedFDeriv ℝ k f x‖ ≤ B := by
    intro k hk x
    have h1 := hB k hk x
    have h2 : 1 ≤ movBracket x ^ (d + 3) := one_le_pow₀ (s66_one_le_bracket x)
    have h3 : 0 ≤ ‖iteratedFDeriv ℝ k f x‖ := norm_nonneg _
    nlinarith
  refine ⟨hf, ⟨hf, fun j hj => ⟨B, ?_⟩⟩, ?_⟩
  · rintro _ ⟨x, rfl⟩
    exact hk j hj x
  · have hcb : cbNorm 3 f ≤ 4 * B := by
      unfold cbNorm
      calc ∑ j ∈ Finset.range (3 + 1), ⨆ z : Euc d, ‖iteratedFDeriv ℝ j f z‖
          ≤ ∑ j ∈ Finset.range (3 + 1), B := by
            refine Finset.sum_le_sum fun j hj => ?_
            have hj3 : j ≤ 3 := by simpa [Nat.lt_succ_iff] using hj
            exact ciSup_le fun z => hk j hj3 z
        _ = 4 * B := by simp
    have hw : weightedSupE 3 ((d : ℝ) + 3) f ≤ ENNReal.ofReal B := by
      refine s66_dse_le (w := fun _ => (d : ℝ) + 3) ?_
      intro j hj i x
      have h1 : jbracket x ^ ((d : ℝ) + 3) = movBracket x ^ (d + 3) := by
        have : jbracket x = movBracket x := rfl
        rw [this, show ((d : ℝ) + 3) = ((d + 3 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
      show jbracket x ^ ((d : ℝ) + 3) * |partialDeriv i f x| ≤ B
      rw [h1]
      calc movBracket x ^ (d + 3) * |partialDeriv i f x|
          ≤ movBracket x ^ (d + 3) * ‖iteratedFDeriv ℝ j f x‖ :=
            mul_le_mul_of_nonneg_left (s66_partial_le i f x) (by
              have := s66_one_le_bracket x; positivity)
        _ ≤ B := hB j hj x
    calc ENNReal.ofReal (cbNorm 3 f) + weightedSupE 3 ((d : ℝ) + 3) f
        ≤ ENNReal.ofReal (4 * B) + ENNReal.ofReal B := add_le_add (ENNReal.ofReal_le_ofReal hcb) hw
      _ = ENNReal.ofReal (4 * B + B) := (ENNReal.ofReal_add (by positivity) hB0).symm
      _ ≤ ENNReal.ofReal Λ := ENNReal.ofReal_le_ofReal (by linarith)

/-- The transport of the mean-field flow is `movU`. -/
theorem s66_transport_eq (s q β : ℝ) (ρ : Euc d → ℝ) :
    mfeTransportW (quadraticGradientDyn d s q β) ρ = movU d s q β ρ := by
  funext x
  unfold mfeTransportW mfeTransport0W movU movForce
  have hg : gradient (quadraticGradientDyn d s q β).V x = q • x := movtr_gradient_confinement q x
  rw [hg]
  show β⁻¹ • gradient (fun y => Real.log (ρ y)) x + convGradConvW (rieszKernelGrad d s) ρ x + q • x = _
  abel

/-- Lipschitz bound of the velocity from the `C_b^1` norm. -/
theorem s66_lip_of_cb {u : Euc d → Euc d} (hu : ContDiff ℝ 1 u) {K : ℝ} (hK : 0 ≤ K)
    (h : cbNormVecE 1 u ≤ ENNReal.ofReal K) : HasLipBoundW u K := by
  refine ⟨Real.toNNReal K, ?_, by simp [Real.coe_toNNReal K hK]⟩
  refine lipschitzWith_of_nnnorm_fderiv_le (hu.differentiable (by norm_num)) fun x => ?_
  have h1 : ENNReal.ofReal ‖iteratedFDeriv ℝ 1 u x‖ ≤ cbNormVecE 1 u := by
    unfold cbNormVecE
    have hm : 1 ∈ Finset.range (1 + 1) := by simp
    refine le_trans ?_ (Finset.single_le_sum (f := fun j => ⨆ x : Euc d, ENNReal.ofReal ‖iteratedFDeriv ℝ j u x‖)
      (fun _ _ => bot_le) hm)
    exact le_iSup (fun x : Euc d => ENNReal.ofReal ‖iteratedFDeriv ℝ 1 u x‖) x
  have h2 := h1.trans h
  rw [norm_iteratedFDeriv_one] at h2
  have h3 : ‖fderiv ℝ u x‖ ≤ K := (ENNReal.ofReal_le_ofReal_iff hK).1 h2
  rw [← NNReal.coe_le_coe, coe_nnnorm]
  simpa [Real.coe_toNNReal K hK] using h3

end HRS.MS.MovEnt

end
