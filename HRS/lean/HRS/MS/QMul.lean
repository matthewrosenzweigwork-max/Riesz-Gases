import HRS.MS.QMulAux10
import HRS.Prob.Gaussian

/-!
# MS-QMUL: quantitative `C_b^m` multiplier estimate on `H^m(ℝ^d)`

`sobolevNormE_mul_cb_le`: for `θ ∈ C_b^m(ℝ^d)` (not necessarily compactly supported) and every `u`,
`‖θ u‖_{H^m} ≤ C(d,m) · ‖θ‖_{C_b^m} · ‖u‖_{H^m}` (in `ℝ≥0∞`, `⊤` if `u ∉ H^m`).

Route: for a Schwartz function `f` the `H^m` norm is equivalent to `∑_{|α|≤m} ‖∂^α f‖_{L²}`
(Plancherel for coordinate derivatives), Leibniz gives the estimate for `θ f`; a general
`u ∈ H^m` is approximated by Schwartz functions in the weighted Fourier space and the bound passes
to the limit by Fatou's lemma on the Fourier side.
-/

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal ComplexConjugate FourierTransform ContDiff

namespace HRS.MS.QMul
open HRS.PDE.ToolboxRd HRS.PDE.ToolboxRd.FourierAux

variable {d : ℕ}

theorem qm_sobE_zero (s : ℝ) : HRS.Whole.sobolevNormE s (fun _ : Euc d => (0 : ℝ)) = 0 := by
  have h0 : MemLp (fun _ : Euc d => (0 : ℝ)) 2 volume := (MemLp.zero : MemLp (0 : Euc d → ℝ) 2 volume)
  have e0 : ofRealLp h0 = 0 := by
    apply Lp.ext
    filter_upwards [ofRealLp_coe h0, Lp.coeFn_zero ℂ 2 (volume : Measure (Euc d))] with x a b
    rw [a, b]; simp
  have hz : fourierL2 (fun _ : Euc d => (0 : ℝ)) =ᵐ[volume] 0 := by
    rw [fourierL2_eq h0, e0, map_zero]
    exact Lp.coeFn_zero ℂ 2 volume
  have h1 := HRS.MS.UlocMW.um_sobE_sq h0 s
  have h2 : ∫⁻ ξ, ENNReal.ofReal (wt ξ ^ s * ‖fourierL2 (fun _ : Euc d => (0 : ℝ)) ξ‖ ^ 2) = 0 := by
    rw [lintegral_congr_ae (g := fun _ => 0)]
    · simp
    · filter_upwards [hz] with ξ hξ
      rw [hξ]; simp
  rw [h2] at h1
  exact pow_eq_zero_iff (two_ne_zero) |>.1 h1

theorem sobolevNormE_mul_cb_le (d m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ θ : Euc d → ℝ, MemCb m θ → ∀ u : Euc d → ℝ,
      HRS.Whole.sobolevNormE (m : ℝ) (fun x => θ x * u x) ≤
        ENNReal.ofReal (C * HRS.cbNorm m θ) * HRS.Whole.sobolevNormE (m : ℝ) u := by
  obtain ⟨K2, hK2, hmain⟩ := qm_main d m
  refine ⟨Real.sqrt K2 + 1, by positivity, fun θ hθ u => ?_⟩
  set A : ℝ := HRS.cbNorm m θ with hAdef
  have hAj : ∀ j ≤ m, ∀ x, ‖iteratedFDeriv ℝ j θ x‖ ≤ A := by
    intro j hj x
    refine (le_ciSup (hθ.2 j hj) x).trans ?_
    show _ ≤ HRS.cbNorm m θ
    unfold HRS.cbNorm
    exact Finset.single_le_sum (f := fun j => ⨆ z : Euc d, ‖iteratedFDeriv ℝ j θ z‖)
      (fun _ _ => Real.iSup_nonneg fun _ => norm_nonneg _) (Finset.mem_range.2 (Nat.lt_succ_of_le hj))
  have hA0 : 0 ≤ A := (norm_nonneg _).trans (hAj 0 (Nat.zero_le _) 0)
  by_cases hA : A = 0
  · have hθ0 : ∀ x, θ x = 0 := fun x => by
      have := hAj 0 (Nat.zero_le _) x
      rw [hA] at this
      simpa using this
    have : (fun x => θ x * u x) = fun _ => (0 : ℝ) := by funext x; simp [hθ0 x]
    rw [this, qm_sobE_zero]
    exact zero_le
  have hApos : 0 < A := lt_of_le_of_ne hA0 (Ne.symm hA)
  by_cases hu : HRS.PDE.ToolboxRd.MemSobolev (m : ℝ) u
  swap
  · have : HRS.Whole.sobolevNormE (m : ℝ) u = ⊤ := by
      unfold HRS.Whole.sobolevNormE; rw [if_neg hu]
    rw [this, ENNReal.mul_top (by simp; positivity)]
    exact le_top
  have hw : ∫⁻ ξ, ENNReal.ofReal (wt ξ ^ m * ‖fourierL2 u ξ‖ ^ 2) < ⊤ := by
    have := hu.2.lintegral_lt_top
    simp only [Real.rpow_natCast] at this
    exact this
  obtain ⟨hθu, hineq⟩ := hmain θ A hθ.1 hAj u hu.1 hw
  have e1 := HRS.MS.UlocMW.um_sobE_sq hθu (m : ℝ)
  have e0 := HRS.MS.UlocMW.um_sobE_sq hu.1 (m : ℝ)
  simp only [Real.rpow_natCast] at e1 e0
  refine (ENNReal.pow_le_pow_left_iff (n := 2) two_ne_zero).1 ?_
  rw [e1, mul_pow, ← ENNReal.ofReal_pow (by positivity)]
  refine hineq.trans ?_
  rw [e0]
  gcongr
  have h1 : K2 ≤ (Real.sqrt K2 + 1) ^ 2 := by
    nlinarith [Real.sq_sqrt hK2, Real.sqrt_nonneg K2]
  calc K2 * A ^ 2 ≤ (Real.sqrt K2 + 1) ^ 2 * A ^ 2 := mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
    _ = _ := by ring

end HRS.MS.QMul
