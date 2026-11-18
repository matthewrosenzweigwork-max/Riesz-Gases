import HRS.Equilibrium.ResponseSubGaussian

/-!
# Packet W4a (namespace `HRS.ME.FamW`): variation lower bound for the rate family

(A) `variation_lower`: for a differentiable `f` with continuous derivative `f'` and `∫_0^R f ≤ 2`,
`f 0 - 2/R ≤ ∫_0^R |f'|`.  Route: some `θN ∈ [0,R]` has `f θN ≤ 2/R` (otherwise the minimum of `f` on
`[0,R]` exceeds `2/R`, forcing `∫_0^R f > 2`); then the fundamental theorem of calculus on `[0,θN]`
and monotonicity of `∫ |f'|` in the interval give the bound.

(B) `integral_rateVarN_le_two`: `∫_0^R rateVarN d s k β N θ dθ ≤ 2` for `N ≥ 2`, via the FTC for
`rateMeanN` (its derivative is `rateVarN`) and `|rateMeanN θ| ≤ 1`.

(C) `rate_variation_lower`: (A) applied to `f = rateVarN`, `f' = √N E[Y_{N,θ}³]` together with (B).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.ME.FamW

open HRS

/-- Lower bound on the total variation of a differentiable function on `[0, R]` with bounded integral. -/
theorem variation_lower {f f' : ℝ → ℝ} (hf : ∀ θ, HasDerivAt f (f' θ) θ) (hf' : Continuous f')
    {R : ℝ} (hR : 0 < R) (hint : ∫ θ in (0:ℝ)..R, f θ ≤ 2) :
    f 0 - 2 / R ≤ ∫ θ in (0:ℝ)..R, |f' θ| := by
  have hfc : Continuous f := continuous_iff_continuousAt.2 fun θ => (hf θ).continuousAt
  have hclaim : ∃ θN ∈ Set.Icc (0:ℝ) R, f θN ≤ 2 / R := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨θ0, hθ0, hmin⟩ := (isCompact_Icc : IsCompact (Set.Icc (0:ℝ) R)).exists_isMinOn
      (Set.nonempty_Icc.2 hR.le) hfc.continuousOn
    have hm : 2 / R < f θ0 := hcon θ0 hθ0
    have hle : ∫ θ in (0:ℝ)..R, f θ0 ≤ ∫ θ in (0:ℝ)..R, f θ :=
      intervalIntegral.integral_mono_on hR.le (continuous_const.intervalIntegrable _ _)
        (hfc.intervalIntegrable _ _) (fun θ hθ => isMinOn_iff.1 hmin θ hθ)
    rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at hle
    have h2 : R * (2 / R) = 2 := by field_simp [hR.ne']
    have h3 := mul_lt_mul_of_pos_left hm hR
    linarith
  obtain ⟨θN, hθN, hfθN⟩ := hclaim
  obtain ⟨h0N, hNR⟩ := hθN
  have hFTC : ∫ y in (0:ℝ)..θN, f' y = f θN - f 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hf x) (hf'.intervalIntegrable _ _)
  have habs : |∫ y in (0:ℝ)..θN, f' y| ≤ ∫ y in (0:ℝ)..θN, |f' y| :=
    intervalIntegral.abs_integral_le_integral_abs h0N
  have hmono : ∫ y in (0:ℝ)..θN, |f' y| ≤ ∫ y in (0:ℝ)..R, |f' y| :=
    intervalIntegral.integral_mono_interval le_rfl h0N hNR
      (Filter.Eventually.of_forall fun x => abs_nonneg (f' x)) (hf'.abs.intervalIntegrable _ _)
  have hneg : -(∫ y in (0:ℝ)..θN, f' y) ≤ |∫ y in (0:ℝ)..θN, f' y| := neg_le_abs _
  linarith

/-- `|M_N(θ)| ≤ 1` for the rate family (`N ≥ 2`). -/
theorem rateMeanN_abs_le_one {d : ℕ} {s : ℝ} (hd : 2 ≤ d) (hs : (d : ℝ) / 2 ≤ s) (hsd : s < d)
    {β : ℝ} (hβ : 0 < β) (k : Lattice d) {N : ℕ} (hN : 2 ≤ N) (θ : ℝ) :
    |rateMeanN d s k β N θ| ≤ 1 := by
  have hs0 : 0 < s := by
    have h1 : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  obtain ⟨gm, hgm, c, hc, hgc, hgm_ae⟩ := resp_good_kernel hd hs0 hsd
  have hN0 : 0 < N := by omega
  haveI := q32d_isProb gm hgm hgm_ae hβ hc hgc hN0 k θ
  exact q32d_mean_abs_le gm hgm hgm_ae hβ hc hgc hN0 k θ

/-- **(B)** `∫_0^R rateVarN = M_N(R) - M_N(0) ≤ 2`. -/
theorem integral_rateVarN_le_two {d : ℕ} {s : ℝ} (hd : 2 ≤ d) (hs : (d : ℝ) / 2 ≤ s) (hsd : s < d)
    {β : ℝ} (hβ : 0 < β) (k : Lattice d) (hk : k ≠ 0) {N : ℕ} (hN : 2 ≤ N) {R : ℝ} (hR : 0 ≤ R) :
    ∫ θ in (0:ℝ)..R, rateVarN d s k β N θ ≤ 2 := by
  obtain ⟨_, hcV, hM, _⟩ := finite_response_rates hd hs hsd β hβ k hk N hN
  have hFTC : ∫ θ in (0:ℝ)..R, rateVarN d s k β N θ =
      rateMeanN d s k β N R - rateMeanN d s k β N 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hM x)
      (hcV.continuous.intervalIntegrable _ _)
  rw [hFTC]
  have h1 := abs_le.1 (rateMeanN_abs_le_one hd hs hsd hβ k hN R)
  have h0 := abs_le.1 (rateMeanN_abs_le_one hd hs hsd hβ k hN 0)
  linarith [h1.2, h0.1]

/-- **(C)** Lower bound on the integrated size of the rate-family variance derivative:
`C_N(0) - 2/R ≤ ∫_0^R |√N E[Y_{N,θ}³]| dθ`. -/
theorem rate_variation_lower {d : ℕ} {s : ℝ} (hd : 2 ≤ d) (hs : (d : ℝ) / 2 ≤ s) (hsd : s < d)
    {β : ℝ} (hβ : 0 < β) (k : Lattice d) (hk : k ≠ 0) {N : ℕ} (hN : 2 ≤ N) {R : ℝ} (hR : 0 < R) :
    rateVarN d s k β N 0 - 2 / R ≤
      ∫ θ in (0:ℝ)..R, |Real.sqrt N * ∫ X, rateY d s k β N θ X ^ 3 ∂(rateGibbs d s k β θ N)| := by
  obtain ⟨_, hcV, _, hV⟩ := finite_response_rates hd hs hsd β hβ k hk N hN
  have hder : (fun θ : ℝ => Real.sqrt N * ∫ X, rateY d s k β N θ X ^ 3 ∂(rateGibbs d s k β θ N)) =
      deriv (rateVarN d s k β N) :=
    funext fun θ => (hV θ).deriv.symm
  have hcont : Continuous (fun θ : ℝ => Real.sqrt N * ∫ X, rateY d s k β N θ X ^ 3 ∂(rateGibbs d s k β θ N)) := by
    rw [hder]
    exact hcV.continuous_deriv (by norm_num)
  have hA := variation_lower (f := rateVarN d s k β N)
    (f' := fun θ : ℝ => Real.sqrt N * ∫ X, rateY d s k β N θ X ^ 3 ∂(rateGibbs d s k β θ N))
    (fun θ => hV θ) hcont hR (integral_rateVarN_le_two hd hs hsd hβ k hk hN hR.le)
  exact hA

end HRS.ME.FamW
