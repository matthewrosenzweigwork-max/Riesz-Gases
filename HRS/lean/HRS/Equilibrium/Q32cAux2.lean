/-
# HRS.Equilibrium.Q32cAux2 -- the rate family inputs of packet Q32c

* a common upper bound `Λ` for every thermal density of `rateV k β θ`, `θ ∈ [a,b]`;
* `rateGibbs = Q_{N,β}(ρ dx)` for a thermal density `ρ` (`canonicalGibbs_eq_modulatedGibbs`);
* `rateVarN = N Var_{P_{N,θ}}[μ_N(cos)]` and the bound on it from the variance input.
-/
import HRS.Equilibrium.Response
import HRS.Equilibrium.Q32cAux1
import HRS.PDE.MeanFieldThermal

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.Q32c

variable {d : ℕ} {s : ℝ}

open HRS

theorem q32c_cosMode_abs_le (k : Lattice d) (x : Torus d) : |Torus.cosMode k x| ≤ 1 := by
  have := Torus.norm_cosMode_le k x
  rwa [Real.norm_eq_abs] at this

theorem q32c_rateV_continuous (k : Lattice d) {β : ℝ} (θ : ℝ) : Continuous (rateV k β θ) := by
  unfold rateV
  exact (continuous_const.mul (Torus.continuous_cosMode k)).div_const β

theorem q32c_rateV_abs_le (k : Lattice d) {β : ℝ} (hβ : 0 < β) (θ : ℝ) (x : Torus d) :
    |rateV k β θ x| ≤ |θ| / β := by
  unfold rateV
  rw [abs_div, abs_mul, abs_neg, abs_of_pos hβ]
  exact div_le_div_of_nonneg_right
    (mul_le_of_le_one_right (abs_nonneg θ) (q32c_cosMode_abs_le k x)) hβ.le

/-- A common upper bound for the thermal densities of `rateV k β θ`, `θ ∈ [a,b]`. -/
theorem q32c_family_upper (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {β : ℝ} (hβ : 0 < β)
    (k : Lattice d) (a b : ℝ) :
    ∃ Λ : ℝ, 1 ≤ Λ ∧ ∀ θ ∈ Set.Icc a b, ∀ ρ : Torus d → ℝ,
      IsThermalDensity (periodicRiesz d s) (rateV k β θ) β ρ → ∀ x, ρ x ≤ Λ := by
  obtain ⟨A, K, hAK⟩ := q32c_thermal_upper (d := d) (s := s) hd hs0 hsd
  set M0 : ℝ := max |a| |b| / β with hM0
  refine ⟨max 1 (Real.exp (β * (M0 + A) + β * (M0 + K))), le_max_left _ _, ?_⟩
  intro θ hθ ρ hρ x
  have hθ' : |θ| ≤ max |a| |b| := by
    rw [abs_le]
    constructor
    · have := neg_abs_le a
      have := le_max_left |a| |b|
      linarith [hθ.1]
    · have := le_abs_self b
      have := le_max_right |a| |b|
      linarith [hθ.2]
  have hVM : ∀ y, |rateV k β θ y| ≤ M0 := fun y =>
    (q32c_rateV_abs_le k hβ θ y).trans (div_le_div_of_nonneg_right hθ' hβ.le)
  exact (hAK (q32c_rateV_continuous k θ) hVM hβ.le hρ x).trans (le_max_right _ _)

/-- `P_{N,θ} = Q_{N,β}(μ_θ)` for a thermal density bounded above. -/
theorem q32c_rateGibbs_eq (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {β : ℝ} (k : Lattice d)
    (θ : ℝ) {ρ : Torus d → ℝ} (hρ : IsThermalDensity (periodicRiesz d s) (rateV k β θ) β ρ)
    {Λ : ℝ} (hΛ : ∀ x, ρ x ≤ Λ) (N : ℕ) :
    rateGibbs d s k β θ N = modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρ) := by
  have hΛ0 : 0 ≤ Λ := (hρ.1.nonneg 0).trans (hΛ 0)
  unfold rateGibbs
  exact canonicalGibbs_eq_modulatedGibbs (periodicRiesz d s) (rateV k β θ) β ρ hρ
    (fun x => periodicRiesz_neg x)
    (fun x => (CoercAux.J_bounds (by omega : 1 ≤ d) hs0 hsd one_pos hρ.1 hΛ0 hΛ x).1)

/-- Exchangeability gives `E[cos(X_i)] = E[cos(X_0)]`. -/
theorem q32c_integral_cos_coord (k : Lattice d) {N : ℕ} (hN : 0 < N) {P : Measure (Config d N)}
    (hP : IsExchangeable P) (i : Fin N) :
    ∫ X, Torus.cosMode k (X i) ∂P = ∫ X, Torus.cosMode k (X ⟨0, hN⟩) ∂P := by
  have h := hP (Equiv.swap (⟨0, hN⟩ : Fin N) i)
  have hm : Measurable (fun X : Config d N => X ∘ (Equiv.swap (⟨0, hN⟩ : Fin N) i)) :=
    (permMeasEquiv _).measurable
  have key : ∫ X, Torus.cosMode k (X ⟨0, hN⟩)
      ∂(P.map (fun X : Config d N => X ∘ (Equiv.swap (⟨0, hN⟩ : Fin N) i))) =
      ∫ X, Torus.cosMode k ((X ∘ (Equiv.swap (⟨0, hN⟩ : Fin N) i)) ⟨0, hN⟩) ∂P :=
    integral_map hm.aemeasurable (f := fun X : Config d N => Torus.cosMode k (X ⟨0, hN⟩))
      ((Torus.continuous_cosMode k).comp (continuous_apply (⟨0, hN⟩ : Fin N))).aestronglyMeasurable
  rw [h] at key
  rw [key]
  simp [Function.comp_def]

/-- `rateVarN = N Var_P[μ_N(cos)]` for an exchangeable probability law `P = P_{N,θ}`. -/
theorem q32c_rateVarN_eq (k : Lattice d) (β : ℝ) (θ : ℝ) {N : ℕ} (hN : 0 < N)
    [IsProbabilityMeasure (rateGibbs d s k β θ N)]
    (hP : IsExchangeable (rateGibbs d s k β θ N)) :
    rateVarN d s k β N θ =
      (N : ℝ) * variance (fun X : Config d N => (1 / (N : ℝ)) * ∑ i, Torus.cosMode k (X i))
        (rateGibbs d s k β θ N) := by
  set P := rateGibbs d s k β θ N with hPdef
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  set F : Config d N → ℝ := fun X => (1 / (N : ℝ)) * ∑ i, Torus.cosMode k (X i) with hF
  have hFc : Continuous F :=
    continuous_const.mul (continuous_finsetSum _ fun i _ =>
      (Torus.continuous_cosMode k).comp (continuous_apply i))
  have hci : ∀ i : Fin N, Integrable (fun X : Config d N => Torus.cosMode k (X i)) P := fun i =>
    Integrable.of_bound ((Torus.continuous_cosMode k).comp (continuous_apply i)).aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun X => by
        rw [Real.norm_eq_abs]; exact q32c_cosMode_abs_le k (X i))
  have hm : rateMeanN d s k β N θ = ∫ X, F X ∂P := by
    unfold rateMeanN
    rw [resp_pair_firstMarginal hN _ (Torus.cosMode k) (Torus.continuous_cosMode k)]
    simp only [hF]
    rw [integral_const_mul, integral_finsetSum _ fun i _ => hci i]
    simp_rw [q32c_integral_cos_coord k hN hP]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
    rfl
  unfold rateVarN
  rw [variance_eq_integral hFc.measurable.aemeasurable, ← hm, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun X => ?_)
  simp only [rateY, hF]
  rw [mul_pow, Real.sq_sqrt hNR.le]

/-- A variance bound `N Var ≤ C'` in terms of `evariance`. -/
theorem q32c_rateVarN_le_of_evariance (k : Lattice d) (β : ℝ) (θ : ℝ) {N : ℕ} (hN : 0 < N)
    [IsProbabilityMeasure (rateGibbs d s k β θ N)]
    (hP : IsExchangeable (rateGibbs d s k β θ N)) {C : ℝ} (hC : 0 ≤ C)
    (h : (N : ℝ≥0∞) * evariance (fun X : Config d N => (1 / (N : ℝ)) * ∑ i, Torus.cosMode k (X i))
        (rateGibbs d s k β θ N) ≤ ENNReal.ofReal C) :
    rateVarN d s k β N θ ≤ C := by
  rw [q32c_rateVarN_eq k β θ hN hP]
  have hFc : Continuous (fun X : Config d N => (1 / (N : ℝ)) * ∑ i, Torus.cosMode k (X i)) :=
    continuous_const.mul (continuous_finsetSum _ fun i _ =>
      (Torus.continuous_cosMode k).comp (continuous_apply i))
  have hmem : MemLp (fun X : Config d N => (1 / (N : ℝ)) * ∑ i, Torus.cosMode k (X i)) 2
      (rateGibbs d s k β θ N) := by
    refine MemLp.of_bound hFc.aestronglyMeasurable 1 (Filter.Eventually.of_forall fun X => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    have hNR : (0 : ℝ) < N := by exact_mod_cast hN
    have h1 : |∑ i, Torus.cosMode k (X i)| ≤ N := by
      calc _ ≤ ∑ i, |Torus.cosMode k (X i)| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _i : Fin N, (1 : ℝ) := Finset.sum_le_sum fun i _ => q32c_cosMode_abs_le k (X i)
        _ = N := by simp
    rw [abs_of_pos (by positivity : (0 : ℝ) < 1 / (N : ℝ))]
    calc 1 / (N : ℝ) * |∑ i, Torus.cosMode k (X i)| ≤ 1 / (N : ℝ) * N :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = 1 := by field_simp
  rw [← hmem.ofReal_variance_eq] at h
  have hv : 0 ≤ variance (fun X : Config d N => (1 / (N : ℝ)) * ∑ i, Torus.cosMode k (X i))
      (rateGibbs d s k β θ N) := variance_nonneg _ _
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg N),
    ENNReal.ofReal_le_ofReal_iff hC] at h
  exact h

/-- `Q_{N,β}(ρ dx)` is a probability measure for `ρ ≤ Λ` (any `N ≥ 1`). -/
theorem q32c_Q_isProb (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {β : ℝ} (hβ : 0 < β) {Λ : ℝ}
    (hΛ1 : 1 ≤ Λ) {ρ : Torus d → ℝ} (hρ : IsProbDensity ρ) (hΛ : ∀ x, ρ x ≤ Λ) {N : ℕ}
    (hN : 0 < N) :
    IsProbabilityMeasure (modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρ)) := by
  obtain ⟨τ, L, M, Ψ, hτ, hτ1, hΨ, -⟩ := q32c_split_params hd hs0 hsd hβ hΛ1
  exact HRS.Quad.riesz_Q_isProb hd hs0 hsd hτ hτ1 L hρ hΛ Ψ hΨ hβ hN

end HRS.Q32c

end
