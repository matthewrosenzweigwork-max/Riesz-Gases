import HRS.MS.MovEntAux2

/-!
# S6.6, packet P3 (part 2): rates, second moment by Donsker-Varadhan, the particle bounds from the entropy bound

* `s66_delta_facts`: `0 < δ_N ≤ 1`, `o_N > 0` and `δ_N ≤ 2 o_N` (`C₀ ≥ 1`, `N ≥ 2`, `0 ≤ s < d`).
* `s66_second_moment`: `E_f N⁻¹∑|x_i|² ≤ c⁻¹(H(f|μ^{⊗N})/N + log E)` from the exponential moment of `μ`.
* `s66_bounds_at`: the four bounds of `MovParticleBounds` (F, product, `e_N`, second moment) for one time from
  `H(f|Q) ≤ C₁ N δ_N`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory InformationTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.MovEnt

open HRS.Whole

local notation "wd" => Whole.withDensityReal

variable {d N : ℕ}

theorem s66_delta_facts (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {C₀ : ℝ} (hC₀ : 1 ≤ C₀)
    (hN : 2 ≤ N) :
    0 < deltaN d s N ∧ deltaN d s N ≤ 1 ∧ 0 < oN d s C₀ N ∧ deltaN d s N ≤ 2 * oN d s C₀ N := by
  have hx : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hx0 : (0 : ℝ) < N := by linarith
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  set x : ℝ := (N : ℝ) with hxdef
  have hpow : 0 < x ^ (s / d - 1) := Real.rpow_pos_of_pos hx0 _
  have hlog : 0 ≤ (if s = 0 then Real.log x / (2 * d * x) else 0) := by
    split_ifs
    · have : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
      positivity
    · exact le_refl _
  have hoN : x ^ (s / d - 1) ≤ oN d s C₀ N := by
    unfold oN
    have : x ^ (s / d - 1) ≤ C₀ * x ^ (s / d - 1) := by nlinarith
    linarith
  have hlogx : Real.log x ≤ x - 1 := Real.log_le_sub_one_of_pos hx0
  unfold deltaN
  split_ifs with h1 h2
  · have hxi : 0 < x⁻¹ := inv_pos.2 hx0
    refine ⟨hxi, inv_le_one_of_one_le₀ (by linarith), by linarith, ?_⟩
    have : x⁻¹ ≤ x ^ (s / d - 1) := by
      rw [← Real.rpow_neg_one]
      exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by
        have : 0 ≤ s / d := div_nonneg hs0 hd0.le
        linarith)
    linarith
  · have hlg : 0 < Real.log (Real.exp 1 * x) := by
      rw [Real.log_mul (Real.exp_pos _).ne' hx0.ne', Real.log_exp]
      have : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
      linarith
    have hxi : 0 < x⁻¹ * Real.log (Real.exp 1 * x) := mul_pos (inv_pos.2 hx0) hlg
    have hrw : Real.log (Real.exp 1 * x) = 1 + Real.log x := by
      rw [Real.log_mul (Real.exp_pos _).ne' hx0.ne', Real.log_exp]
    refine ⟨hxi, ?_, by linarith, ?_⟩
    · rw [hrw, inv_mul_le_iff₀ hx0]; linarith
    · -- x⁻¹ (1 + log x) ≤ 2 x^{-1/2}
      have hσ : s / d = 1 / 2 := by rw [h2]; field_simp
      have hr : x ^ (s / d - 1) = (Real.sqrt x)⁻¹ := by
        rw [hσ, Real.sqrt_eq_rpow, ← Real.rpow_neg_one, ← Real.rpow_mul hx0.le]
        norm_num
      rw [hr] at hoN
      set r := Real.sqrt x with hrdef
      have hr0 : 0 < r := Real.sqrt_pos.2 hx0
      have hrr : r * r = x := Real.mul_self_sqrt hx0.le
      have hlog2 : Real.log x ≤ 2 * (r - 1) := by
        have : Real.log r ≤ r - 1 := Real.log_le_sub_one_of_pos hr0
        have e : Real.log x = 2 * Real.log r := by
          rw [← hrr, Real.log_mul hr0.ne' hr0.ne']; ring
        linarith
      rw [hrw]
      have h3 : x⁻¹ * (1 + Real.log x) ≤ x⁻¹ * (2 * r) := by
        apply mul_le_mul_of_nonneg_left _ (inv_nonneg.2 hx0.le); linarith
      have h4 : x⁻¹ * (2 * r) = 2 * r⁻¹ := by
        rw [← hrr]; field_simp
      linarith
  · have hspos : 0 < s := by
      have : (0 : ℝ) < (d : ℝ) / 2 := by positivity
      push Not at h1
      linarith
    have hσ0 : 0 < s / d := div_pos hspos hd0
    have hp : 1 < (d : ℝ) / s := by rw [lt_div_iff₀ hspos]; linarith
    have hpos : 0 < x ^ (1 - (d : ℝ) / s) := Real.rpow_pos_of_pos hx0 _
    refine ⟨hpos, Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith), by linarith, ?_⟩
    have hexp : 1 - (d : ℝ) / s ≤ s / d - 1 := by
      have hq : (d : ℝ) / s = (s / d)⁻¹ := by rw [inv_div]
      rw [hq]
      set σ := s / d
      have : 2 ≤ σ + σ⁻¹ := by
        have h0 : 0 ≤ (σ - 1) ^ 2 / σ := by positivity
        have e : (σ - 1) ^ 2 / σ = σ + σ⁻¹ - 2 := by field_simp; ring
        linarith
      linarith
    have : x ^ (1 - (d : ℝ) / s) ≤ x ^ (s / d - 1) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) hexp
    linarith

set_option backward.isDefEq.respectTransparency false in
/-- Product formula for the `lintegral` over a finite power product measure. -/
theorem s66_lintegral_pi_pow {E : Type*} [MeasurableSpace E] (μ : Measure E) [SigmaFinite μ]
    {g : E → ℝ≥0∞} (hg : Measurable g) (n : ℕ) :
    ∫⁻ x : Fin n → E, ∏ i, g (x i) ∂(Measure.pi fun _ : Fin n => μ) = (∫⁻ x, g x ∂μ) ^ n := by
  induction n with
  | zero => simp
  | succ n n_ih =>
      calc
        _ = ∫⁻ x : E × (Fin n → E), g x.1 * ∏ i : Fin n, g (x.2 i)
            ∂(μ.prod (Measure.pi fun _ : Fin n => μ)) := by
          rw [← ((measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μ) 0).symm).lintegral_comp_emb
            (MeasurableEquiv.measurableEmbedding _)]
          simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
            Fin.prod_univ_succ, Fin.insertNth_zero, Equiv.coe_fn_mk, Fin.cons_succ,
            Fin.zero_succAbove, cast_eq, Fin.cons_zero]
        _ = (∫⁻ x, g x ∂μ) * (∫⁻ x, g x ∂μ) ^ n := by
          rw [← n_ih, ← lintegral_prod_mul hg.aemeasurable]
          exact (Finset.measurable_prod _ fun i _ => hg.comp (measurable_pi_apply i)).aemeasurable
        _ = _ := by rw [pow_succ']

/-- The second moment from the exponential moment of the one-particle law (Donsker-Varadhan). -/
theorem s66_second_moment (hd : 1 ≤ d) {μ : Measure (Euc d)} [IsProbabilityMeasure μ] {c₁ E : ℝ}
    (hc₁ : 0 < c₁) (hE : ∫⁻ x, ENNReal.ofReal (Real.exp (c₁ * ‖x‖ ^ 2)) ∂μ ≤ ENNReal.ofReal E)
    (hN : 1 ≤ N) (f : Measure (EucConfig d N)) [IsProbabilityMeasure f]
    (hKL : relEntropy f (Measure.pi fun _ : Fin N => μ) ≠ ⊤) :
    ∫⁻ X, ENNReal.ofReal (movSecondMoment X) ∂f ≤
      ENNReal.ofReal (c₁⁻¹ * ((relEntropy f (Measure.pi fun _ : Fin N => μ)).toReal / N +
        Real.log (max E 1))) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  set π := Measure.pi fun _ : Fin N => μ with hπ
  set Ψ : EucConfig d N → ℝ := fun X => c₁ * ∑ i, ‖X i‖ ^ 2 with hΨ
  have hΨm : Measurable Ψ := by fun_prop
  have hΨ0 : ∀ X, 0 ≤ Ψ X := fun X => by positivity
  set E' : ℝ := max E 1 with hE'
  have hE'1 : 1 ≤ E' := le_max_right _ _
  set K : ℝ := N * Real.log E' with hK
  have hK0 : 0 ≤ K := by
    have := Real.log_nonneg hE'1
    positivity
  have hZ : ∫⁻ X, ENNReal.ofReal (Real.exp (Ψ X)) ∂π ≤ ENNReal.ofReal (Real.exp K) := by
    have e : ∀ X : EucConfig d N, ENNReal.ofReal (Real.exp (Ψ X)) =
        ∏ i, ENNReal.ofReal (Real.exp (c₁ * ‖X i‖ ^ 2)) := by
      intro X
      simp only [hΨ, Finset.mul_sum, Real.exp_sum]
      rw [ENNReal.ofReal_prod_of_nonneg (fun i _ => (Real.exp_pos _).le)]
    simp_rw [e]
    rw [s66_lintegral_pi_pow (E := Euc d) μ (g := fun x => ENNReal.ofReal (Real.exp (c₁ * ‖x‖ ^ 2)))
      (by fun_prop) N]
    have h1 : ∀ i : Fin N, ∫⁻ x, ENNReal.ofReal (Real.exp (c₁ * ‖x‖ ^ 2)) ∂μ ≤ ENNReal.ofReal E' :=
      fun i => hE.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
    calc (∫⁻ x, ENNReal.ofReal (Real.exp (c₁ * ‖x‖ ^ 2)) ∂μ) ^ N
        ≤ (ENNReal.ofReal E') ^ N := pow_le_pow_left' (h1 ⟨0, hN⟩) N
      _ = ENNReal.ofReal (E' ^ N) := by
          rw [ENNReal.ofReal_pow (by linarith)]
      _ = ENNReal.ofReal (Real.exp K) := by
          congr 1
          rw [hK, Real.exp_nat_mul, Real.exp_log (by linarith)]
  have hdv := HRS.dv_lintegral π f hKL hΨm hΨ0 hK0 hZ
  have hpt : ∀ X : EucConfig d N, ENNReal.ofReal (movSecondMoment X) =
      ENNReal.ofReal ((c₁ * N)⁻¹) * ENNReal.ofReal (Ψ X) := by
    intro X
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    simp only [movSecondMoment, hΨ]
    field_simp
  simp_rw [hpt]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have hfin : relEntropy f π ≠ ⊤ := hKL
  calc ENNReal.ofReal ((c₁ * N)⁻¹) * ∫⁻ X, ENNReal.ofReal (Ψ X) ∂f
      ≤ ENNReal.ofReal ((c₁ * N)⁻¹) * (relEntropy f π + ENNReal.ofReal K) :=
        mul_le_mul_right hdv _
    _ = ENNReal.ofReal ((c₁ * N)⁻¹ * ((relEntropy f π).toReal + K)) := by
        rw [← ENNReal.ofReal_toReal hfin, ← ENNReal.ofReal_add ENNReal.toReal_nonneg hK0,
          ← ENNReal.ofReal_mul (by positivity)]
        simp [ENNReal.toReal_ofReal]
    _ = ENNReal.ofReal (c₁⁻¹ * ((relEntropy f π).toReal / N + Real.log E')) := by
        congr 1
        rw [hK]
        field_simp

end HRS.MS.MovEnt

end
