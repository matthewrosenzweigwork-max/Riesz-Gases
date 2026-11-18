import HRS.MS.SharpBiasAux1
import HRS.MS.CondDens

/-!
# HRS.MS.SharpBiasAux2 -- S7.1: the first-marginal density `θ_N` for every `N ≥ 1`, and the generic conclusion

Packet S71, namespace `HRS.Whole.S71`, helper prefix `s71_`.

* `s71_theta_*`: the density `θ_N = dπ_N/dμ = wr13d_theta` of the first marginal of `Q_{N,β}(μ)` is measurable,
  strictly positive, bounded by `exp (2 β M_g)` and integrates to `1`, for every `N = n + 1 ≥ 1`
  (the merged `wr13d_*` lemmas assume `n ≥ 1` only through a positivity argument that is valid for `n = 0`).
* `s71_conclusion`: if the first marginal is `μ.withDensity θ` with `θ` bounded and
  `‖(θ-1)/δ_N - b‖_{L²(μ)} ≤ C N^{-θ_{d,s}}` then `SharpBiasConclusion d s N β ρ C` holds (the statistic
  clause `S:eq:sharp-statistic`, `S:eq:test-remainder` is Cauchy-Schwarz).
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.Whole.S71

open HRS.MS.Wr

variable {d : ℕ} {s : ℝ}

/-! ### Exponents -/

theorem s71_theta_pos_exp (hd : 2 ≤ d) (hs : (d : ℝ) / 2 < s) (hsd : s < d) :
    0 < biasTheta d s ∧ biasTheta d s ≤ biasTau d s ∧ biasTheta d s ≤ (2 - biasP d s) / 8 ∧
      biasTheta d s ≤ 1 ∧ 0 < biasTau d s ∧ biasTau d s ≤ (biasP d s - 1) / 2 ∧
      biasTau d s ≤ biasP d s - 1 ∧ biasTau d s ≤ 1 := by
  obtain ⟨hp1, hp2⟩ := s74_p_bounds hd hs hsd
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs0 : 0 < s := by linarith
  have hp : biasP d s = (d : ℝ) / s := rfl
  have hp0 : 0 < biasP d s := by rw [hp]; linarith
  have h34 : 0 < 3 / (4 * s) := by positivity
  have hτ : biasTau d s = (biasP d s - 1) ^ 2 / biasP d s := rfl
  have hτ0 : 0 < biasTau d s := by rw [hτ]; apply div_pos (by nlinarith) hp0
  have hθ : biasTheta d s = min ((biasP d s - 1) ^ 2 / biasP d s)
      (min ((2 - biasP d s) / 8) (3 / (4 * s))) := rfl
  have h2 : 0 < (2 - biasP d s) / 8 := by linarith
  refine ⟨?_, ?_, ?_, ?_, hτ0, ?_, ?_, ?_⟩
  · rw [hθ]; exact lt_min hτ0 (lt_min h2 h34)
  · rw [hθ, hτ]; exact min_le_left _ _
  · rw [hθ]; exact (min_le_right _ _).trans (min_le_left _ _)
  · rw [hθ]; exact (min_le_right _ _).trans ((min_le_left _ _).trans (by linarith))
  · rw [hτ, div_le_iff₀ hp0]; nlinarith
  · rw [hτ, div_le_iff₀ hp0]; nlinarith
  · rw [hτ, div_le_iff₀ hp0]; nlinarith

/-! ### The density `θ_N` for every `N ≥ 1` -/

section Theta

variable {ρ : Euc d → ℝ} {M β : ℝ}

theorem s71_theta_pos (hd : 2 ≤ d) (hs0 : 0 < s) (hsd : s < d) (hρ : IsProbDensity ρ)
    (hM : ∀ x, ρ x ≤ M) (hβ : 0 ≤ β) (n : ℕ) (x : Euc d) :
    0 < wr13d_theta d s n β (withDensityReal ρ) x := by
  haveI := wr13a_isProb_density hρ
  have hΦ : 0 < poleNormalizer d s (n + 1) β (withDensityReal ρ) x 1 :=
    (wr13a_cavityWellDefined hs0 (wr13a_conv_le_density (by omega) hs0 hsd hρ hM) hβ zero_le_one
      (n + 1) x).pole_pos
  exact div_pos (mul_pos (Real.exp_pos _) hΦ) (wr13d_Z_pos hd hs0 hsd hρ hM hβ n)

theorem s71_firstMarginal_isProb (hd : 2 ≤ d) (hs0 : 0 < s) (hsd : s < d) (hρ : IsProbDensity ρ)
    (hM : ∀ x, ρ x ≤ M) (hβ : 0 ≤ β) (n : ℕ) :
    IsProbabilityMeasure (firstMarginal (modulatedGibbs (rieszKernel d s) (n + 1) β
      (withDensityReal ρ))) := by
  have := wr13a_isProb_density hρ
  have := wr13c2_Q_isProb hs0 (wr13a_conv_le_density (by omega) hs0 hsd hρ hM) hβ
    (by omega : 1 ≤ n + 1)
  unfold firstMarginal
  rw [dif_pos (by omega : 0 < n + 1)]
  infer_instance

theorem s71_theta_integral (hd : 2 ≤ d) (hs0 : 0 < s) (hsd : s < d) (hρ : IsProbDensity ρ)
    (hM : ∀ x, ρ x ≤ M) (hβ : 0 ≤ β) (n : ℕ) :
    ∫ x, wr13d_theta d s n β (withDensityReal ρ) x ∂(withDensityReal ρ) = 1 := by
  have := wr13a_isProb_density hρ
  have := s71_firstMarginal_isProb hd hs0 hsd hρ hM hβ n
  have hm := wr13d_theta_meas hd hs0 hsd hρ hM hβ n
  have hint : Integrable (wr13d_theta d s n β (withDensityReal ρ)) (withDensityReal ρ) :=
    Integrable.of_bound hm.aestronglyMeasurable (Real.exp (2 * β * potentialBound d s M))
      (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_pos (s71_theta_pos hd hs0 hsd hρ hM hβ n x)]
        exact wr13d_theta_le hd hs0 hsd hρ hM hβ n x)
  have h1 : ∫⁻ x, ENNReal.ofReal (wr13d_theta d s n β (withDensityReal ρ) x)
      ∂(withDensityReal ρ) = 1 := by
    have := measure_univ (μ := firstMarginal (modulatedGibbs (rieszKernel d s)
      (n + 1) β (withDensityReal ρ)))
    rw [wr13d_firstMarginal_eq hd hs0 hsd hρ hM hβ n, withDensity_apply _ MeasurableSet.univ,
      Measure.restrict_univ] at this
    exact this
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall fun x => (s71_theta_pos hd hs0 hsd hρ hM hβ n x).le)] at h1
  exact (ENNReal.ofReal_eq_one.1 h1)

/-- `θ ≤ exp (2 βp |M_g|)` for `0 ≤ β ≤ βp`. -/
theorem s71_theta_le (hd : 2 ≤ d) (hs0 : 0 < s) (hsd : s < d) (hρ : IsProbDensity ρ)
    (hM : ∀ x, ρ x ≤ M) {βp : ℝ} (hβ : 0 ≤ β) (hββp : β ≤ βp) (n : ℕ) (x : Euc d) :
    wr13d_theta d s n β (withDensityReal ρ) x ≤ Real.exp (2 * βp * |potentialBound d s M|) := by
  refine (wr13d_theta_le hd hs0 hsd hρ hM hβ n x).trans (Real.exp_le_exp.2 ?_)
  have h1 : 2 * β * potentialBound d s M ≤ 2 * β * |potentialBound d s M| :=
    mul_le_mul_of_nonneg_left (le_abs_self _) (by positivity)
  have h2 : 2 * β * |potentialBound d s M| ≤ 2 * βp * |potentialBound d s M| :=
    mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
  linarith

end Theta

/-! ### The generic conclusion -/

section Conclusion

variable {ρ : Euc d → ℝ} {M : ℝ}

theorem s71_deltaN_pos (hs : (d : ℝ) / 2 < s) (N : ℕ) (hN : 1 ≤ N) : 0 < deltaN d s N := by
  rw [s74_deltaN hs N]
  exact Real.rpow_pos_of_pos (by exact_mod_cast hN) _

theorem s71_conclusion (hd : 2 ≤ d) (hs : (d : ℝ) / 2 < s) (hsd : s < d) {β : ℝ} (hβ : 0 < β)
    (hρ : IsProbDensity ρ) (hM : ∀ x, ρ x ≤ M) {N : ℕ} (hN : 1 ≤ N) {C : ℝ}
    (hG : GibbsWellDefined (fun x y => rieszKernel d s (x - y)) N β (withDensityReal ρ))
    {θ : Euc d → ℝ} (hθm : Measurable θ) (hθ0 : ∀ x, 0 ≤ θ x) {Cθ : ℝ} (hθC : ∀ x, θ x ≤ Cθ)
    (hπ : firstMarginal (modulatedGibbs (rieszKernel d s) N β (withDensityReal ρ)) =
      (withDensityReal ρ).withDensity (fun x => ENNReal.ofReal (θ x)))
    (hθ1 : ∫ x, θ x ∂(withDensityReal ρ) = 1)
    (hE : MemLp (fun x => (θ x - 1) / deltaN d s N - biasDensity d s β ρ x) 2 (withDensityReal ρ) ∧
      l2Norm (withDensityReal ρ) (fun x => (θ x - 1) / deltaN d s N - biasDensity d s β ρ x) ≤
        C * (N : ℝ) ^ (-biasTheta d s)) :
    SharpBiasConclusion d s N β ρ C := by
  have hs0 : 0 < s := by
    have : (1 : ℝ) ≤ (d : ℝ) / 2 := by
      have : (2 : ℝ) ≤ d := by exact_mod_cast hd
      linarith
    linarith
  haveI hμ := wr13a_isProb_density hρ
  set μ := withDensityReal ρ with hμdef
  have hq : Q34.Q34Hyp d s ρ M := ⟨by omega, hs0, hsd, hρ, hM⟩
  have hδ := s71_deltaN_pos hs N hN
  set δ := deltaN d s N with hδdef
  have hρL : MemLp ρ 2 μ := by
    have hM0 : 0 ≤ M := (hρ.nonneg 0).trans (hM 0)
    exact MemLp.of_bound hρ.measurable.aestronglyMeasurable M (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hρ.nonneg x)]
      exact hM x)
  have hR := s71_resp_spec hq hβ hρL
  set r := responseInverse (rieszKernel d s) μ β ρ with hr
  have hrL : MemLp r 2 μ := hR.1.1
  set c₀ : ℝ := 2 * biasConst d s * β ^ biasP d s with hc₀
  have hbias : biasDensity d s β ρ = fun x => c₀ * r x := rfl
  have hbL : MemLp (biasDensity d s β ρ) 2 μ := by rw [hbias]; exact hrL.const_mul c₀
  -- θ - 1 ∈ L²
  have hzL : MemLp (fun x => θ x - 1) 2 μ := by
    have h1 : MemLp (fun x => δ * ((θ x - 1) / δ - biasDensity d s β ρ x + biasDensity d s β ρ x)) 2 μ :=
      (hE.1.add hbL).const_mul δ
    refine h1.ae_eq (Eventually.of_forall fun x => ?_)
    show δ * ((θ x - 1) / δ - biasDensity d s β ρ x + biasDensity d s β ρ x) = θ x - 1
    field_simp
    ring
  have hθint : Integrable θ μ := by
    have := (hzL.integrable one_le_two).add (integrable_const (1 : ℝ))
    exact this.congr (Eventually.of_forall fun x => by simp)
  have hzero : ∫ x, (θ x - 1) ∂μ = 0 := by
    rw [integral_sub hθint (integrable_const _), hθ1]
    simp
  refine ⟨hG, hrL, ⟨θ, hθm, hθ0, hπ, hE.1, hE.2⟩, ?_⟩
  intro φ hφ
  have hφ1 : Integrable φ μ := hφ.integrable one_le_two
  have hθf : ∀ᵐ x ∂μ, ENNReal.ofReal (θ x) < ∞ := Eventually.of_forall fun x => ENNReal.ofReal_lt_top
  have hθmeas : Measurable fun x => ENNReal.ofReal (θ x) := ENNReal.measurable_ofReal.comp hθm
  have hφθ : Integrable (fun x => θ x * φ x) μ := by
    refine hφ1.bdd_mul (c := Cθ) hθm.aestronglyMeasurable (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hθ0 x)]
    exact hθC x
  have hint : Integrable φ (firstMarginal (modulatedGibbs (rieszKernel d s) N β μ)) := by
    rw [hπ, integrable_withDensity_iff_integrable_smul' hθmeas hθf]
    refine hφθ.congr (Eventually.of_forall fun x => ?_)
    simp [ENNReal.toReal_ofReal (hθ0 x)]
  refine ⟨hint, ?_⟩
  have hint2 : ∫ x, φ x ∂(firstMarginal (modulatedGibbs (rieszKernel d s) N β μ)) =
      ∫ x, θ x * φ x ∂μ := by
    rw [hπ, integral_withDensity_eq_integral_toReal_smul hθmeas hθf]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp [ENNReal.toReal_ofReal (hθ0 x)]
  set c := pair μ φ with hc
  have hPφL : MemLp (projMean μ φ) 2 μ := hφ.sub (memLp_const _)
  have hEL := hE.1
  set E := fun x => (θ x - 1) / δ - biasDensity d s β ρ x with hEdef
  -- the identity
  have hid : ∫ x, φ x ∂(firstMarginal (modulatedGibbs (rieszKernel d s) N β μ)) - ∫ x, φ x ∂μ -
      c₀ * δ * l2Inner μ (projMean μ φ) r = δ * l2Inner μ (projMean μ φ) E := by
    rw [hint2]
    have hA : Integrable (fun x => projMean μ φ x * (θ x - 1)) μ := hPφL.integrable_mul hzL
    have hB : Integrable (fun x => projMean μ φ x * r x) μ := hPφL.integrable_mul hrL
    have hC : Integrable (fun x => projMean μ φ x * E x) μ := hPφL.integrable_mul hEL
    unfold l2Inner
    have e1 : ∫ x, θ x * φ x ∂μ - ∫ x, φ x ∂μ = ∫ x, projMean μ φ x * (θ x - 1) ∂μ := by
      have : (fun x => projMean μ φ x * (θ x - 1)) = fun x => (θ x * φ x - φ x) - c * (θ x - 1) := by
        funext x; simp only [projMean]; rw [← hc]; ring
      have hI : Integrable (fun x => θ x * φ x - φ x) μ := hφθ.sub hφ1
      have hJ : Integrable (fun x => c * (θ x - 1)) μ := (hzL.integrable one_le_two).const_mul c
      rw [this, integral_sub hI hJ, integral_sub hφθ hφ1, integral_const_mul, hzero]
      ring
    have e2 : ∀ x, projMean μ φ x * E x = projMean μ φ x * (θ x - 1) / δ - c₀ * (projMean μ φ x * r x) := by
      intro x
      simp only [hEdef, hbias]
      ring
    have e3 : ∫ x, projMean μ φ x * E x ∂μ =
        (∫ x, projMean μ φ x * (θ x - 1) ∂μ) / δ - c₀ * ∫ x, projMean μ φ x * r x ∂μ := by
      simp_rw [e2]
      rw [integral_sub (hA.div_const δ) (hB.const_mul c₀), integral_div, integral_const_mul]
    rw [e3, ← e1]
    field_simp
  rw [hid]
  have hcs := s71_abs_l2Inner_le hPφL hEL
  rw [abs_mul, abs_of_pos hδ]
  have hn0 := s71_l2Norm_nonneg μ (projMean μ φ)
  calc δ * |l2Inner μ (projMean μ φ) E| ≤ δ * (l2Norm μ (projMean μ φ) * l2Norm μ E) :=
        mul_le_mul_of_nonneg_left hcs hδ.le
    _ ≤ δ * (l2Norm μ (projMean μ φ) * (C * (N : ℝ) ^ (-biasTheta d s))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hE.2 hn0) hδ.le
    _ = C * δ * (N : ℝ) ^ (-biasTheta d s) * l2Norm μ (projMean μ φ) := by ring

end Conclusion

end HRS.Whole.S71
