import HRS.Energy.Modulated
import HRS.Energy.PressureDV

/-!
# DYNCMP: Theorem 5.4 `dynamic_comparison`, step (3): the linear-statistic entropy bound

`N:eq:product-linear` (Hoeffding for the `iid` product measure, `dyncmp_hoeffding_mgf`, from Mathlib's
`hasSubgaussianMGF_of_mem_Icc`) and `N:eq:linear-entropy` (`dyncmp_linear_entropy`, M L6514-6521): by the
Donsker-Varadhan inequality (`dv_lintegral`) optimised in `z`, using both signs,
`E_ν|μ_N(a) - μ(a)| ≤ K √(2 (H(ν|μ^{⊗N}) + log 2)/N)` for `|a| ≤ K`.
-/

open MeasureTheory Filter Topology ProbabilityTheory Set InformationTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS

variable {d N : ℕ}

/-- Hoeffding for the empirical mean of an `iid` bounded sample, in the form of an exponential-moment bound. -/
theorem dyncmp_hoeffding_mgf {μ : Measure (Torus d)} [IsProbabilityMeasure μ] {a : Torus d → ℝ}
    (ha : Measurable a) {K : ℝ} (hK : 0 ≤ K) (hab : ∀ x, |a x| ≤ K) (hN : 0 < N) (z : ℝ) :
    ∫ X : Config d N, Real.exp (z * ((1 / (N : ℝ)) * ∑ i, a (X i) - ∫ x, a x ∂μ))
        ∂(Measure.pi fun _ : Fin N => μ) ≤ Real.exp (K ^ 2 * z ^ 2 / (2 * N)) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  set m : ℝ := ∫ x, a x ∂μ with hm
  have hsg : HasSubgaussianMGF (fun x => a x - μ[a]) ((‖K - -K‖₊ / 2) ^ 2) μ :=
    hasSubgaussianMGF_of_mem_Icc ha.aemeasurable (Eventually.of_forall fun x => ⟨by linarith [(abs_le.1 (hab x)).1], (abs_le.1 (hab x)).2⟩)
  have hc : (((‖K - -K‖₊ / 2) ^ 2 : ℝ≥0) : ℝ) = K ^ 2 := by
    have : ((‖K - -K‖₊ : ℝ≥0) : ℝ) = 2 * K := by
      rw [coe_nnnorm, Real.norm_eq_abs, sub_neg_eq_add, abs_of_nonneg (by linarith)]; ring
    rw [NNReal.coe_pow, NNReal.coe_div, this]; norm_num
  have hprod : ∀ X : Config d N, Real.exp (z * ((1 / (N : ℝ)) * ∑ i, a (X i) - m)) =
      ∏ i : Fin N, Real.exp ((z / N) * (a (X i) - m)) := by
    intro X
    rw [← Real.exp_sum, Finset.sum_congr rfl (fun i _ => (mul_sub (z / N) (a (X i)) m)), Finset.sum_sub_distrib,
      ← Finset.mul_sum]
    congr 1
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  simp_rw [hprod]
  rw [integral_fintype_prod_eq_pow (fun x => Real.exp ((z / N) * (a x - m)))]
  have h1 : ∫ x, Real.exp ((z / N) * (a x - m)) ∂μ ≤ Real.exp (K ^ 2 * (z / N) ^ 2 / 2) := by
    have := hsg.mgf_le (z / N)
    rw [hc] at this
    exact this
  have h0 : 0 ≤ ∫ x, Real.exp ((z / N) * (a x - m)) ∂μ := integral_nonneg fun x => (Real.exp_pos _).le
  calc (∫ x, Real.exp ((z / N) * (a x - m)) ∂μ) ^ Fintype.card (Fin N)
      ≤ (Real.exp (K ^ 2 * (z / N) ^ 2 / 2)) ^ Fintype.card (Fin N) := pow_le_pow_left₀ h0 h1 _
    _ = Real.exp (K ^ 2 * z ^ 2 / (2 * N)) := by
      rw [← Real.exp_nat_mul, Fintype.card_fin]
      congr 1
      field_simp


theorem dyncmp_exp_abs_le (x : ℝ) : Real.exp |x| ≤ Real.exp x + Real.exp (-x) := by
  rcases abs_cases x with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h]
  · have := Real.exp_pos (-x); linarith
  · have := Real.exp_pos x; linarith

/-- **The linear-statistic entropy bound** `N:eq:linear-entropy` (M L6516-6520), from Hoeffding and the
Donsker-Varadhan inequality: `E_ν|μ_N(a) - μ(a)| ≤ K √(2 (H(ν|μ^{⊗N}) + log 2)/N)` for `|a| ≤ K`. -/
theorem dyncmp_linear_entropy {μ : Measure (Torus d)} [IsProbabilityMeasure μ] {a : Torus d → ℝ}
    (ha : Measurable a) {K : ℝ} (hK : 0 ≤ K) (hab : ∀ x, |a x| ≤ K) (hN : 0 < N)
    {ν : Measure (Config d N)} [IsProbabilityMeasure ν]
    (hH : relEntropy ν (Measure.pi fun _ : Fin N => μ) ≠ ⊤) :
    ∫ X, |(1 / (N : ℝ)) * ∑ i, a (X i) - ∫ x, a x ∂μ| ∂ν ≤
      K * Real.sqrt (2 * ((relEntropy ν (Measure.pi fun _ : Fin N => μ)).toReal + Real.log 2) / N) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  set m : ℝ := ∫ x, a x ∂μ with hm
  set Q : Measure (Config d N) := Measure.pi fun _ : Fin N => μ with hQ
  haveI : IsProbabilityMeasure Q := inferInstance
  set S : Config d N → ℝ := fun X => (1 / (N : ℝ)) * ∑ i, a (X i) - m with hS
  have hSm : Measurable S := by
    refine (measurable_const.mul (Finset.measurable_sum _ fun i _ => ha.comp (measurable_pi_apply i))).sub
      measurable_const
  have hmK : |m| ≤ K := by
    rw [hm]
    refine (abs_integral_le_integral_abs).trans ?_
    calc ∫ x, |a x| ∂μ ≤ ∫ x, K ∂μ := integral_mono_of_nonneg (Eventually.of_forall fun x => abs_nonneg _)
          (integrable_const _) (Eventually.of_forall hab)
      _ = K := by simp
  have hSb : ∀ X, |S X| ≤ 2 * K := by
    intro X
    have h1 : |(1 / (N : ℝ)) * ∑ i, a (X i)| ≤ K := by
      rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / N)]
      calc 1 / (N : ℝ) * |∑ i, a (X i)| ≤ 1 / (N : ℝ) * ∑ i, |a (X i)| :=
            mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by positivity)
        _ ≤ 1 / (N : ℝ) * ∑ i : Fin N, K := mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => hab _) (by positivity)
        _ = K := by simp; field_simp
    calc |S X| ≤ |(1 / (N : ℝ)) * ∑ i, a (X i)| + |m| := abs_sub _ _
      _ ≤ 2 * K := by linarith
  rcases hK.eq_or_lt with hK0 | hKpos
  · subst hK0
    have ha0 : ∀ x, a x = 0 := fun x => abs_nonpos_iff.1 (hab x)
    have hSz : ∀ X, S X = 0 := fun X => abs_nonpos_iff.1 (by simpa using hSb X)
    have hz0 : (fun X => |S X|) = fun _ => (0 : ℝ) := funext fun X => by rw [hSz X, abs_zero]
    show ∫ X, |S X| ∂ν ≤ _
    rw [hz0]; simp
  set H : ℝ := (relEntropy ν Q).toReal with hHdef
  have hH0 : 0 ≤ H := ENNReal.toReal_nonneg
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set u : ℝ := H + Real.log 2 with hu
  have hupos : 0 < u := by linarith
  set z : ℝ := Real.sqrt (2 * N * u) / K with hz
  have hzpos : 0 < z := by rw [hz]; positivity
  set K' : ℝ := Real.log 2 + K ^ 2 * z ^ 2 / (2 * N) with hK'
  have hK'0 : 0 ≤ K' := by rw [hK']; positivity
  have hmgf : ∀ w : ℝ, ∫⁻ X, ENNReal.ofReal (Real.exp (w * S X)) ∂Q ≤ ENNReal.ofReal (Real.exp (K ^ 2 * w ^ 2 / (2 * N))) := by
    intro w
    have hint : Integrable (fun X => Real.exp (w * S X)) Q :=
      Integrable.of_bound (C := Real.exp (|w| * (2 * K))) (Real.measurable_exp.comp (measurable_const.mul hSm)).aestronglyMeasurable
        (Eventually.of_forall fun X => by
          rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
          refine Real.exp_le_exp.2 ?_
          calc w * S X ≤ |w * S X| := le_abs_self _
            _ = |w| * |S X| := abs_mul _ _
            _ ≤ |w| * (2 * K) := mul_le_mul_of_nonneg_left (hSb X) (abs_nonneg _))
    rw [← ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun X => (Real.exp_pos _).le)]
    exact ENNReal.ofReal_le_ofReal (dyncmp_hoeffding_mgf ha hK hab hN w)
  have hZ : ∫⁻ X, ENNReal.ofReal (Real.exp (z * |S X|)) ∂Q ≤ ENNReal.ofReal (Real.exp K') := by
    have hpt : ∀ X, ENNReal.ofReal (Real.exp (z * |S X|)) ≤
        ENNReal.ofReal (Real.exp (z * S X)) + ENNReal.ofReal (Real.exp ((-z) * S X)) := by
      intro X
      rw [← ENNReal.ofReal_add (Real.exp_pos _).le (Real.exp_pos _).le]
      refine ENNReal.ofReal_le_ofReal ?_
      have : z * |S X| = |z * S X| := by rw [abs_mul, abs_of_pos hzpos]
      rw [this]
      have h3 : (-z) * S X = -(z * S X) := by ring
      rw [h3]; exact dyncmp_exp_abs_le _
    calc ∫⁻ X, ENNReal.ofReal (Real.exp (z * |S X|)) ∂Q
        ≤ ∫⁻ X, (ENNReal.ofReal (Real.exp (z * S X)) + ENNReal.ofReal (Real.exp ((-z) * S X))) ∂Q :=
          lintegral_mono hpt
      _ = ∫⁻ X, ENNReal.ofReal (Real.exp (z * S X)) ∂Q + ∫⁻ X, ENNReal.ofReal (Real.exp ((-z) * S X)) ∂Q :=
          lintegral_add_left (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
            (measurable_const.mul hSm))) _
      _ ≤ ENNReal.ofReal (Real.exp (K ^ 2 * z ^ 2 / (2 * N))) +
          ENNReal.ofReal (Real.exp (K ^ 2 * (-z) ^ 2 / (2 * N))) := add_le_add (hmgf z) (hmgf (-z))
      _ = ENNReal.ofReal (Real.exp K') := by
          rw [← ENNReal.ofReal_add (Real.exp_pos _).le (Real.exp_pos _).le]
          congr 1
          rw [hK', Real.exp_add, Real.exp_log (by norm_num)]
          have : (-z) ^ 2 = z ^ 2 := by ring
          rw [this]; ring
  have hdv := dv_lintegral Q ν hH (F := fun X => z * |S X|) (measurable_const.mul hSm.abs)
    (fun X => by positivity) hK'0 hZ
  have hnn : 0 ≤ᵐ[ν] fun X => z * |S X| := Eventually.of_forall fun X => by positivity
  have hae : AEStronglyMeasurable (fun X => z * |S X|) ν := (measurable_const.mul hSm.abs).aestronglyMeasurable
  have hle : ∫ X, z * |S X| ∂ν ≤ H + K' := by
    rw [integral_eq_lintegral_of_nonneg_ae hnn hae]
    have := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hH, ENNReal.ofReal_ne_top⟩) hdv
    rw [ENNReal.toReal_add hH ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hK'0] at this
    exact this
  rw [integral_const_mul] at hle
  have hz2 : z ^ 2 = 2 * N * u / K ^ 2 := by
    rw [hz, div_pow, Real.sq_sqrt (by positivity)]
  have hKz : K ^ 2 * z ^ 2 / (2 * N) = u := by
    rw [hz2]; field_simp
  have hbd : z * ∫ X, |S X| ∂ν ≤ 2 * u := by
    have : H + K' = 2 * u := by rw [hK', hKz, hu]; ring
    linarith
  have hfin : ∫ X, |S X| ∂ν ≤ 2 * u / z := by
    rw [le_div_iff₀ hzpos]; linarith
  refine hfin.trans (le_of_eq ?_)
  -- `2u / z = K √(2u/N)`
  have hs1 : 0 < Real.sqrt (2 * N * u) := by positivity
  have hs2 : Real.sqrt (2 * N * u) * Real.sqrt (2 * u / N) = 2 * u := by
    rw [← Real.sqrt_mul (by positivity)]
    have : 2 * N * u * (2 * u / N) = (2 * u) ^ 2 := by field_simp
    rw [this, Real.sqrt_sq (by positivity)]
  rw [div_eq_iff hzpos.ne', hz]
  calc 2 * u = Real.sqrt (2 * u / N) * Real.sqrt (2 * N * u) := by rw [mul_comm (Real.sqrt (2 * u / N))]; exact hs2.symm
    _ = K * Real.sqrt (2 * u / N) * (Real.sqrt (2 * N * u) / K) := by field_simp

end HRS

end
