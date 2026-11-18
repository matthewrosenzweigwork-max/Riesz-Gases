import HRS.MS.R2GenInitAux7

/-!
# S10.5 input `hmom` (part 2): Donsker-Varadhan for the second moment

`s105_dv_second`: if `∫ e^{c|x|²} dμ ≤ Z` (`Z ≥ 1`, `c > 0`) and `H(f | μ^{⊗N}) < ∞`, then
`E_f N⁻¹∑|x_i|² ≤ c⁻¹ (N⁻¹ H(f | μ^{⊗N}) + Z)`: `∫⁻ e^{cΣ|x_i|²} dμ^{⊗N} = (∫ e^{c|x|²})^N ≤ e^{NZ}` and `wr9_dv_abs`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Function Set
open scoped ENNReal NNReal

namespace HRS.MS.R2GenInit

open HRS.Whole HRS.MS.Wr

variable {d : ℕ}

theorem s105_exp_second_product {μ : Measure (Euc d)} [IsProbabilityMeasure μ] {N : ℕ} {c Z : ℝ}
    (hc : 0 < c) (hZ1 : 1 ≤ Z)
    (hZ : ∫⁻ x, ENNReal.ofReal (Real.exp (c * ‖x‖ ^ 2)) ∂μ ≤ ENNReal.ofReal Z) :
    ∫⁻ X : EucConfig d N, ENNReal.ofReal (Real.exp (c * |∑ i, ‖X i‖ ^ 2|))
      ∂(Measure.pi fun _ : Fin N => μ) ≤ ENNReal.ofReal (Real.exp ((N : ℝ) * Z)) := by
  set π : Measure (EucConfig d N) := Measure.pi fun _ : Fin N => μ with hπ
  have hsum0 : ∀ X : EucConfig d N, 0 ≤ ∑ i, ‖X i‖ ^ 2 := fun X => Finset.sum_nonneg fun i _ => by positivity
  have hpt : ∀ X : EucConfig d N, ENNReal.ofReal (Real.exp (c * |∑ i, ‖X i‖ ^ 2|)) =
      ∏ i : Fin N, ENNReal.ofReal (Real.exp (c * ‖X i‖ ^ 2)) := by
    intro X
    rw [abs_of_nonneg (hsum0 X), Finset.mul_sum, Real.exp_sum,
      ENNReal.ofReal_prod_of_nonneg (fun i _ => (Real.exp_pos _).le)]
  simp_rw [hpt]
  have hmeas : ∀ i : Fin N, Measurable fun X : EucConfig d N => ENNReal.ofReal (Real.exp (c * ‖X i‖ ^ 2)) :=
    fun i => by fun_prop
  have hind : iIndepFun (fun (i : Fin N) (X : EucConfig d N) => ENNReal.ofReal (Real.exp (c * ‖X i‖ ^ 2))) π :=
    iIndepFun_pi (X := fun (_ : Fin N) (x : Euc d) => ENNReal.ofReal (Real.exp (c * ‖x‖ ^ 2)))
      (fun _ => (by fun_prop : Measurable fun x : Euc d => ENNReal.ofReal (Real.exp (c * ‖x‖ ^ 2))).aemeasurable)
  rw [lintegral_prod_eq_prod_lintegral_of_indepFun Finset.univ _ hind hmeas]
  have hone : ∀ i : Fin N, ∫⁻ X : EucConfig d N, ENNReal.ofReal (Real.exp (c * ‖X i‖ ^ 2)) ∂π =
      ∫⁻ x, ENNReal.ofReal (Real.exp (c * ‖x‖ ^ 2)) ∂μ := by
    intro i
    exact (measurePreserving_eval (fun _ : Fin N => μ) i).lintegral_comp
      (by fun_prop : Measurable fun x : Euc d => ENNReal.ofReal (Real.exp (c * ‖x‖ ^ 2)))
  simp_rw [hone]
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  calc (∫⁻ x, ENNReal.ofReal (Real.exp (c * ‖x‖ ^ 2)) ∂μ) ^ N ≤ (ENNReal.ofReal Z) ^ N :=
        pow_le_pow_left' hZ N
    _ = ENNReal.ofReal (Z ^ N) := (ENNReal.ofReal_pow (by linarith) N).symm
    _ ≤ ENNReal.ofReal (Real.exp ((N : ℝ) * Z)) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have h1 : Z ≤ Real.exp Z := by linarith [Real.add_one_le_exp Z]
        calc Z ^ N ≤ (Real.exp Z) ^ N := pow_le_pow_left₀ (by linarith) h1 N
          _ = Real.exp ((N : ℝ) * Z) := by rw [← Real.exp_nat_mul]

theorem s105_second_moment_of_kl {μ : Measure (Euc d)} [IsProbabilityMeasure μ] {N : ℕ} (hN : 0 < N) {c Z : ℝ}
    (hc : 0 < c) (hZ1 : 1 ≤ Z)
    (hZ : ∫⁻ x, ENNReal.ofReal (Real.exp (c * ‖x‖ ^ 2)) ∂μ ≤ ENNReal.ofReal Z)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → EucConfig d N)
    (hX : Measurable X)
    (hKL : InformationTheory.klDiv (P.map X) (Measure.pi fun _ : Fin N => μ) ≠ ⊤) :
    ∫⁻ ζ, ENNReal.ofReal (movSecondMoment (X ζ)) ∂P ≤ ENNReal.ofReal (c⁻¹ *
      ((InformationTheory.klDiv (P.map X) (Measure.pi fun _ : Fin N => μ)).toReal / N + Z)) := by
  haveI : IsProbabilityMeasure (P.map X) := ⟨by rw [Measure.map_apply hX MeasurableSet.univ]; simp⟩
  set π : Measure (EucConfig d N) := Measure.pi fun _ : Fin N => μ with hπ
  set Ψ : EucConfig d N → ℝ := fun X => ∑ i, ‖X i‖ ^ 2 with hΨ
  have hΨm : Measurable Ψ := Finset.measurable_sum _ fun i _ =>
    ((measurable_norm.comp (measurable_pi_apply i)).pow_const 2)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hK : 0 ≤ (N : ℝ) * Z := mul_nonneg hN0.le (by linarith)
  obtain ⟨hi, hb⟩ := wr9_dv_abs π (P.map X) hKL hΨm hc hK (s105_exp_second_product hc hZ1 hZ)
  have hΨ0 : ∀ Y : EucConfig d N, 0 ≤ Ψ Y := fun Y => Finset.sum_nonneg fun i _ => by positivity
  have hmov : ∀ Y : EucConfig d N, movSecondMoment Y = (N : ℝ)⁻¹ * Ψ Y := by
    intro Y; unfold movSecondMoment; simp only [hΨ, one_div]
  have hint : Integrable (fun Y => (N : ℝ)⁻¹ * Ψ Y) (P.map X) := by
    refine (hi.const_mul (N : ℝ)⁻¹).congr (Filter.Eventually.of_forall fun Y => ?_)
    simp only [abs_of_nonneg (hΨ0 Y)]
  have hfm : Measurable fun Y : EucConfig d N => ENNReal.ofReal (movSecondMoment Y) :=
    ENNReal.measurable_ofReal.comp (by
      have e : (movSecondMoment : EucConfig d N → ℝ) = fun Y => (N : ℝ)⁻¹ * Ψ Y := funext hmov
      rw [e]; exact hΨm.const_mul _)
  rw [← lintegral_map hfm hX]
  simp_rw [hmov]
  rw [← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun Y =>
    mul_nonneg (inv_nonneg.2 hN0.le) (hΨ0 Y))]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [integral_const_mul]
  have hb' : ∫ Y, Ψ Y ∂(P.map X) ≤ c⁻¹ * ((InformationTheory.klDiv (P.map X) π).toReal + N * Z) := by
    refine le_trans (le_of_eq ?_) hb
    exact integral_congr_ae (Filter.Eventually.of_forall fun Y => (abs_of_nonneg (hΨ0 Y)).symm)
  calc (N : ℝ)⁻¹ * ∫ Y, Ψ Y ∂(P.map X) ≤ (N : ℝ)⁻¹ * (c⁻¹ * ((InformationTheory.klDiv (P.map X) π).toReal + N * Z)) :=
        mul_le_mul_of_nonneg_left hb' (inv_nonneg.2 hN0.le)
    _ = c⁻¹ * ((InformationTheory.klDiv (P.map X) π).toReal / N + Z) := by
        field_simp

end HRS.MS.R2GenInit
