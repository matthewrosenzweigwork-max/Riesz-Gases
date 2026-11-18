import HRS.MS.MfeConfAux62

/-!
# S.B.1, packet F6 (part 24): the modulated Gibbs measure as a density

`sb1_modGibbs_eq_Dm`: `ℚ_{N,β}(μ) = q dx` with `q(X) = K⁻¹ ∏ρ(X_i) exp(-βN 𝖤(X))`, for any measurable kernel `k` and a probability
density `ρ` with a positive normaliser `K`; `sb1_modGibbs_density_int`: `∫⁻ q = 1`.
-/

open MeasureTheory Filter Topology InformationTheory
open scoped ENNReal NNReal BigOperators ContDiff

noncomputable section

namespace HRS.MS.MfeConf

variable {d N : ℕ}

/-- The Lebesgue density of the modulated Gibbs measure. -/
def sb1qd (k : Euc d → ℝ) (β : ℝ) (N : ℕ) (ρ : Euc d → ℝ) (X : Whole.EucConfig d N) : ℝ :=
  (Whole.gibbsNormalizer k N β (Whole.withDensityReal ρ))⁻¹ *
    ((∏ i, ρ (X i)) * Real.exp (-β * N * sb1En k ρ X))

theorem sb1_modGibbs_eq_Dm {k : Euc d → ℝ} (hk : Measurable k) {β : ℝ} {ρ : Euc d → ℝ}
    (hρ : Whole.IsProbDensity ρ) (hK : 0 < Whole.gibbsNormalizer k N β (Whole.withDensityReal ρ)) :
    Whole.modulatedGibbs k N β (Whole.withDensityReal ρ) = sb1Dm (sb1qd k β N ρ) := by
  haveI : IsProbabilityMeasure (Whole.withDensityReal ρ) := HRS.MS.Thm.cb_withDensityReal_isProb hρ
  have hρi : Integrable ρ := HRS.MS.Canon.cn_integrable_of_prob ρ hρ
  have hpi := HRS.MS.Canon.cn_pi_withDensityReal (N := N) ρ hρ.nonneg hρi
  have hP : Measurable fun X : Whole.EucConfig d N => ∏ i, ρ (X i) :=
    Finset.measurable_prod _ fun i _ => hρ.measurable.comp (measurable_pi_apply i)
  have hE : Measurable fun X : Whole.EucConfig d N => Real.exp (-β * N * sb1En k ρ X) := by
    have : Measurable fun X : Whole.EucConfig d N =>
        Whole.modulatedEnergy k X (Whole.withDensityReal ρ) :=
      sb1_measurable_modulatedEnergy hk _
    simp_rw [sb1_modEnergy_eq hρ] at this
    exact Real.measurable_exp.comp (this.const_mul _)
  unfold Whole.modulatedGibbs sb1Dm
  rw [hpi]
  simp_rw [sb1_modEnergy_eq hρ]
  rw [← withDensity_mul _ hP.ennreal_ofReal hE.ennreal_ofReal]
  have hc : (ENNReal.ofReal (Whole.gibbsNormalizer k N β (Whole.withDensityReal ρ)))⁻¹ ≠ ⊤ :=
    ENNReal.inv_ne_top.2 (ENNReal.ofReal_pos.2 hK).ne'
  rw [← withDensity_smul' _ _ hc]
  congr 1
  funext X
  have hP0 : 0 ≤ ∏ i, ρ (X i) := Finset.prod_nonneg fun i _ => hρ.nonneg _
  show (ENNReal.ofReal (Whole.gibbsNormalizer k N β (Whole.withDensityReal ρ)))⁻¹ *
      (ENNReal.ofReal (∏ i, ρ (X i)) * ENNReal.ofReal (Real.exp (-β * N * sb1En k ρ X))) =
    ENNReal.ofReal (sb1qd k β N ρ X)
  unfold sb1qd
  rw [ENNReal.ofReal_mul (inv_nonneg.2 hK.le), ENNReal.ofReal_mul hP0, ENNReal.ofReal_inv_of_pos hK]

theorem sb1_qd_pos {k : Euc d → ℝ} {β : ℝ} {ρ : Euc d → ℝ} (hρ : ∀ x, 0 < ρ x)
    (hK : 0 < Whole.gibbsNormalizer k N β (Whole.withDensityReal ρ)) (X : Whole.EucConfig d N) :
    0 < sb1qd k β N ρ X := by
  unfold sb1qd
  exact mul_pos (inv_pos.2 hK) (mul_pos (Finset.prod_pos fun i _ => hρ _) (Real.exp_pos _))

theorem sb1_qd_lintegral {k : Euc d → ℝ} {β : ℝ} {ρ : Euc d → ℝ}
    (hρ : Whole.IsProbDensity ρ) (hK : 0 < Whole.gibbsNormalizer k N β (Whole.withDensityReal ρ)) :
    ∫⁻ X, ENNReal.ofReal (sb1qd k β N ρ X) = 1 := by
  set K := Whole.gibbsNormalizer k N β (Whole.withDensityReal ρ) with hKdef
  have hKint : K = ∫ X : Whole.EucConfig d N, (∏ i, ρ (X i)) * Real.exp (-β * N * sb1En k ρ X) :=
    sb1_gibbsNormalizer_eq hρ
  have hi : Integrable (fun X : Whole.EucConfig d N => (∏ i, ρ (X i)) * Real.exp (-β * N * sb1En k ρ X)) := by
    by_contra h
    rw [integral_undef h] at hKint
    linarith
  have hqi : Integrable (fun X : Whole.EucConfig d N => sb1qd k β N ρ X) := hi.const_mul _
  have hq0 : ∀ X, 0 ≤ sb1qd k β N ρ X := fun X => by
    unfold sb1qd
    exact mul_nonneg (inv_nonneg.2 hK.le) (mul_nonneg (Finset.prod_nonneg fun i _ => hρ.nonneg _)
      (Real.exp_pos _).le)
  rw [← ofReal_integral_eq_lintegral_ofReal hqi (Filter.Eventually.of_forall hq0)]
  have : ∫ X : Whole.EucConfig d N, sb1qd k β N ρ X = 1 := by
    unfold sb1qd
    rw [integral_const_mul, ← hKint, inv_mul_cancel₀ hK.ne']
  rw [this, ENNReal.ofReal_one]

end HRS.MS.MfeConf
