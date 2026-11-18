import HRS.Main.Rel513RieszG

/-!
# HRS.Main.Rel513RieszH -- packet rel513, part 8: the `L²` norm of the linear part

For `f = H_μ - H_{m_N}` the centred empirical average `√N (μ_N(f) - m_N(f))` has `L²(Q_{N,β}(μ))`
norm at most `K' B δ_N` (`linearStat_variance`, exchangeability, `rel513_linear_L2`).
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.Main

variable {d : ℕ} {s : ℝ}

open HRS.MarginalAux HRS.PoleCavityAux

theorem rel513_modulatedGibbs_isProb (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {β : ℝ} (hβ : 0 < β)
    {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ) {N : ℕ} (hN : 0 < N) :
    IsProbabilityMeasure (modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρ)) := by
  have hlam : 0 ≤ β / (N : ℝ) := by positivity
  rw [modulatedGibbs_eq_cavity hd hs0 hsd hβ hρ N hN]
  exact cavity_isProb hd hs0 hsd β hρ N (β / N) hlam

theorem rel513_linear_eLpNorm (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {β : ℝ} (hβ : 0 < β)
    {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ N : ℕ, 2 ≤ N → ∀ B : ℝ, 0 ≤ B → ∀ h : Torus d → Torus d → ℝ,
      Measurable (Function.uncurry h) →
      (∀ x y, x ≠ y → |h x y| ≤ B * singEnvelope s (Torus.eucDist x y)) →
      eLpNorm (fun X : Config d N => Real.sqrt N *
          ((∫ y, (Quad.Hc h (withDensityReal ρ) y -
              Quad.Hc h (firstMarginal (modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρ))) y)
              ∂(empirical X))
            - ∫ y, (Quad.Hc h (withDensityReal ρ) y -
              Quad.Hc h (firstMarginal (modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρ))) y)
              ∂(firstMarginal (modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρ)))))
        2 (modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρ)) ≤
        ENNReal.ofReal (K * B * deltaN d s N) := by
  haveI hμ := isProbabilityMeasure_mu hρ
  obtain ⟨Clin, hClin⟩ := linearStat_variance hd hs0 hsd β hβ ρ hρ
  obtain ⟨K, hK0, hK⟩ := rel513_linear_L2 hd hs0 hsd hβ hρ
  obtain ⟨Mp, CF, hMp1, hCF0, hfacts⟩ := rel513_marginal_facts hd hs0 hsd hβ hρ
  refine ⟨Real.sqrt (|Clin| * K), Real.sqrt_nonneg _, fun N hN B hB h hm hh => ?_⟩
  have hN0 : 0 < N := by omega
  set μ := withDensityReal ρ with hμdef
  set Q := modulatedGibbs (periodicRiesz d s) N β μ with hQdef
  haveI hQ : IsProbabilityMeasure Q := rel513_modulatedGibbs_isProb hd hs0 hsd hβ hρ hN0
  set m := firstMarginal Q with hmdef
  obtain ⟨hmP, hmle, -, -⟩ := hfacts N hN
  haveI : IsProbabilityMeasure m := hmP
  obtain ⟨hmem, hint2⟩ := hK N hN B hB h hm hh
  set f : Torus d → ℝ := fun y => Quad.Hc h μ y - Quad.Hc h m y with hfdef
  have hfm : Measurable f := (Quad.measurable_Hc hm μ).sub (Quad.measurable_Hc hm m)
  have hmemm : MemLp f 2 m :=
    (hmem.smul_measure ENNReal.ofReal_ne_top).mono_measure hmle
  have hintm : Integrable f m := hmemm.integrable (by norm_num)
  have hex : IsExchangeable Q :=
    modulatedGibbs_isExchangeable _ _ _ (fun x => periodicRiesz_neg x)
  have hmean := rel513_integral_stat hN0 hex hfm hintm
  set Y : Config d N → ℝ := fun X => (N : ℝ)⁻¹ * ∑ i, f (X i) with hYdef
  have hYm : Measurable Y := by
    refine Measurable.const_mul (Finset.measurable_sum _ fun i _ => hfm.comp (measurable_pi_apply i)) _
  have hfun : (fun X : Config d N => Real.sqrt N * ((∫ y, f y ∂(empirical X)) - ∫ y, f y ∂m)) =
      fun X => Real.sqrt N * (Y X - ∫ X', Y X' ∂Q) := by
    funext X
    rw [rel513_integral_empirical]
    congr 2
    exact hmean.symm
  show eLpNorm (fun X : Config d N => Real.sqrt N * ((∫ y, f y ∂(empirical X)) - ∫ y, f y ∂m)) 2 Q ≤ _
  rw [hfun]
  have hsq := rel513_eLpNorm_sq_centered Q Y hYm.aestronglyMeasurable (Real.sqrt N)
  have hvar := hClin N hN f hfm hmem
  simp only [one_div] at hvar
  have hδ0 : 0 ≤ deltaN d s N := (Quad.deltaN_pos hd hs0 hsd (by omega : 1 ≤ N)).le
  have ha0 : 0 ≤ Real.sqrt (|Clin| * K) * B * deltaN d s N := by positivity
  refine rel513_le_of_sq_le ha0 ?_
  rw [hsq, Real.sq_sqrt (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
  refine hvar.trans (ENNReal.ofReal_le_ofReal ?_)
  have hi0 : 0 ≤ ∫ y, f y ^ 2 ∂μ := integral_nonneg fun y => sq_nonneg _
  calc Clin * ∫ y, f y ^ 2 ∂μ ≤ |Clin| * ∫ y, f y ^ 2 ∂μ :=
        mul_le_mul_of_nonneg_right (le_abs_self _) hi0
    _ ≤ |Clin| * (K * (B * deltaN d s N) ^ 2) :=
        mul_le_mul_of_nonneg_left hint2 (abs_nonneg _)
    _ = (Real.sqrt (|Clin| * K) * B * deltaN d s N) ^ 2 := by
        have e := Real.sq_sqrt (show 0 ≤ |Clin| * K from by positivity)
        calc |Clin| * (K * (B * deltaN d s N) ^ 2)
            = (|Clin| * K) * B ^ 2 * deltaN d s N ^ 2 := by ring
          _ = _ := by rw [mul_pow, mul_pow, e]

end HRS.Main

end
