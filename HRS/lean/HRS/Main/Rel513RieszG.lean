import HRS.Main.Rel513RieszF

/-!
# HRS.Main.Rel513RieszG -- packet rel513, part 7: the linear part

`f = H_μ - H_{m_N}` satisfies `‖f‖²_{L²(μ)} ≤ K (B δ_N)²` (`change_term_le` with `π = μ`, `ν = m_N`,
`m_N ≤ M_p μ`, and `‖dm_N/dμ - 1‖_{L²(μ)} ≤ C δ_N`), and then the `L²(Q_{N,β}(μ))` norm of
`√N (μ_N(f) - m_N(f))` is at most `C B δ_N` (`linearStat_variance`, exchangeability).
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.Main

variable {d : ℕ} {s : ℝ}

open HRS.MarginalAux HRS.PoleCavityAux

theorem rel513_enorm_sq (x : ℝ) : ‖x‖ₑ ^ 2 = ENNReal.ofReal (x ^ 2) := by
  rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _), Real.norm_eq_abs, sq_abs]

theorem rel513_linear_L2 (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {β : ℝ} (hβ : 0 < β)
    {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ N : ℕ, 2 ≤ N → ∀ B : ℝ, 0 ≤ B → ∀ h : Torus d → Torus d → ℝ,
      Measurable (Function.uncurry h) →
      (∀ x y, x ≠ y → |h x y| ≤ B * singEnvelope s (Torus.eucDist x y)) →
      MemLp (fun y => Quad.Hc h (withDensityReal ρ) y -
          Quad.Hc h (firstMarginal (modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρ))) y)
        2 (withDensityReal ρ) ∧
      ∫ y, (Quad.Hc h (withDensityReal ρ) y -
          Quad.Hc h (firstMarginal (modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρ))) y) ^ 2
        ∂(withDensityReal ρ) ≤ K * (B * deltaN d s N) ^ 2 := by
  haveI hμ := isProbabilityMeasure_mu hρ
  obtain ⟨Mp, CF, hMp1, hCF0, hfacts⟩ := rel513_marginal_facts hd hs0 hsd hβ hρ
  obtain ⟨Λ, hΛ0, hΛ⟩ := HRS.PoleCavityAux.exists_density_bound hρ
  obtain ⟨c, hc, hch⟩ := Quad.change_term_le hd hs0 hsd
  refine ⟨c * Mp * Λ ^ 2 * CF ^ 2, by positivity, fun N hN B hB h hm hh => ?_⟩
  obtain ⟨hmP, hmle, hmac, hmL2⟩ := hfacts N hN
  set μ := withDensityReal ρ with hμdef
  set m := firstMarginal (modulatedGibbs (periodicRiesz d s) N β μ) with hmdef
  have hμle : μ ≤ ENNReal.ofReal Mp • μ := by
    refine Measure.le_iff'.2 fun A => ?_
    rw [Measure.smul_apply, smul_eq_mul]
    exact le_mul_of_one_le_left bot_le (ENNReal.one_le_ofReal.2 hMp1)
  have key := hch (ρ := ρ) (Λ := Λ) hΛ hΛ0.le (Cp := Mp) (by linarith) hB hm hh (π := μ) (ν := m)
    hμle hmle (Measure.AbsolutelyContinuous.refl _) hmac
  have hδ0 : 0 ≤ deltaN d s N := (Quad.deltaN_pos hd hs0 hsd (by omega : 1 ≤ N)).le
  have hdiff : eLpNorm (fun y => (m.rnDeriv μ y).toReal - (μ.rnDeriv μ y).toReal) 2 μ ≤
      ENNReal.ofReal (CF * deltaN d s N) := by
    refine le_trans (le_of_eq ?_) hmL2
    refine eLpNorm_congr_ae ?_
    filter_upwards [Measure.rnDeriv_self μ] with y hy
    simp [hy]
  have hHμ := Quad.measurable_Hc hm μ
  have hHm := Quad.measurable_Hc hm m
  have hfm : Measurable (fun y => Quad.Hc h μ y - Quad.Hc h m y) := hHμ.sub hHm
  have hS : ∫⁻ y, ‖Quad.Hc h μ y - Quad.Hc h m y‖ₑ ^ 2 ∂μ ≤
      ENNReal.ofReal (c * Mp * Λ ^ 2 * B ^ 2) * ENNReal.ofReal (CF * deltaN d s N) ^ 2 := by
    calc ∫⁻ y, ‖Quad.Hc h μ y - Quad.Hc h m y‖ₑ ^ 2 ∂μ
        = ∫⁻ y, ‖Quad.Hc h m y - Quad.Hc h μ y‖ₑ ^ 2 ∂μ := by
          refine lintegral_congr fun y => ?_
          rw [enorm_sub_rev]
      _ ≤ _ := key
      _ ≤ _ := by gcongr
  have hsq : ∫⁻ y, ‖Quad.Hc h μ y - Quad.Hc h m y‖ₑ ^ 2 ∂μ =
      (eLpNorm (fun y => Quad.Hc h μ y - Quad.Hc h m y) 2 μ) ^ 2 :=
    Quad.lintegral_enorm_sq_eq_eLpNorm_sq hfm.aestronglyMeasurable
  have hA0 : 0 ≤ c * Mp * Λ ^ 2 * B ^ 2 * (CF * deltaN d s N) ^ 2 := by positivity
  have hS' : ∫⁻ y, ‖Quad.Hc h μ y - Quad.Hc h m y‖ₑ ^ 2 ∂μ ≤
      ENNReal.ofReal (c * Mp * Λ ^ 2 * B ^ 2 * (CF * deltaN d s N) ^ 2) := by
    refine hS.trans (le_of_eq ?_)
    rw [← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  have hfin : eLpNorm (fun y => Quad.Hc h μ y - Quad.Hc h m y) 2 μ < ∞ := by
    by_contra hcon
    rw [not_lt, top_le_iff] at hcon
    rw [hcon] at hsq
    have := hS'.trans_lt ENNReal.ofReal_lt_top
    rw [hsq] at this
    simp at this
  have hmem : MemLp (fun y => Quad.Hc h μ y - Quad.Hc h m y) 2 μ := hfin
  refine ⟨hmem, ?_⟩
  have hint := hmem.integrable_sq
  have e1 : ENNReal.ofReal (∫ y, (Quad.Hc h μ y - Quad.Hc h m y) ^ 2 ∂μ) =
      ∫⁻ y, ‖Quad.Hc h μ y - Quad.Hc h m y‖ₑ ^ 2 ∂μ := by
    rw [ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun y => sq_nonneg _)]
    exact lintegral_congr fun y => (rel513_enorm_sq _).symm
  have h3 : ENNReal.ofReal (∫ y, (Quad.Hc h μ y - Quad.Hc h m y) ^ 2 ∂μ) ≤
      ENNReal.ofReal (c * Mp * Λ ^ 2 * B ^ 2 * (CF * deltaN d s N) ^ 2) := by
    rw [e1]; exact hS'
  have h4 := (ENNReal.ofReal_le_ofReal_iff hA0).1 h3
  calc _ ≤ _ := h4
    _ = _ := by ring

end HRS.Main

end
