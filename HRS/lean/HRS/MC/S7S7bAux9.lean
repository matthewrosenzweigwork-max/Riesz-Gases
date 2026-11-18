import HRS.MC.S7S7bAux8

/-!
# Packet `s7_S7b_weighted_moments`, helper 9: `iint h_v^2 dmu dmu <= C sum_j ||v_j||_{H^1}^2`
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ComplexConjugate

noncomputable section

namespace HRS.MC.Sec7.S7b

open HRS HRS.Sec7 HRS.MC.SEdge HRS.PDE

variable {d : ℕ} {s : ℝ}

theorem s7b_hv_L2 (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) {ρ : Torus d → ℝ}
    (hρ : SmoothPosDensity ρ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v : Fin d → Torus d → ℝ, (∀ j, Torus.IsSmooth (v j)) →
      (∀ j, MemHs (1 : ℝ) (coeffOf (v j))) →
      ∫ x, ∫ y, Q66.q66_hv d s v x y ^ 2 ∂(withDensityReal ρ) ∂(withDensityReal ρ) ≤
        C * ∑ j, hsNormSq (1 : ℝ) (coeffOf (v j)) := by
  have hsd : s < (d : ℝ) := by
    have : (0 : ℝ) ≤ d := by positivity
    linarith
  have hd0 : 1 ≤ d := by omega
  haveI hμ : IsProbabilityMeasure (withDensityReal ρ) := HRS.MC.SEdge.B3.b3_prob hρ
  obtain ⟨Λ, hΛpos, hΛ⟩ := PoleCavityAux.exists_density_bound hρ
  obtain ⟨K, c, hK0, hw, hgd⟩ := s7b_grad_dist hd hs0 hs
  have hg2 : Integrable (fun z : Torus d => periodicRiesz d s z ^ 2) :=
    HRS.InitialDataAux.riesz_sq_integrable_volume hd hs0 hs
  have hIint : Integrable
      (fun z : Torus d => 2 * K ^ 2 * periodicRiesz d s z ^ 2 + 2 * K ^ 2 * c ^ 2) :=
    (hg2.const_mul _).add (integrable_const _)
  set I : ℝ := ∫ z : Torus d, (2 * K ^ 2 * periodicRiesz d s z ^ 2 + 2 * K ^ 2 * c ^ 2) with hI
  have hI0 : 0 ≤ I := integral_nonneg fun z => by positivity
  refine ⟨Λ * Λ * I, by positivity, fun v hv hvH => ?_⟩
  have hvc : ∀ j, Continuous (v j) := fun j => HRS.StaticLimitAux.continuous_of_smooth (hv j)
  have hFm : Measurable (Function.uncurry (Q66.q66_hv d s v)) :=
    Q66.q66_hv_measurable hsd hvc
  set Fv : Torus d → Torus d → ℝ≥0∞ := fun x y => ENNReal.ofReal (Q66.q66_hv d s v x y ^ 2)
    with hFv
  have hFvm : Measurable (Function.uncurry Fv) := (hFm.pow_const 2).ennreal_ofReal
  set Hs : ℝ := ∑ j, hsNormSq (1 : ℝ) (coeffOf (v j)) with hHs
  have hH0 : ∀ j, 0 ≤ hsNormSq (1 : ℝ) (coeffOf (v j)) := fun j =>
    tsum_nonneg fun k => mul_nonneg (MFProduct.sobWeight_nonneg _ k) (sq_nonneg _)
  have hHs0 : 0 ≤ Hs := Finset.sum_nonneg fun j _ => hH0 j
  -- Step A and B
  have hAB : ∫⁻ x, ∫⁻ y, Fv x y ∂(withDensityReal ρ) ∂(withDensityReal ρ) ≤
      ENNReal.ofReal Λ * (ENNReal.ofReal Λ * ∫⁻ z : Torus d, ∫⁻ y, Fv (y + z) y) := by
    rw [← s7b_lintegral_shift Fv hFvm]
    calc ∫⁻ x, ∫⁻ y, Fv x y ∂(withDensityReal ρ) ∂(withDensityReal ρ)
        ≤ ∫⁻ x, (ENNReal.ofReal Λ * ∫⁻ y, Fv x y) ∂(withDensityReal ρ) :=
          lintegral_mono fun x => s7b_lintegral_density_le hΛ _
      _ = ENNReal.ofReal Λ * ∫⁻ x, (∫⁻ y, Fv x y) ∂(withDensityReal ρ) :=
          lintegral_const_mul' (ENNReal.ofReal Λ)
            (fun x => ∫⁻ y, Fv x y) ENNReal.ofReal_ne_top
      _ ≤ _ := mul_le_mul' le_rfl (s7b_lintegral_density_le hΛ (fun x => ∫⁻ y, Fv x y))
  -- Step C
  have hC : ∀ z : Torus d, ∫⁻ y, Fv (y + z) y ≤
      ENNReal.ofReal (‖periodicRieszGrad d s z‖ ^ 2 * (‖Torus.centeredRep z‖ ^ 2 * Hs)) := by
    intro z
    have hsh : ∀ j, ∫⁻ y, ENNReal.ofReal ((v j (y + z) - v j y) ^ 2) ≤
        ENNReal.ofReal (‖Torus.centeredRep z‖ ^ 2 * hsNormSq (1 : ℝ) (coeffOf (v j))) := by
      intro j
      have hcont : Continuous (fun y => (v j (y + z) - v j y) ^ 2) :=
        (((hvc j).comp (continuous_id.add continuous_const)).sub (hvc j)).pow 2
      have hint : Integrable (fun y : Torus d => (v j (y + z) - v j y) ^ 2) :=
        hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
      rw [← ofReal_integral_eq_lintegral_ofReal hint
        (Filter.Eventually.of_forall fun y => sq_nonneg _)]
      refine ENNReal.ofReal_le_ofReal ?_
      have hmem : MemHs (1 : ℝ) (coeffOf (v j)) := hvH j
      exact s7b_shift_L2 (hvc j) hmem z
    calc ∫⁻ y, Fv (y + z) y
        ≤ ∫⁻ y, ENNReal.ofReal (‖periodicRieszGrad d s z‖ ^ 2) *
            ∑ j, ENNReal.ofReal ((v j (y + z) - v j y) ^ 2) := by
          refine lintegral_mono fun y => ?_
          simp only [hFv]
          rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => sq_nonneg _),
            ← ENNReal.ofReal_mul (sq_nonneg _)]
          refine ENNReal.ofReal_le_ofReal ?_
          have := s7b_hv_sq_le (s := s) (v := v) (y + z) y
          rwa [add_sub_cancel_left] at this
      _ = ENNReal.ofReal (‖periodicRieszGrad d s z‖ ^ 2) *
            ∑ j, ∫⁻ y, ENNReal.ofReal ((v j (y + z) - v j y) ^ 2) := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_finsetSum]
          intro j _
          exact (((hvc j).comp (continuous_id.add continuous_const)).sub (hvc j)).pow 2
            |>.measurable.ennreal_ofReal
      _ ≤ ENNReal.ofReal (‖periodicRieszGrad d s z‖ ^ 2) *
            ∑ j, ENNReal.ofReal (‖Torus.centeredRep z‖ ^ 2 * hsNormSq (1 : ℝ) (coeffOf (v j))) :=
          mul_le_mul' le_rfl (Finset.sum_le_sum fun j _ => hsh j)
      _ = _ := by
          rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => mul_nonneg (sq_nonneg _) (hH0 j)),
            ← ENNReal.ofReal_mul (sq_nonneg _), ← Finset.mul_sum]
  -- Step D
  have hz0 : ∀ᵐ z : Torus d ∂(volume : Measure (Torus d)), z ≠ 0 := by
    rw [ae_iff]
    simpa using HRS.volume_singleton_torus hd0 0
  have hD : ∫⁻ z : Torus d, ∫⁻ y, Fv (y + z) y ≤ ENNReal.ofReal (I * Hs) := by
    calc ∫⁻ z : Torus d, ∫⁻ y, Fv (y + z) y
        ≤ ∫⁻ z : Torus d, ENNReal.ofReal
            ((2 * K ^ 2 * periodicRiesz d s z ^ 2 + 2 * K ^ 2 * c ^ 2) * Hs) := by
          refine lintegral_mono_ae ?_
          filter_upwards [hz0] with z hz
          refine (hC z).trans (ENNReal.ofReal_le_ofReal ?_)
          have h1 := hgd z hz
          have h2 : (‖periodicRieszGrad d s z‖ * ‖Torus.centeredRep z‖) ^ 2 ≤
              (K * (periodicRiesz d s z + c)) ^ 2 :=
            pow_le_pow_left₀ (by positivity) h1 2
          have h3 : (K * (periodicRiesz d s z + c)) ^ 2 ≤
              2 * K ^ 2 * periodicRiesz d s z ^ 2 + 2 * K ^ 2 * c ^ 2 := by
            nlinarith [sq_nonneg K, mul_nonneg (sq_nonneg K) (sq_nonneg (periodicRiesz d s z - c))]
          calc ‖periodicRieszGrad d s z‖ ^ 2 * (‖Torus.centeredRep z‖ ^ 2 * Hs)
              = (‖periodicRieszGrad d s z‖ * ‖Torus.centeredRep z‖) ^ 2 * Hs := by ring
            _ ≤ _ := mul_le_mul_of_nonneg_right (h2.trans h3) hHs0
      _ = ENNReal.ofReal (∫ z : Torus d,
            (2 * K ^ 2 * periodicRiesz d s z ^ 2 + 2 * K ^ 2 * c ^ 2) * Hs) := by
          rw [ofReal_integral_eq_lintegral_ofReal (hIint.mul_const Hs)
            (Filter.Eventually.of_forall fun z => by positivity)]
      _ = ENNReal.ofReal (I * Hs) := by rw [hI, integral_mul_const]
  -- conclusion
  have hL : ∫⁻ x, ∫⁻ y, Fv x y ∂(withDensityReal ρ) ∂(withDensityReal ρ) ≤
      ENNReal.ofReal (Λ * Λ * I * Hs) := by
    refine hAB.trans ?_
    calc ENNReal.ofReal Λ * (ENNReal.ofReal Λ * ∫⁻ z : Torus d, ∫⁻ y, Fv (y + z) y)
        ≤ ENNReal.ofReal Λ * (ENNReal.ofReal Λ * ENNReal.ofReal (I * Hs)) := by
          gcongr
      _ = ENNReal.ofReal (Λ * Λ * I * Hs) := by
          rw [← ENNReal.ofReal_mul hΛpos.le, ← ENNReal.ofReal_mul hΛpos.le]
          congr 1; ring
  -- back to the Bochner integral
  have hint := HRS.MC.SEdge.B2b.sed_B2b_hs_proof hd hs0 hs hρ hv
  rw [show (∫ x, ∫ y, Q66.q66_hv d s v x y ^ 2 ∂(withDensityReal ρ) ∂(withDensityReal ρ)) =
      ∫ p : Torus d × Torus d, Q66.q66_hv d s v p.1 p.2 ^ 2
        ∂((withDensityReal ρ).prod (withDensityReal ρ)) from (integral_prod _ hint).symm]
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun p => sq_nonneg _)
    hint.aestronglyMeasurable]
  have hprod : ∫⁻ p : Torus d × Torus d, ENNReal.ofReal (Q66.q66_hv d s v p.1 p.2 ^ 2)
      ∂((withDensityReal ρ).prod (withDensityReal ρ)) =
      ∫⁻ x, ∫⁻ y, Fv x y ∂(withDensityReal ρ) ∂(withDensityReal ρ) :=
    lintegral_prod _ hFvm.aemeasurable
  rw [hprod]
  have := ENNReal.toReal_le_of_le_ofReal (by positivity) hL
  calc _ ≤ Λ * Λ * I * Hs := this
    _ = _ := by ring

end HRS.MC.Sec7.S7b

end
