import HRS.MH.WpSpec2

/-!
# WpQ1: `HRS.MH.Wp.gfwp_sigN_pos`, `gfwp_energy_aux`, `gfwp_transport_cost_meas`

* `gfwp_sigN_pos`: `unfold sigN sigmaScale; split_ifs`, `S.hκ N`, `S.hinvβ N`, `lt_min`, `Real.sqrt_pos`, `div_pos`.
* `gfwp_energy_aux`: `gf_energy_integral_moment_proof` (GFB2Aux1.lean:245) without `hE`: the `hnn` block (GFB2Aux1:262-265),
  `gfb2_G_meas` (GFB2Aux3:44), `gfb2_G_eq` (GFB2Aux3:52), and the integrability argument of `gfb2_time_integral` (GFB2Aux1:161-166).
* `gfwp_transport_cost_meas`: first conjunct of `gfb2_transport_core` (GFB2Aux5.lean:77-99), plus the same with no `toReal`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MH.WpP

open HRS HRS.GF HRS.Uniform HRS.Uniform.Kot

theorem gfwp_sigN_pos_proof : type_of% @HRS.MH.Wp.gfwp_sigN_pos := by
  intro d S N hN
  unfold sigN sigmaScale
  split_ifs with h
  · exact S.hκ N
  · have hinv : 0 < S.invβ N := lt_of_le_of_ne (S.hinvβ N) (Ne.symm h)
    have hN0 : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.2 (by omega)
    exact lt_min (S.hκ N) (Real.sqrt_pos.2 (div_pos hN0 hinv))

/-- Sections of a jointly measurable function are measurable (used to avoid unfolding `gfb2_G` in unification). -/
theorem wpq1_section_meas {Ω : Type} [MeasurableSpace Ω] (F : ℝ × Ω → ℝ) (hF : Measurable F) (ω : Ω) :
    Measurable fun r : ℝ => F (r, ω) :=
  hF.comp measurable_prodMk_right

theorem gfwp_energy_aux_proof : type_of% @HRS.MH.Wp.gfwp_energy_aux := by
  intro d S M hMF N hN Ω mΩ P X₀ W X hX hF
  obtain ⟨ℱ, W', hFil⟩ := hF
  have hnn : ∀ᵐ ω ∂P, ∀ r ∈ Set.Icc (0 : ℝ) S.T, 0 ≤ S.energyCompletion N (X (Real.toNNReal r) ω) r := by
    filter_upwards [hX.no_collision] with ω hω r hr
    refine S.energy_nonneg N hN r hr _ (hω (Real.toNNReal r) ?_)
    rw [Real.coe_toNNReal r hr.1]; exact hr.2
  have hGm := gfb2_G_meas S M hMF N ℱ X hFil.progressive
  have hjm : Measurable fun q : ℝ × Ω => ENNReal.ofReal (gfb2_G S N X q.1 q.2) :=
    ENNReal.measurable_ofReal.comp hGm
  have hL : ∀ ω, (∫⁻ r in Set.Icc (0 : ℝ) S.T, ENNReal.ofReal (S.energyCompletion N (X (Real.toNNReal r) ω) r)) =
      ∫⁻ r in Set.Icc (0 : ℝ) S.T, ENNReal.ofReal (gfb2_G S N X r ω) := fun ω =>
    setLIntegral_congr_fun measurableSet_Icc fun r hr => by rw [gfb2_G_eq S N X hr ω]
  have hI : ∀ ω, (∫ r in Set.Icc (0 : ℝ) S.T, S.energyCompletion N (X (Real.toNNReal r) ω) r) =
      ∫ r in Set.Icc (0 : ℝ) S.T, gfb2_G S N X r ω := fun ω =>
    setIntegral_congr_fun measurableSet_Icc fun r hr => gfb2_G_eq S N X hr ω
  have hnnG : ∀ᵐ ω ∂P, ∀ r ∈ Set.Icc (0 : ℝ) S.T, 0 ≤ gfb2_G S N X r ω := by
    filter_upwards [hnn] with ω hω r hr
    rw [← gfb2_G_eq S N X hr ω]; exact hω r hr
  refine ⟨hnn, ?_, ?_⟩
  · have hmeas : Measurable fun ω => ∫⁻ r in Set.Icc (0 : ℝ) S.T, ENNReal.ofReal (gfb2_G S N X r ω) :=
      (hjm.comp measurable_swap).lintegral_prod_right'
    simp only [hL]
    exact hmeas
  · filter_upwards [hnnG] with ω hω hlt
    rw [hL ω] at hlt
    have hmeasω : Measurable fun r => gfb2_G S N X r ω := wpq1_section_meas _ hGm ω
    have hint : IntegrableOn (fun r => gfb2_G S N X r ω) (Set.Icc (0 : ℝ) S.T) := by
      refine ⟨hmeasω.aestronglyMeasurable, ?_⟩
      rw [HasFiniteIntegral]
      refine lt_of_le_of_lt (le_of_eq ?_) hlt
      refine setLIntegral_congr_fun measurableSet_Icc fun r hr => ?_
      rw [← ofReal_norm_eq_enorm, Real.norm_of_nonneg (hω r hr)]
    refine ⟨hint.congr_fun (fun r hr => (gfb2_G_eq S N X hr ω).symm) measurableSet_Icc, ?_⟩
    rw [hI ω, hL ω]
    exact ofReal_integral_eq_lintegral_ofReal hint
      ((ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall fun r hr => hω r hr))

theorem gfwp_transport_cost_meas_proof : type_of% @HRS.MH.Wp.gfwp_transport_cost_meas := by
  intro d S M hMF N hN Ω mΩ P X₀ W X hX hF
  obtain ⟨ℱ, W', hFil⟩ := hF
  have hT : 0 ≤ S.T := S.hT.le
  have hZ := gfb2_progressive_meas ℱ X hFil.progressive hT
  have hWm : Measurable fun p : ℝ × Ω => torusWassersteinE 2 (empirical (X (Real.toNNReal (Q54c.clampT S.T p.1)) p.2))
      (withDensityReal (S.ρ N (Q54c.clampT S.T p.1))) := by
    have h := (gfb2_W_meas S M hMF N (by omega)).comp (hZ.prodMk measurable_fst)
    exact h
  have hfm : Measurable fun p : ℝ × Ω => ENNReal.ofReal ((torusWassersteinE 2
      (empirical (X (Real.toNNReal (Q54c.clampT S.T p.1)) p.2))
      (withDensityReal (S.ρ N (Q54c.clampT S.T p.1)))).toReal ^ 2) :=
    ENNReal.measurable_ofReal.comp (hWm.ennreal_toReal.pow_const 2)
  have hcongr : ∀ ω, ∫⁻ r in Set.Icc (0 : ℝ) S.T, ENNReal.ofReal
      ((torusWassersteinE 2 (empirical (X (Real.toNNReal r) ω))
        (withDensityReal (S.ρ N r))).toReal ^ 2) =
      ∫⁻ r in Set.Icc (0 : ℝ) S.T, ENNReal.ofReal ((torusWassersteinE 2
      (empirical (X (Real.toNNReal (Q54c.clampT S.T r)) ω))
      (withDensityReal (S.ρ N (Q54c.clampT S.T r)))).toReal ^ 2) := fun ω =>
    setLIntegral_congr_fun measurableSet_Icc fun r hr => by simp only [Q54c.clampT_of_mem hr]
  have hcongr2 : ∀ ω, ∫⁻ r in Set.Icc (0 : ℝ) S.T,
      torusWassersteinE 2 (empirical (X (Real.toNNReal r) ω)) (withDensityReal (S.ρ N r)) ^ 2 =
      ∫⁻ r in Set.Icc (0 : ℝ) S.T, torusWassersteinE 2
      (empirical (X (Real.toNNReal (Q54c.clampT S.T r)) ω))
      (withDensityReal (S.ρ N (Q54c.clampT S.T r))) ^ 2 := fun ω =>
    setLIntegral_congr_fun measurableSet_Icc fun r hr => by simp only [Q54c.clampT_of_mem hr]
  refine ⟨?_, ?_⟩
  · simp only [hcongr]
    exact (hfm.comp measurable_swap).lintegral_prod_right' (ν := volume.restrict (Set.Icc (0 : ℝ) S.T))
  · simp only [hcongr2]
    exact ((hWm.pow_const 2).comp measurable_swap).lintegral_prod_right' (ν := volume.restrict (Set.Icc (0 : ℝ) S.T))

end HRS.MH.WpP
