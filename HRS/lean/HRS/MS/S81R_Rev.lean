import HRS.MS.S81R_Ident
import HRS.MS.S81R_Stat
import HRS.MS.S81R_Rew
import HRS.MS.S81R_Ratio

/-!
# S81R, packet R10a: the reweighted regularised flow is stationary and reversible on cylinder products

For the regularised solution `Y = Ys M` of the configuration SDE (drift `sb1DriftM D k_M N`) started at `X₀ ~ Γ` on a Brownian filtration,
there is a density `r` (ratio of the regularised to the singular Gibbs density, `r ≥ Z/Z_M`, `∫ r dΓ = 1`) such that, under `P' = r(X₀) P`,
`E' ∏ fₖ(Φ Y_{a₀+tₖ}) = E' ∏ fₖ(Φ Y_{a₀+T-tₖ})` for all test functions `fₖ ∈ s81r_S`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open HRS HRS.MP.SelfSimP4 HRS.MP.SelfSimP4Impl HRS.MS.MfeConf HRS.MS.PoisFlow HRS.MS.Gap HRS.MS.S81G
open scoped ENNReal NNReal

namespace HRS.MS.S81R

variable {d N : ℕ}

theorem s81r_smooth_rev {s a β : ℝ} (hd : 1 ≤ d) (hs : 0 ≤ s) (ha : 0 < a) (hβ : 0 < β) (M : ℕ)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {Pm : Measure Ω} [IsProbabilityMeasure Pm]
    {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ}
    (hBF : IsBrownianFiltration Pm ℱ W')
    {X0 : Ω → Whole.EucConfig d N} (hX0 : Measurable[ℱ 0] X0)
    (hlawX0 : Pm.map X0 = sb1Gam (Whole.quadraticGradientDyn d s a β) (Whole.rieszKernel d s) N)
    {Y : ℝ → Ω → Whole.EucConfig d N}
    (hYpath : ∀ᵐ ζ ∂Pm, IsPathSolution
      (fun _ => sb1DriftM (Whole.quadraticGradientDyn d s a β) (sb1kM d s M) N)
      (p4r_sigma d N (Whole.quadraticGradientDyn d s a β).invβ) (fun t => W' t ζ) (X0 ζ) ⊤
      (fun t => Y t ζ))
    {a0 T : ℝ} (ha0 : 0 ≤ a0) (n : ℕ) (t : Fin n → ℝ) (ht : ∀ i, t i ∈ Set.Icc 0 T)
    (f : Fin n → Euc (N * d) → ℝ) (hf : ∀ i, s81r_S (f i)) :
    ∃ r : Whole.EucConfig d N → ℝ, Measurable r ∧ (∀ x, 0 ≤ r x) ∧
      (∀ᵐ x ∂(Pm.map X0), sb1Gz (Whole.quadraticGradientDyn d s a β) (Whole.rieszKernel d s) N /
        sb1Gz (Whole.quadraticGradientDyn d s a β) (sb1kM d s M) N ≤ r x) ∧
      ∫⁻ x, ENNReal.ofReal (r x) ∂(Pm.map X0) = 1 ∧
      ∫ ζ, ∏ k, f k (s81r_Phi β d N (Y (a0 + t k) ζ))
          ∂(Pm.withDensity (fun ζ => ENNReal.ofReal (r (X0 ζ)))) =
        ∫ ζ, ∏ k, f k (s81r_Phi β d N (Y (a0 + T - t k) ζ))
          ∂(Pm.withDensity (fun ζ => ENNReal.ofReal (r (X0 ζ)))) := by
  set D := Whole.quadraticGradientDyn d s a β with hD
  obtain ⟨B0, hB0⟩ := s81g_pot (d := d) a
  have H : S81Hyp D :=
    ⟨hs, hd, inv_pos.2 hβ, by show Continuous (fun x : Euc d => a * ‖x‖ ^ 2 / 2); fun_prop,
      ⟨a / 2, 0, by positivity, fun x => s81g_conf_lower a x⟩⟩
  obtain ⟨ρ, G, hR, hlaw, hG⟩ := s81r_gapref (N := N) hd hs ha hβ M
  obtain ⟨r, hrm, hrpos, hQ, hrc⟩ := s81r_ratio (N := N) H M
  haveI hΓp : IsProbabilityMeasure (sb1Gam D (Whole.rieszKernel d D.s) N) := s81g_sing_prob H
  haveI hQp : IsProbabilityMeasure (sb1Gam D (sb1kM d D.s M) N) := s81g_reg_prob H M
  have hX0m : Measurable X0 := hX0.mono (ℱ.le 0) le_rfl
  have hmass : ∫⁻ x, ENNReal.ofReal (r x) ∂(sb1Gam D (Whole.rieszKernel d D.s) N) = 1 := by
    have h1 : (sb1Gam D (sb1kM d D.s M) N) Set.univ = 1 := measure_univ
    rw [hQ, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at h1
    exact h1
  refine ⟨r, hrm, fun x => (hrpos x).le, ?_, ?_, ?_⟩
  · rw [hlawX0]
    exact hrc
  · rw [hlawX0]
    exact hmass
  -- the reweighted measure
  set g : Ω → ℝ≥0∞ := fun ζ => ENNReal.ofReal (r (X0 ζ)) with hg
  have hgm0 : Measurable[ℱ 0] g := (hrm.ennreal_ofReal).comp hX0
  have hgm : Measurable g := hgm0.mono (ℱ.le 0) le_rfl
  have hg1 : ∫⁻ ζ, g ζ ∂Pm = 1 := by
    rw [hg, ← lintegral_map (hrm.ennreal_ofReal) hX0m, hlawX0]
    exact hmass
  have hgpos : ∀ᵐ ζ ∂Pm, g ζ ≠ 0 :=
    Filter.Eventually.of_forall fun ζ => (ENNReal.ofReal_pos.2 (hrpos _)).ne'
  haveI hP' : IsProbabilityMeasure (Pm.withDensity g) := by
    refine ⟨?_⟩
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, hg1]
  have hBD : IsBrownianFiltration Pm ℱ (fun t ω k' => W' t ω (finProdFinEquiv.symm k')) :=
    s81r_bf_reindex (finProdFinEquiv : Fin N × Fin d ≃ Fin (N * d)) hBF
  have hBD' := s81r_bf_withDensity hBD hgm0 hg1 hgpos
  -- the rescaled initial datum
  set z0 : Ω → Euc (N * d) := fun ζ => s81r_Phi β d N (X0 ζ) with hz0
  have hz0m : Measurable[ℱ 0] z0 :=
    (s81r_Phi β d N).continuous.measurable.comp hX0
  have hlawY : (Pm.withDensity g).map X0 = sb1Gam D (sb1kM d D.s M) N := by
    rw [hg, s81r_law_withDensity Pm hX0m (fun x => ENNReal.ofReal (r x)) hrm.ennreal_ofReal, hlawX0,
      hQ]
    rfl
  have hlawZ : (Pm.withDensity g).map z0 = Whole.withDensityReal ρ := by
    have : z0 = (s81r_PhiE hβ d N) ∘ X0 := rfl
    rw [this, ← Measure.map_map (s81r_PhiE hβ d N).continuous.measurable hX0m, hlawY]
    exact hlaw
  -- identification with the Pois flow, almost surely
  have hae : ∀ᵐ ζ ∂Pm, ∀ u : ℝ, 0 ≤ u → s81r_Phi β d N (Y u ζ) =
      flowMap a (gradient G) (fun v k' => W' v ζ (finProdFinEquiv.symm k')) u (z0 ζ) := by
    filter_upwards [hYpath] with ζ hy
    exact s81r_ident_flow ha hβ ρ G hR hG (hBF.cont ζ) (hBF.zero ζ) hy
  have hae' : ∀ᵐ ζ ∂(Pm.withDensity g), ∀ u : ℝ, 0 ≤ u → s81r_Phi β d N (Y u ζ) =
      flowMap a (gradient G) (fun v k' => W' v ζ (finProdFinEquiv.symm k')) u (z0 ζ) :=
    (withDensity_absolutelyContinuous _ _).ae_le hae
  obtain ⟨Mb2, hMb2⟩ := hR.cb 2
  have hcore := s81r_core_rev (P := Pm.withDensity g) hBD' ha hMb2 hR hz0m hlawZ ha0 n t ht f hf
  have hnn1 : ∀ k, 0 ≤ a0 + t k := fun k => by linarith [(ht k).1]
  have hnn2 : ∀ k, 0 ≤ a0 + T - t k := fun k => by linarith [(ht k).2]
  have e1 : ∫ ζ, ∏ k, f k (s81r_Phi β d N (Y (a0 + t k) ζ)) ∂(Pm.withDensity g) =
      ∫ ζ, ∏ k, f k (flowMap a (gradient G) (fun v k' => W' v ζ (finProdFinEquiv.symm k'))
        (a0 + t k) (z0 ζ)) ∂(Pm.withDensity g) := by
    refine integral_congr_ae ?_
    filter_upwards [hae'] with ζ hζ
    exact Finset.prod_congr rfl fun k _ => by rw [hζ _ (hnn1 k)]
  have e2 : ∫ ζ, ∏ k, f k (s81r_Phi β d N (Y (a0 + T - t k) ζ)) ∂(Pm.withDensity g) =
      ∫ ζ, ∏ k, f k (flowMap a (gradient G) (fun v k' => W' v ζ (finProdFinEquiv.symm k'))
        (a0 + T - t k) (z0 ζ)) ∂(Pm.withDensity g) := by
    refine integral_congr_ae ?_
    filter_upwards [hae'] with ζ hζ
    exact Finset.prod_congr rfl fun k _ => by rw [hζ _ (hnn2 k)]
  rw [e1, e2]
  exact hcore

end HRS.MS.S81R
