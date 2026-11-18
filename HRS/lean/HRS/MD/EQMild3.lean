import HRS.MD.EQMild1
import HRS.Sections.AdjKCFinal
import HRS.Sections.DynCmpAux1

/-!
# EQ-MILD, part 3: the stationary forcing is the evolving forcing plus a deterministic constant

For the constant trajectory `ρ^t ≡ ρ_β` and a stationary particle system (`P.map (X r) = ℙ_{N,β}` for `r ≤ T`), fix `t ∈ [0,T]` and a mode
`k`.  The integrand of `statForcingCoord` is the integrand `f(r,ω)` of `evolvingForcingCoord` plus the deterministic function
`e(r) = √N E_{ℙ_{N,β}} F_N^{h_r}(·; μ_β)` (`eqmild_stat_formula`).  Joint measurability comes from `adjk_forcing_intervalIntegrable_proof`,
the domination from `eqmild_mE_bound` (the dominating function is `ℙ_{N,β}`-integrable and `X_r ∼ ℙ_{N,β}`), and Fubini on `[0,t] × Ω`
gives
`statForcingCoord = evolvingForcingCoord + E` for every `ω` with an interval-integrable integrand (`E = ∫_0^t e`, deterministic), and
`E[evolvingForcingCoord] = -E`.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MD.EQMild

open HRS HRS.MD.EQ29 HRS.MD.EQRem HRS.Quad

variable {d : ℕ} {s β : ℝ} {V ρ₀ : Torus d → ℝ} {ρ : ℝ → Torus d → ℝ}

/-- The propagator of a mode is `C²` with a uniform `cbNorm 2` bound along `[0,t]`, `t ∈ [0,T]`. -/
theorem eqmild_prop_facts (hd : 2 ≤ d) (htr : IsSmoothPositiveTrajectory d s β V ρ₀ ρ) (T : ℝ)
    (k : NonzeroLattice d) :
    ∃ Cφ : ℝ, 0 ≤ Cφ ∧ ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ r ∈ Set.Icc (0 : ℝ) t,
      Torus.IsCk 2 (propagator htr.dyn ρ r t (Torus.realMode k)) ∧
      Torus.cbNorm 2 (propagator htr.dyn ρ r t (Torus.realMode k)) ≤ Cφ := by
  obtain ⟨Λ, -, -, hall⟩ := dyncmp_adjoint_package hd htr T
  obtain ⟨Cφ, hC⟩ := hall _ (HRS.FieldSingAux.isSmooth_realMode k)
  exact ⟨max Cφ 0, le_max_right _ _, fun t ht r hr =>
    ⟨(hC t ht).1.c2 r hr, ((hC t ht).2 r hr).trans (le_max_left _ _)⟩⟩

theorem eqmild_forcing_split (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hV : Torus.IsSmooth V)
    (hβ : 0 < β) {ρβ : Torus d → ℝ} (hρβ : IsThermalDensity (periodicRiesz d s) V β ρβ)
    (htr : IsSmoothPositiveTrajectory d s β V ρβ (fun _ => ρβ)) {T : ℝ} (hT : 0 ≤ T) {N : ℕ}
    (hN : 2 ≤ N) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N)
    (hX : IsParticleSystem P htr.dyn T X₀ W X)
    (hF : ∃ (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
      (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ), IsFilteredSolution P ℱ W' W X)
    (hstat : ∀ r : ℝ≥0, (r : ℝ) ≤ T → P.map (X r) = canonicalGibbs (periodicRiesz d s) V N β)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) (k : NonzeroLattice d) :
    ∃ E : ℝ,
      (∀ ω : Ω, IntervalIntegrable (fun r =>
          Real.sqrt N * modulatedEnergy
            (commKernel (periodicRieszGrad d htr.dyn.s)
              (Torus.grad (propagator htr.dyn (fun _ => ρβ) r t (Torus.realMode k))))
            (X r.toNNReal ω) (withDensityReal ((fun _ => ρβ) r))) volume 0 t →
        statForcingCoord d hs0 hsd V hβ ρβ X k t ω =
          evolvingForcingCoord htr.dyn (fun _ => ρβ) X k t ω + E) ∧
      Integrable (fun ω => evolvingForcingCoord htr.dyn (fun _ => ρβ) X k t ω) P ∧
      ∫ ω, evolvingForcingCoord htr.dyn (fun _ => ρβ) X k t ω ∂P = -E := by
  classical
  have hN0 : 0 < N := by omega
  haveI hGprob : IsProbabilityMeasure (canonicalGibbs (periodicRiesz d s) V N β) :=
    eqrem_gibbs_prob hd hs0 hsd V hV hβ hρβ hN0
  obtain ⟨Cφ, hCφ0, hCφ⟩ := eqmild_prop_facts hd htr T k
  obtain ⟨C₀, hC₀, hCenv⟩ := eqrem_pairKernel_envGood (d := d) (s := s) hd hs0 hsd
  obtain ⟨𝔅, h𝔅m, h𝔅0, h𝔅i, h𝔅b⟩ := eqmild_mE_bound hd hs0 hsd V hV hβ hρβ hN
  obtain ⟨-, hjm⟩ := HRS.AdjK.adjk_forcing_intervalIntegrable_proof hd htr hN P X₀ W X T hT hX hF
  have hjm' := hjm t ht k
  set G := canonicalGibbs (periodicRiesz d s) V N β with hG
  set φr : ℝ → Torus d → ℝ := fun r => propagator htr.dyn (fun _ => ρβ) r t (Torus.realMode k)
    with hφr
  set mE : ℝ → Config d N → ℝ := fun r Y =>
    modulatedEnergy (pairKernel d s (φr r)) Y (withDensityReal ρβ) with hmE
  set f : ℝ × Ω → ℝ := fun p => -(Real.sqrt N * mE p.1 (X p.1.toNNReal p.2)) with hf
  have hfm : AEMeasurable f ((volume.restrict (Set.Icc (0 : ℝ) t)).prod P) := hjm'.neg
  have hrT : ∀ r ∈ Set.Icc (0 : ℝ) t, ((r.toNNReal : ℝ≥0) : ℝ) ≤ T := fun r hr => by
    rw [Real.coe_toNNReal _ hr.1]; exact hr.2.trans ht.2
  have hbd : ∀ r ∈ Set.Icc (0 : ℝ) t, ∀ Y, |mE r Y| ≤ (C₀ * Cφ) * 𝔅 Y := by
    intro r hr Y
    obtain ⟨hck, hcb⟩ := hCφ t ht r hr
    have hg : EnvGood s (C₀ * Cφ) (pairKernel d s (φr r)) :=
      (hCenv _ hck).mono (mul_le_mul_of_nonneg_left hcb hC₀)
    exact h𝔅b _ _ hg Y
  obtain ⟨ℱ, W', hFil⟩ := hF
  have hXm : ∀ r ∈ Set.Icc (0 : ℝ) t, AEMeasurable (X r.toNNReal) P := fun r _ =>
    ((hFil.adapted r.toNNReal).mono (ℱ.le _) le_rfl).aemeasurable
  have hmeas_mE : ∀ r ∈ Set.Icc (0 : ℝ) t, Measurable (mE r) := fun r hr =>
    eqmild_mE_meas hd hs0 hsd V hV hβ hρβ hN (hCφ t ht r hr).1
  -- domination and integrability on the product
  set K : ℝ := Real.sqrt N * (C₀ * Cφ) with hK
  have hK0 : 0 ≤ K := mul_nonneg (Real.sqrt_nonneg _) (mul_nonneg hC₀ hCφ0)
  have hpw : ∀ r ∈ Set.Icc (0 : ℝ) t, ∀ ω, ‖f (r, ω)‖ₑ ≤
      ENNReal.ofReal K * ENNReal.ofReal (𝔅 (X r.toNNReal ω)) := by
    intro r hr ω
    rw [← ENNReal.ofReal_mul hK0, Real.enorm_eq_ofReal_abs]
    refine ENNReal.ofReal_le_ofReal ?_
    show |-(Real.sqrt N * mE r (X r.toNNReal ω))| ≤ _
    rw [abs_neg, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _), hK, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hbd r hr _) (Real.sqrt_nonneg _)
  have hinner : ∀ r ∈ Set.Icc (0 : ℝ) t, ∫⁻ ω, ‖f (r, ω)‖ₑ ∂P ≤
      ENNReal.ofReal K * ∫⁻ y, ENNReal.ofReal (𝔅 y) ∂G := by
    intro r hr
    have hm := lintegral_map' (μ := P) (f := fun y => ENNReal.ofReal (𝔅 y)) (g := X r.toNNReal)
      h𝔅m.ennreal_ofReal.aemeasurable (hXm r hr)
    rw [hstat r.toNNReal (hrT r hr)] at hm
    calc ∫⁻ ω, ‖f (r, ω)‖ₑ ∂P
        ≤ ∫⁻ ω, ENNReal.ofReal K * ENNReal.ofReal (𝔅 (X r.toNNReal ω)) ∂P :=
          lintegral_mono fun ω => hpw r hr ω
      _ = ENNReal.ofReal K * ∫⁻ ω, ENNReal.ofReal (𝔅 (X r.toNNReal ω)) ∂P :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ = _ := by rw [← hm]
  have hint : Integrable f ((volume.restrict (Set.Icc (0 : ℝ) t)).prod P) := by
    refine ⟨hfm.aestronglyMeasurable, ?_⟩
    unfold HasFiniteIntegral
    have h1 : ∫⁻ z, ‖f z‖ₑ ∂((volume.restrict (Set.Icc (0 : ℝ) t)).prod P) =
        ∫⁻ r, ∫⁻ ω, ‖f (r, ω)‖ₑ ∂P ∂(volume.restrict (Set.Icc (0 : ℝ) t)) :=
      lintegral_prod _ hfm.enorm
    rw [h1]
    calc ∫⁻ r, ∫⁻ ω, ‖f (r, ω)‖ₑ ∂P ∂(volume.restrict (Set.Icc (0 : ℝ) t))
        ≤ ∫⁻ r, ENNReal.ofReal K * ∫⁻ y, ENNReal.ofReal (𝔅 y) ∂G
            ∂(volume.restrict (Set.Icc (0 : ℝ) t)) :=
          lintegral_mono_ae (by
            filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
            exact hinner r hr)
      _ = (ENNReal.ofReal K * ∫⁻ y, ENNReal.ofReal (𝔅 y) ∂G) * ENNReal.ofReal t := by
          rw [lintegral_const, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
            Real.volume_Icc, sub_zero]
      _ < ⊤ := ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top h𝔅i.lintegral_lt_top)
          ENNReal.ofReal_lt_top
  -- pointwise expectation (stationarity)
  have hpt : ∀ r ∈ Set.Icc (0 : ℝ) t,
      ∫ ω, f (r, ω) ∂P = -(Real.sqrt N * ∫ Y, mE r Y ∂G) := by
    intro r hr
    have h1 : ∫ ω, mE r (X r.toNNReal ω) ∂P = ∫ Y, mE r Y ∂G := by
      rw [← hstat r.toNNReal (hrT r hr),
        integral_map (hXm r hr) (hmeas_mE r hr).aestronglyMeasurable]
    show ∫ ω, -(Real.sqrt N * mE r (X r.toNNReal ω)) ∂P = _
    rw [integral_neg, integral_const_mul, h1]
  -- Fubini consequences
  have hB : Integrable (fun r => ∫ ω, f (r, ω) ∂P) (volume.restrict (Set.Icc (0 : ℝ) t)) :=
    hint.integral_prod_left
  have hC : Integrable (fun ω => ∫ r, f (r, ω) ∂(volume.restrict (Set.Icc (0 : ℝ) t))) P :=
    hint.integral_prod_right
  have hD : ∫ ω, ∫ r, f (r, ω) ∂(volume.restrict (Set.Icc (0 : ℝ) t)) ∂P =
      ∫ r, ∫ ω, f (r, ω) ∂P ∂(volume.restrict (Set.Icc (0 : ℝ) t)) :=
    (integral_integral_swap (f := fun r ω => f (r, ω)) hint).symm
  have hecongr : (fun r => Real.sqrt N * ∫ Y, mE r Y ∂G) =ᵐ[volume.restrict (Set.Icc (0 : ℝ) t)]
      fun r => -(∫ ω, f (r, ω) ∂P) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
    rw [hpt r hr]; ring
  have heI : IntegrableOn (fun r => Real.sqrt N * ∫ Y, mE r Y ∂G) (Set.Icc (0 : ℝ) t) :=
    hB.neg.congr hecongr.symm
  have heI' : IntervalIntegrable (fun r => Real.sqrt N * ∫ Y, mE r Y ∂G) volume 0 t :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le ht.1).2 (heI.mono_set Set.Ioc_subset_Icc_self)
  have hev : ∀ ω, evolvingForcingCoord htr.dyn (fun _ => ρβ) X k t ω =
      ∫ r, f (r, ω) ∂(volume.restrict (Set.Icc (0 : ℝ) t)) := by
    intro ω
    show (∫ r in (0 : ℝ)..t, f (r, ω)) = _
    rw [intervalIntegral.integral_of_le ht.1, integral_Icc_eq_integral_Ioc]
  refine ⟨∫ r in (0 : ℝ)..t, Real.sqrt N * ∫ Y, mE r Y ∂G, ?_, ?_, ?_⟩
  · intro ω hω
    have hωI : IntervalIntegrable (fun r => f (r, ω)) volume 0 t := hω.neg
    have key : (∫ r in (0 : ℝ)..t, statRemainder d s V β ρβ (N := N) (φr r) (X r.toNNReal ω)) =
        ∫ r in (0 : ℝ)..t, (f (r, ω) + Real.sqrt N * ∫ Y, mE r Y ∂G) := by
      refine intervalIntegral.integral_congr (fun r hr => ?_)
      rw [Set.uIcc_of_le ht.1] at hr
      show statRemainder d s V β ρβ (N := N) (φr r) (X r.toNNReal ω) =
        -(Real.sqrt N * mE r (X r.toNNReal ω)) + Real.sqrt N * ∫ Y, mE r Y ∂G
      rw [eqmild_stat_formula hd hs0 hsd V hV hβ hρβ hN (hCφ t ht r hr).1 (X r.toNNReal ω)]
      show -(Real.sqrt N * (mE r (X r.toNNReal ω) - ∫ Y, mE r Y ∂G)) = _
      ring
    show (∫ r in (0 : ℝ)..t, statRemainder d s V β ρβ (N := N) (φr r) (X r.toNNReal ω)) =
      (∫ r in (0 : ℝ)..t, f (r, ω)) + ∫ r in (0 : ℝ)..t, Real.sqrt N * ∫ Y, mE r Y ∂G
    rw [key, intervalIntegral.integral_add hωI heI']
  · have : (fun ω => evolvingForcingCoord htr.dyn (fun _ => ρβ) X k t ω) =
        fun ω => ∫ r, f (r, ω) ∂(volume.restrict (Set.Icc (0 : ℝ) t)) := funext hev
    rw [this]; exact hC
  · calc ∫ ω, evolvingForcingCoord htr.dyn (fun _ => ρβ) X k t ω ∂P
        = ∫ ω, ∫ r, f (r, ω) ∂(volume.restrict (Set.Icc (0 : ℝ) t)) ∂P := by
          simp_rw [hev]
      _ = ∫ r, ∫ ω, f (r, ω) ∂P ∂(volume.restrict (Set.Icc (0 : ℝ) t)) := hD
      _ = ∫ r, -(Real.sqrt N * ∫ Y, mE r Y ∂G) ∂(volume.restrict (Set.Icc (0 : ℝ) t)) :=
          integral_congr_ae (by
            filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
            exact hpt r hr)
      _ = -(∫ r in Set.Icc (0 : ℝ) t, Real.sqrt N * ∫ Y, mE r Y ∂G) := integral_neg _
      _ = -(∫ r in (0 : ℝ)..t, Real.sqrt N * ∫ Y, mE r Y ∂G) := by
          rw [intervalIntegral.integral_of_le ht.1, integral_Icc_eq_integral_Ioc]

end HRS.MD.EQMild

end
