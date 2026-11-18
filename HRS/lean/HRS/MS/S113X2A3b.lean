import HRS.MS.S113X2A3a

/-!
# S11.3 X2 part A3b: killed laws increase to the particle law (removal of the localization)
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S113X2

open HRS HRS.Whole

variable {d N : ℕ}

open Classical in
/-- The killed law is dominated by the law of the particle. -/
theorem s113a_killedLaw_le {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (D : Set (EucConfig d N)) (X₀ : Ω → EucConfig d N) (X : ℝ≥0 → Ω → EucConfig d N)
    (chi : EucConfig d N → ℝ) (hchi1 : ∀ z, chi z ≤ 1) (t : ℝ≥0) (hXt : Measurable (X t)) :
    s113a_killedLaw P D X₀ X chi t ≤ P.map (X t) := by
  refine Measure.le_iff.2 fun A hA => ?_
  unfold s113a_killedLaw
  rw [Measure.map_apply hXt hA, Measure.map_apply hXt hA, withDensity_apply _ (hXt hA)]
  calc ∫⁻ w in X t ⁻¹' A, (if w ∈ s113a_survives D X t then ENNReal.ofReal (chi (X₀ w)) else 0) ∂P
      ≤ ∫⁻ _ in X t ⁻¹' A, 1 ∂P := lintegral_mono fun w => by
        split_ifs
        · exact ENNReal.ofReal_le_one.2 (hchi1 _)
        · exact bot_le
    _ = P (X t ⁻¹' A) := by simp

open Classical in
/-- The weight of the killed law is a.e. measurable. -/
theorem s113a_weight_aemeasurable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {s q β : ℝ}
    {X₀ : Ω → EucConfig d N} {W : ℝ≥0 → Ω → (Fin N → Euc d)} {X : ℝ≥0 → Ω → EucConfig d N}
    (hX : MovParticleSetup P d s q β N X₀ W X) (D : Set (EucConfig d N)) (hD : IsOpen D)
    (chi : EucConfig d N → ℝ) (hchi : Measurable chi) (t : ℝ≥0) :
    AEMeasurable (fun ζ => if ζ ∈ s113a_survives D X t then ENNReal.ofReal (chi (X₀ ζ)) else 0) P := by
  obtain ⟨ℱ, W', hF, τ, hτ, hτg⟩ := s113a_setup hX D hD
  have hsol := hX.sol 0
  refine ⟨fun ζ => if ((t : ℝ) : WithTop ℝ) < τ ζ then ENNReal.ofReal (chi (X 0 ζ)) else 0, ?_, ?_⟩
  · exact Measurable.ite ((s113a_measurableSet_lt_stopping hτ).preimage
      (measurable_prodMk_left (x := (t : ℝ)))) (ENNReal.measurable_ofReal.comp (hchi.comp (hsol.adapted 0)))
      measurable_const
  · filter_upwards [hτg, hsol.init] with ζ h1 h2
    simp only [h2]
    by_cases hs : ζ ∈ s113a_survives D X t
    · rw [if_pos hs, if_pos ((h1.1 t).1 hs)]
    · rw [if_neg hs, if_neg (fun h => hs ((h1.1 t).2 h))]

open Classical in
/-- Removal of the localization: the killed laws have total mass tending to `1`. -/
theorem s113a_killedLaw_mass_tendsto {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {s q β : ℝ}
    {X₀ : Ω → EucConfig d N} {W : ℝ≥0 → Ω → (Fin N → Euc d)} {X : ℝ≥0 → Ω → EucConfig d N}
    (hX : MovParticleSetup P d s q β N X₀ W X) (D : ℕ → Set (EucConfig d N))
    (hDo : ∀ n, IsOpen (D n)) (hDm : Monotone D) (hDU : (⋃ n, D n) = (eucCollisionSet d N)ᶜ)
    (chi : ℕ → EucConfig d N → ℝ) (hchi : ∀ n, Measurable (chi n)) (hchi1 : ∀ n z, chi n z ≤ 1)
    (hchi0 : ∀ n z, 0 ≤ chi n z)
    (hlim : ∀ᵐ ζ ∂P, Tendsto (fun n => chi n (X₀ ζ)) atTop (𝓝 1)) (t : ℝ≥0) :
    Tendsto (fun n => s113a_killedLaw P (D n) X₀ X (chi n) t Set.univ) atTop (𝓝 (P.map (X t) Set.univ)) := by
  have hsol := hX.sol t
  have hmass : ∀ n, s113a_killedLaw P (D n) X₀ X (chi n) t Set.univ =
      ∫⁻ ζ, (if ζ ∈ s113a_survives (D n) X t then ENNReal.ofReal (chi n (X₀ ζ)) else 0) ∂P := by
    intro n
    unfold s113a_killedLaw
    rw [Measure.map_apply (hsol.adapted t) MeasurableSet.univ, Set.preimage_univ,
      withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  rw [Measure.map_apply (hsol.adapted t) MeasurableSet.univ, Set.preimage_univ, measure_univ]
  simp_rw [hmass]
  have key := tendsto_lintegral_of_dominated_convergence' (μ := P) (bound := fun _ => 1)
    (F := fun n ζ => if ζ ∈ s113a_survives (D n) X t then ENNReal.ofReal (chi n (X₀ ζ)) else 0)
    (f := fun _ => 1)
    (fun n => s113a_weight_aemeasurable hX (D n) (hDo n) (chi n) (hchi n) t)
    (fun n => ae_of_all _ fun ζ => by
      beta_reduce
      split_ifs
      · exact ENNReal.ofReal_le_one.2 (hchi1 _ _)
      · exact bot_le)
    (by simp) ?_
  · simpa using key
  · filter_upwards [hlim, hsol.cont, hsol.no_collision] with ζ h1 hc hnc
    -- the path stays in some `D n`
    set γ : ℝ → EucConfig d N := fun r => X r.toNNReal ζ with hγ
    have hγc : Continuous γ := (continuous_pi hc).comp continuous_real_toNNReal
    have hK : IsCompact (γ '' Set.Icc 0 (t : ℝ)) := (isCompact_Icc).image hγc
    have hKfree : γ '' Set.Icc 0 (t : ℝ) ⊆ ⋃ n, D n := by
      rintro _ ⟨r, hr, rfl⟩
      rw [hDU]
      have := hnc r.toNNReal (by rw [Real.coe_toNNReal _ hr.1]; exact hr.2)
      exact this
    obtain ⟨n0, hn0⟩ := hK.elim_directed_cover D hDo hKfree hDm.directed_le
    have hev : ∀ᶠ n in atTop, (if ζ ∈ s113a_survives (D n) X t then ENNReal.ofReal (chi n (X₀ ζ)) else 0)
        = ENNReal.ofReal (chi n (X₀ ζ)) := by
      filter_upwards [eventually_ge_atTop n0] with n hn
      have : ζ ∈ s113a_survives (D n) X t := by
        intro r hr
        refine hDm hn (hn0 ⟨(r : ℝ), ⟨r.2, by exact_mod_cast hr⟩, ?_⟩)
        simp [hγ]
      rw [if_pos this]
    refine Tendsto.congr' (hev.mono fun n hn => hn.symm) ?_
    simpa using (ENNReal.tendsto_ofReal h1)

end HRS.MS.S113X2

end
