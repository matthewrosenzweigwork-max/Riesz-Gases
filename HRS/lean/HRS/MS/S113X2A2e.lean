import HRS.MS.S113X2A2d

/-!
# S11.3 X2 part A2e: the killed law has the smooth Weyl density at every time in `(0,T)`
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S113X2

open HRS HRS.Whole

variable {d N : ℕ}

open Classical in
theorem s113a_killedLaw_finite {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (D : Set (EucConfig d N)) (X₀ : Ω → EucConfig d N) (X : ℝ≥0 → Ω → EucConfig d N)
    (chi : EucConfig d N → ℝ) (hchi1 : ∀ z, chi z ≤ 1) (t : ℝ≥0) :
    IsFiniteMeasure (s113a_killedLaw P D X₀ X chi t) := by
  unfold s113a_killedLaw
  haveI : IsFiniteMeasure (P.withDensity fun w =>
      if w ∈ s113a_survives D X t then ENNReal.ofReal (chi (X₀ w)) else 0) := by
    refine ⟨?_⟩
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    calc ∫⁻ w, (if w ∈ s113a_survives D X t then ENNReal.ofReal (chi (X₀ w)) else 0) ∂P
        ≤ ∫⁻ _, 1 ∂P := lintegral_mono fun w => by
          split_ifs
          · exact ENNReal.ofReal_le_one.2 (hchi1 _)
          · exact bot_le
      _ = 1 := by simp
      _ < ⊤ := ENNReal.one_lt_top
  infer_instance

open Classical in
theorem s113a_killedLaw_compl {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (D : Set (EucConfig d N)) (hD : IsOpen D) (X₀ : Ω → EucConfig d N) (X : ℝ≥0 → Ω → EucConfig d N)
    (chi : EucConfig d N → ℝ) (t : ℝ≥0) (hXt : Measurable (X t)) :
    s113a_killedLaw P D X₀ X chi t Dᶜ = 0 := by
  unfold s113a_killedLaw
  rw [Measure.map_apply hXt hD.isClosed_compl.measurableSet]
  have hw : ∀ w ∈ X t ⁻¹' Dᶜ, (if w ∈ s113a_survives D X t then ENNReal.ofReal (chi (X₀ w)) else 0) = 0 := by
    intro w hw
    have : w ∉ s113a_survives D X t := fun h => hw (h t le_rfl)
    simp [this]
  have hm : MeasurableSet (X t ⁻¹' Dᶜ) := hXt hD.isClosed_compl.measurableSet
  rw [withDensity_apply _ hm, setLIntegral_congr_fun hm hw]
  simp

theorem s113a_integrable_smul_cont {T : ℝ} {θ : ℝ → ℝ} (hθ : Continuous θ) (hθc : HasCompactSupport θ)
    (hθs : tsupport θ ⊆ Set.Ioo 0 T) {h : ℝ → ℝ} (hh : ContinuousOn h (Set.Ioo 0 T)) :
    Integrable (fun t => θ t * h t) := by
  have hon : IntegrableOn (fun t => θ t * h t) (tsupport θ) :=
    (hθ.continuousOn.mul (hh.mono hθs)).integrableOn_compact hθc.isCompact
  refine (integrableOn_iff_integrable_of_support_subset ?_).1 hon
  intro t ht
  by_contra h'
  exact ht (show θ t * h t = 0 by rw [image_eq_zero_of_notMem_tsupport h', zero_mul])

/-- Continuity in time of `t ↦ ∫ ψ(x) F(t,x) dx` on `(0,T)`. -/
theorem s113a_density_pairing_continuousOn {T : ℝ} {D : Set (EucConfig d N)} (hD : IsOpen D)
    {F : ℝ × EucConfig d N → ℝ} (hFc : ContinuousOn F (Set.Ioo 0 T ×ˢ D))
    {ψ : EucConfig d N → ℝ} (hψ : Continuous ψ) (hψc : HasCompactSupport ψ) (hψs : tsupport ψ ⊆ D) :
    ContinuousOn (fun t : ℝ => ∫ x, ψ x * F (t, x)) (Set.Ioo 0 T) := by
  refine continuousOn_integral_of_compact_support (f := fun t x => ψ x * F (t, x)) hψc.isCompact ?_ ?_
  · intro p hp
    obtain ⟨t, x⟩ := p
    have ht : t ∈ Set.Ioo 0 T := hp.1
    by_cases hx : x ∈ D
    · have hOp : IsOpen (Set.Ioo 0 T ×ˢ D) := isOpen_Ioo.prod hD
      have hFa : ContinuousAt F (t, x) := hFc.continuousAt (hOp.mem_nhds ⟨ht, hx⟩)
      exact ((hψ.comp continuous_snd).continuousAt.mul hFa).continuousWithinAt
    · have hz : (fun p : ℝ × EucConfig d N => ψ p.2 * F p) =ᶠ[𝓝 (t, x)] fun _ => 0 := by
        have hx' : x ∉ tsupport ψ := fun h => hx (hψs h)
        filter_upwards [(isClosed_tsupport ψ).isOpen_compl.preimage continuous_snd |>.mem_nhds hx'] with p hp
        rw [image_eq_zero_of_notMem_tsupport hp, zero_mul]
      refine (continuousAt_const.congr hz.symm).continuousWithinAt.congr_of_eventuallyEq ?_ ?_
      · exact EventuallyEq.rfl
      · simpa using hz.self_of_nhds
  · intro t _ x hx
    rw [image_eq_zero_of_notMem_tsupport hx, zero_mul]

end HRS.MS.S113X2

end
