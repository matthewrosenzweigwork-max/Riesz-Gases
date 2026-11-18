import HRS.MP.SelfSimP5MixA

/-!
# MPP5C (1b): measurability in time of the Fisher information of the marginal laws

For a path-continuous process `Y` and the weight `Ḡ = selfSimWeight d 0 invβ N τ` (`s = 0`), the map
`r ↦ fisherInfoW Ḡ (law Q (Y_r))` is a supremum of continuous functions of `r` (each test field gives a bounded
continuous integrand on `ℝ^{dN}`, because `log Ḡ` is smooth off the collision set and the test field is compactly
supported there), hence lower semicontinuous, hence measurable.  Replaces `h5_fisher_measurable_ck`.
-/

open MeasureTheory Filter Topology InformationTheory
open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MC.CepH0
open scoped ENNReal NNReal BigOperators ContDiff

noncomputable section

namespace HRS.MP.SelfSimP5Impl

variable {d N : ℕ}

theorem ss5m_collision_closed : IsClosed (eucCollisionSet d N) := by
  have : eucCollisionSet d N = ⋃ i, ⋃ j, ⋃ (_ : i ≠ j), {X : EucConfig d N | X i = X j} := by
    ext X; simp [eucCollisionSet]
  rw [this]
  exact isClosed_iUnion_of_finite fun i => isClosed_iUnion_of_finite fun j =>
    isClosed_iUnion_of_finite fun _ => isClosed_eq (continuous_apply i) (continuous_apply j)

theorem ss5m_logW_smooth (invβ τ : ℝ) :
    ContDiffOn ℝ ∞ (fun Z : EucConfig d N => Real.log (selfSimWeight d 0 invβ N τ Z))
      (eucCollisionSet d N)ᶜ := by
  have key : ContDiffOn ℝ ∞ (fun Z : EucConfig d N => selfSimPotential d 0 N τ Z)
      (eucCollisionSet d N)ᶜ := by
    unfold selfSimPotential
    refine ContDiffOn.add (contDiffOn_const.mul ?_) (contDiffOn_const.mul ?_)
    · refine ContDiffOn.sum fun i _ => ContDiffOn.sum fun j hj => ?_
      have hij : j ≠ i := (Finset.mem_erase.1 hj).1
      intro Z hZ
      have hne : Z i - Z j ≠ 0 := sub_ne_zero.2 (fun h => hZ ⟨i, j, hij.symm, h⟩)
      refine ContDiffAt.contDiffWithinAt ?_
      have hsm : ContDiffAt ℝ ∞ (fun Z : EucConfig d N => Z i - Z j) Z :=
        ((contDiff_apply ℝ (Euc d) i).sub (contDiff_apply ℝ (Euc d) j)).contDiffAt
      have hn : ContDiffAt ℝ ∞ (fun Z : EucConfig d N => ‖Z i - Z j‖) Z := hsm.norm ℝ hne
      have hn0 : ‖Z i - Z j‖ ≠ 0 := norm_ne_zero_iff.2 hne
      simpa [rieszKernel] using (hn.log hn0).neg
    · exact ContDiffOn.sum fun i _ =>
        (((contDiff_norm_sq ℝ).comp (contDiff_apply ℝ (Euc d) i)).contDiffOn)
  refine (contDiffOn_const (c := -(invβ⁻¹)) |>.mul key).congr fun Z hZ => ?_
  have hZ' : Z ∉ eucCollisionSet d N := hZ
  simp [selfSimWeight, hZ']

theorem ss5mF_support (G : EucConfig d N → ℝ) {ζ : EucConfig d N → EucConfig d N} (K : Set (EucConfig d N))
    (hKc : IsClosed K) (hKs : ∀ X, X ∉ K → ζ X = 0) {X : EucConfig d N} (hX : X ∉ K) :
    ss5mF G ζ X = 0 := by
  have hev : ζ =ᶠ[𝓝 X] fun _ => 0 := by
    filter_upwards [hKc.isOpen_compl.mem_nhds hX] with Z hZ
    exact hKs Z hZ
  have hdiv : configDivW ζ X = 0 := by
    unfold configDivW
    refine Finset.sum_eq_zero fun k _ => ?_
    have : (fun Z : EucConfig d N => ζ Z k.1 k.2) =ᶠ[𝓝 X] fun _ => 0 := by
      filter_upwards [hev] with Z hZ
      simp [hZ]
    rw [this.fderiv_eq]; simp
  have h0 : ζ X = 0 := hKs X hX
  simp [ss5mF, hdiv, h0]

theorem ss5mF_continuous (invβ τ : ℝ) {ζ : EucConfig d N → EucConfig d N} (hζ : IsFisherTestFieldW ζ) :
    Continuous (ss5mF (selfSimWeight d 0 invβ N τ) ζ) ∧
      ∃ C : ℝ, ∀ X, ‖ss5mF (selfSimWeight d 0 invβ N τ) ζ X‖ ≤ C := by
  set G := selfSimWeight d 0 invβ N τ with hG
  obtain ⟨K, hKcomp, hKd, hKs⟩ := hζ.support
  have hKc : IsClosed K := hKcomp.isClosed
  have hUo : IsOpen (eucCollisionSet d N)ᶜ := ss5m_collision_closed.isOpen_compl
  have hdiv_cont : Continuous (configDivW ζ) := by
    unfold configDivW
    refine continuous_finset_sum _ fun k _ => ?_
    have hc : ContDiff ℝ ∞ (fun Z : EucConfig d N => ζ Z k.1 k.2) :=
      (EuclideanSpace.proj (𝕜 := ℝ) k.2).contDiff.comp ((contDiff_apply ℝ (Euc d) k.1).comp hζ.smooth)
    exact (hc.continuous_fderiv (by simp)).clm_apply continuous_const
  have hfd : ContinuousOn (fun X : EucConfig d N => fderiv ℝ (fun Z => Real.log (G Z)) X)
      (eucCollisionSet d N)ᶜ :=
    (ss5m_logW_smooth (d := d) (N := N) invβ τ).continuousOn_fderiv_of_isOpen hUo (by simp)
  have hcont : Continuous (ss5mF G ζ) := by
    rw [continuous_iff_continuousAt]
    intro X
    by_cases hXK : X ∈ K
    · have hXU : X ∈ (eucCollisionSet d N)ᶜ := fun h => Set.disjoint_left.1 hKd hXK h
      have hon : ContinuousOn (ss5mF G ζ) (eucCollisionSet d N)ᶜ := by
        unfold ss5mF
        refine ((continuousOn_const.mul hdiv_cont.continuousOn).sub ?_).sub
          (continuous_finset_sum _ fun i _ =>
            ((continuous_apply i).comp hζ.smooth.continuous).norm.pow 2).continuousOn
        exact continuousOn_const.mul (ContinuousOn.clm_apply hfd hζ.smooth.continuous.continuousOn)
      exact hon.continuousAt (hUo.mem_nhds hXU)
    · have : ss5mF G ζ =ᶠ[𝓝 X] fun _ => 0 := by
        filter_upwards [hKc.isOpen_compl.mem_nhds hXK] with Z hZ
        exact ss5mF_support G K hKc hKs hZ
      exact continuousAt_const.congr this.symm
  refine ⟨hcont, ?_⟩
  exact hcont.bounded_above_of_compact_support
    (HasCompactSupport.intro hKcomp fun X hX => ss5mF_support G K hKc hKs hX)

/-- **(1b)** Measurability in time of `r ↦ 𝓘_Ḡ(law Y_r)`. -/
theorem ss5m_fisher_meas (invβ τ : ℝ) {Ω : Type*} [MeasurableSpace Ω] (Q : Measure Ω)
    [IsProbabilityMeasure Q] {Y : ℝ≥0 → Ω → EucConfig d N} (hYm : ∀ t, Measurable (Y t))
    (hYc : ∀ ζ, Continuous fun t => Y t ζ) :
    Measurable fun r : ℝ => fisherInfoW (selfSimWeight d 0 invβ N τ) (law Q (Y (Real.toNNReal r))) := by
  set G := selfSimWeight d 0 invβ N τ with hG
  have hfun : (fun r : ℝ => fisherInfoW G (law Q (Y (Real.toNNReal r)))) =
      fun r : ℝ => ⨆ ζ : Ss5mA d N,
        ENNReal.ofReal (∫ X, ss5mF G ζ.1 X ∂(law Q (Y (Real.toNNReal r)))) := by
    funext r; rw [ss5m_fisher_eq, iSup_subtype']
  rw [hfun]
  refine (lowerSemicontinuous_iSup fun ζ => ?_).measurable
  apply Continuous.lowerSemicontinuous
  obtain ⟨hc, C, hC⟩ := ss5mF_continuous (d := d) (N := N) invβ τ ζ.2
  have heq : (fun r : ℝ => ∫ X, ss5mF G ζ.1 X ∂(law Q (Y (Real.toNNReal r)))) =
      fun r : ℝ => ∫ w, ss5mF G ζ.1 (Y (Real.toNNReal r) w) ∂Q := by
    funext r
    exact integral_map (hYm _).aemeasurable hc.aestronglyMeasurable
  have hcont : Continuous fun r : ℝ => ∫ w, ss5mF G ζ.1 (Y (Real.toNNReal r) w) ∂Q :=
    continuous_of_dominated (bound := fun _ => C)
      (fun r => (hc.measurable.comp (hYm _)).aestronglyMeasurable)
      (fun r => Filter.Eventually.of_forall fun w => hC _) (integrable_const C)
      (Filter.Eventually.of_forall fun w => hc.comp ((hYc w).comp continuous_real_toNNReal))
  have hcont' : Continuous fun r : ℝ => ∫ X, ss5mF G ζ.1 X ∂(law Q (Y (Real.toNNReal r))) := by
    rw [heq]; exact hcont
  exact ENNReal.continuous_ofReal.comp hcont'

end HRS.MP.SelfSimP5Impl
