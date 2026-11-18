import HRS.ME.UIEntropy
import HRS.Sections.Sec5

/-!
# Proposition 5.10, last sentence: the entropy bound implies uniform integrability (frozen statement)

Proof of `HRS.ui_of_entropy_bound` exactly as frozen, with no hypotheses on `d`, `s`, `V`, `β`.  For arbitrary `V` and `β`,
`canonicalGibbs` is `c • μ` with `μ` the measure with density `exp (-β H)` and `c = (ofReal Z)⁻¹`, `Z` the Bochner integral
of the density.  The density is positive, so `Z ≥ 0`, and there are two cases.

* `Z > 0`: the density is integrable, `μ univ = ofReal Z`, and the Gibbs law is a probability measure.  Then
  `HRS.ME.UIEntropy.ui_tail_of_relEntropy` applies.
* `Z = 0`: `c = ⊤`.  From the entropy bound `ν ≪ Q`.  If `ν` had a Lebesgue decomposition with respect to `Q`, then
  `ν = Q.withDensity (ν.rnDeriv Q)` would have total mass `⊤ * ∫⁻ rnDeriv dμ ∈ {0, ⊤}`, not `1`.  So there is no
  Lebesgue decomposition, `rnDeriv = 0` by the junk-value convention, and the tail set is empty.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace HRS.ME.UIEntropyFrozen

/-- If `Q = ⊤ • μ` and `ν` is a probability measure with `ν ≪ Q`, then `ν.rnDeriv Q = 0`. -/
lemma rnDeriv_top_smul {α : Type*} [MeasurableSpace α] (ν μ : Measure α) [IsProbabilityMeasure ν]
    (hac : ν ≪ (⊤ : ℝ≥0∞) • μ) : ν.rnDeriv ((⊤ : ℝ≥0∞) • μ) = 0 := by
  by_cases h : ν.HaveLebesgueDecomposition ((⊤ : ℝ≥0∞) • μ)
  · exfalso
    have e := Measure.withDensity_rnDeriv_eq ν ((⊤ : ℝ≥0∞) • μ) hac
    have h1 := congrArg (fun m : Measure α => m Set.univ) e
    simp only [measure_univ] at h1
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, lintegral_smul_measure] at h1
    simp only [smul_eq_mul] at h1
    by_cases h0 : ∫⁻ x, ν.rnDeriv ((⊤ : ℝ≥0∞) • μ) x ∂μ = 0
    · rw [h0, mul_zero] at h1
      exact zero_ne_one h1
    · rw [ENNReal.top_mul h0] at h1
      exact ENNReal.top_ne_one h1
  · exact Measure.rnDeriv_of_not_haveLebesgueDecomposition h

theorem ui_of_entropy_bound_proof {d : ℕ} : type_of% (@HRS.ui_of_entropy_bound d) := by
  intro s β V ν hν H₀ hH
  have hb : ∀ L : ℝ, 1 < L → uiTail d s β V ν L ≤ ENNReal.ofReal ((H₀ + Real.exp (-1)) / Real.log L) := by
    intro L hL
    unfold uiTail
    refine iSup_le fun n => ?_
    have := hν n
    set N := n + 2 with hN
    set f : Config d N → ℝ := fun X => Real.exp (-β * canonicalHamiltonian (periodicRiesz d s) V X) with hf
    set Z := canonicalPartition (periodicRiesz d s) V N β with hZ
    have hZ0 : 0 ≤ Z := integral_nonneg fun X => (Real.exp_pos _).le
    rcases hZ0.eq_or_lt with hZ0 | hZpos
    · -- junk case `Z = 0`
      have hQ : canonicalGibbs (periodicRiesz d s) V N β =
          (⊤ : ℝ≥0∞) • (volume : Measure (Config d N)).withDensity fun X => ENNReal.ofReal (f X) := by
        unfold canonicalGibbs
        rw [← hZ, ← hZ0, ENNReal.ofReal_zero, ENNReal.inv_zero]
      have hkl := hH n
      have hac : ν n ≪ canonicalGibbs (periodicRiesz d s) V N β := by
        have : HRS.relEntropy (ν n) (canonicalGibbs (periodicRiesz d s) V N β) ≠ ⊤ :=
          ne_top_of_le_ne_top ENNReal.ofReal_ne_top hkl
        exact (InformationTheory.klDiv_ne_top_iff.mp this).1
      rw [hQ] at hac ⊢
      rw [rnDeriv_top_smul _ _ hac]
      have : {X : Config d N | ENNReal.ofReal L < (0 : Config d N → ℝ≥0∞) X} = ∅ := by
        ext X; simp
      simp
    · -- `Z > 0`: the Gibbs law is a probability measure
      have hP : IsProbabilityMeasure (canonicalGibbs (periodicRiesz d s) V N β) := by
        have hint : Integrable f := by
          by_contra hni
          have : Z = 0 := integral_undef hni
          exact hZpos.ne' this
        have hl := ofReal_integral_eq_lintegral_ofReal hint
          (Filter.Eventually.of_forall fun X => (Real.exp_pos _).le)
        refine ⟨?_⟩
        unfold canonicalGibbs
        rw [Measure.smul_apply, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
          ← hl, smul_eq_mul]
        exact ENNReal.inv_mul_cancel (by simpa using hZpos) ENNReal.ofReal_ne_top
      exact (HRS.ME.UIEntropy.ui_tail_of_relEntropy (ν n) _ H₀ L hL (hH n)).2
  refine ⟨hb, ?_⟩
  have hlim : Tendsto (fun L : ℝ => ENNReal.ofReal ((H₀ + Real.exp (-1)) / Real.log L)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun L : ℝ => (H₀ + Real.exp (-1)) / Real.log L) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop Real.tendsto_log_atTop
    have h2 := (ENNReal.continuous_ofReal.tendsto 0).comp h1
    rw [ENNReal.ofReal_zero] at h2
    exact h2
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim (Eventually.of_forall fun L => bot_le) ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with L hL using hb L hL

end HRS.ME.UIEntropyFrozen
