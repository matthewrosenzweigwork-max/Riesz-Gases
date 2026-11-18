import HRS.MP.SelfSimP4Spec

/-!
# MP-SSP4LIMIT: `p4_limit_bookkeeping` (Fatou and `liminf` bookkeeping for `M → ∞`)

Namespace `HRS.MP.SelfSimP4Impl`, helpers `p4lim_`.  Theorem `p4_limit_bookkeeping_proof`, tied to
`HRS.MP.SelfSimP4.p4_limit_bookkeeping`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MP.SelfSim HRS HRS.MP.SelfSimP4
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MP.SelfSimP4Impl

/-- Fatou for the Fisher majorants, restricted to `[0,τ] ⊆ [0,S]`. -/
theorem p4lim_fatou {S : ℝ} {I : ℝ → ℝ≥0∞} {D : ℕ → ℝ → ℝ≥0∞}
    (hDm : ∀ M, AEMeasurable (D M) (volume.restrict (Set.Icc (0 : ℝ) S)))
    (hlscI : ∀ r ∈ Set.Icc (0 : ℝ) S, I r ≤ liminf (fun M => D M r) atTop)
    {τ : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) S) :
    ∫⁻ r in Set.Icc (0 : ℝ) τ, I r ≤ liminf (fun M => ∫⁻ r in Set.Icc (0 : ℝ) τ, D M r) atTop := by
  have hsub : Set.Icc (0 : ℝ) τ ⊆ Set.Icc (0 : ℝ) S := Set.Icc_subset_Icc_right hτ.2
  have hm : ∀ M, AEMeasurable (D M) (volume.restrict (Set.Icc (0 : ℝ) τ)) := fun M =>
    (hDm M).mono_measure (Measure.restrict_mono hsub le_rfl)
  calc ∫⁻ r in Set.Icc (0 : ℝ) τ, I r
      ≤ ∫⁻ r in Set.Icc (0 : ℝ) τ, liminf (fun M => D M r) atTop := by
        refine setLIntegral_mono' measurableSet_Icc fun r hr => hlscI r (hsub hr)
    _ ≤ _ := lintegral_liminf_le' hm

theorem p4_limit_bookkeeping_proof {θ S : ℝ} {H : ℝ → EReal} {HM : ℕ → ℝ → EReal} {I : ℝ → ℝ≥0∞}
    {D : ℕ → ℝ → ℝ≥0∞} {R : EReal}
    (hDm : ∀ M, AEMeasurable (D M) (volume.restrict (Set.Icc (0 : ℝ) S)))
    (hlscH : ∀ τ ∈ Set.Icc (0 : ℝ) S, H τ ≤ liminf (fun M => HM M τ) atTop)
    (hlscI : ∀ r ∈ Set.Icc (0 : ℝ) S, I r ≤ liminf (fun M => D M r) atTop)
    (hlev : ∀ M, ∀ τ ∈ Set.Icc (0 : ℝ) S,
      HM M τ + ((ENNReal.ofReal θ * ∫⁻ r in Set.Icc (0 : ℝ) τ, D M r : ℝ≥0∞) : EReal) ≤ R) :
    ∀ τ ∈ Set.Icc (0 : ℝ) S,
      H τ + ((ENNReal.ofReal θ * ∫⁻ r in Set.Icc (0 : ℝ) τ, I r : ℝ≥0∞) : EReal) ≤ R := by
  intro τ hτ
  have hF := p4lim_fatou hDm hlscI hτ
  -- the `ENNReal` inequality multiplied by `ofReal θ`, then pushed into `EReal`
  have h1 : ENNReal.ofReal θ * ∫⁻ r in Set.Icc (0 : ℝ) τ, I r ≤
      liminf (fun M => ENNReal.ofReal θ * ∫⁻ r in Set.Icc (0 : ℝ) τ, D M r) atTop := by
    refine (mul_le_mul_right hF _).trans ?_
    have := ENNReal.le_liminf_mul (f := atTop) (u := fun _ : ℕ => ENNReal.ofReal θ)
      (v := fun M => ∫⁻ r in Set.Icc (0 : ℝ) τ, D M r)
    rwa [liminf_const] at this
  have h2 : (((ENNReal.ofReal θ * ∫⁻ r in Set.Icc (0 : ℝ) τ, I r : ℝ≥0∞)) : EReal) ≤
      liminf (fun M => ((ENNReal.ofReal θ * ∫⁻ r in Set.Icc (0 : ℝ) τ, D M r : ℝ≥0∞) : EReal))
        atTop := by
    have hm : Monotone (fun x : ℝ≥0∞ => (x : EReal)) := fun x y h =>
      EReal.coe_ennreal_le_coe_ennreal_iff.2 h
    have := hm.map_liminf_of_continuousAt (F := atTop)
      (fun M => ENNReal.ofReal θ * ∫⁻ r in Set.Icc (0 : ℝ) τ, D M r)
      continuous_coe_ennreal_ereal.continuousAt
    rw [Function.comp_def] at this
    rw [← this]
    exact hm h1
  calc H τ + _ ≤ liminf (fun M => HM M τ) atTop +
        liminf (fun M => ((ENNReal.ofReal θ * ∫⁻ r in Set.Icc (0 : ℝ) τ, D M r : ℝ≥0∞) : EReal))
          atTop := add_le_add (hlscH τ hτ) h2
    _ ≤ liminf ((fun M => HM M τ) + fun M =>
        ((ENNReal.ofReal θ * ∫⁻ r in Set.Icc (0 : ℝ) τ, D M r : ℝ≥0∞) : EReal)) atTop :=
        EReal.le_liminf_add
    _ ≤ R := liminf_le_of_frequently_le' (Frequently.of_forall fun M => hlev M τ hτ)

example := (@p4_limit_bookkeeping_proof : type_of% @HRS.MP.SelfSimP4.p4_limit_bookkeeping)

end HRS.MP.SelfSimP4Impl
