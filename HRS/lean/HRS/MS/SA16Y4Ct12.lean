import HRS.MS.SA16Y4Ct11

/-!
# S.A.16 (SA16Y4) Ct12: weak-to-strong at fixed mollification scale

`sa16y4_weak_strong`: if `‖Z i‖ ≤ B` eventually and the `κ`-component pairings of `Z i` against every `N ∈ C_c^∞` tend to `0` along a
countably generated filter, then `‖1_{B(0,R₁)} (R_n Z i)_κ‖_{L^p} → 0` (dominated convergence for `ρ_n ⋆ Z_κ`).
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff Convolution

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Q Phase2SA16Evolution Phase2SA16Transfer

section Ct12
variable {d : ℕ} {p : ℝ} [Fact (2 ≤ p)]

theorem sa16y4_weak_strong (k n : ℕ) (R : WmpSpace d k p →L[ℝ] WmpSpace d k p)
    (hR : ∀ ψ : ccSub d, R (sa16r_Jcc d k p ψ) = sa16r_Jcc d k p ⟨sa16q_mol n ψ.1, sa16y4_mol_cc ψ.2 n⟩)
    (κ : WIndex d k) (R₁ : ℝ) {ι : Type*} (l : Filter ι) [l.IsCountablyGenerated]
    (Z : ι → WmpSpace d k p) (B : ℝ) (hB : ∀ᶠ i in l, ‖Z i‖ ≤ B)
    (hw : ∀ {N : EuclideanSpace ℝ (Fin d) → ℝ} (hN : IsCcInfty N),
      Tendsto (fun i => sa16y4_ellK k κ hN (Z i)) l (𝓝 0)) :
    Tendsto (fun i => (eLpNorm ((Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) R₁).indicator
      (sa16y4_comp k (R (Z i)) κ)) (ENNReal.ofReal p) volume).toReal) l (𝓝 0) := by
  have hp0 : (0 : ℝ) < p := lt_of_lt_of_le zero_lt_two (Fact.out : 2 ≤ p)
  have hP0 : ENNReal.ofReal p ≠ 0 := (ENNReal.ofReal_pos.2 hp0).ne'
  have hPt : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
  have hPr : (ENNReal.ofReal p).toReal = p := ENNReal.toReal_ofReal hp0.le
  obtain ⟨C, hC0, hC⟩ := sa16y4_mol_comp_bound (p := p) k n κ
  set K : Set (EuclideanSpace ℝ (Fin d)) := Metric.closedBall 0 R₁ with hK
  set f : ι → EuclideanSpace ℝ (Fin d) → ℝ := fun i => sa16q_mol n (sa16y4_comp k (Z i) κ) with hf
  have hfae : ∀ i, f i =ᵐ[volume] sa16y4_comp k (R (Z i)) κ := fun i => (sa16y4_R_kernel k n R hR κ (Z i)).symm
  have hind : ∀ i, eLpNorm (K.indicator (sa16y4_comp k (R (Z i)) κ)) (ENNReal.ofReal p) volume =
      eLpNorm (K.indicator (f i)) (ENNReal.ofReal p) volume := fun i =>
    eLpNorm_congr_ae ((hfae i).mono fun x hx => by simp only [Set.indicator, hx])
  set F : ι → EuclideanSpace ℝ (Fin d) → ℝ≥0∞ := fun i x => ‖K.indicator (f i) x‖ₑ ^ p with hF
  set bd : EuclideanSpace ℝ (Fin d) → ℝ≥0∞ := K.indicator (fun _ => ENNReal.ofReal (C * B) ^ p) with hbd
  have hsm : ∀ i, AEStronglyMeasurable (K.indicator (f i)) volume := fun i =>
    ((sa16y4_comp_aesm k (R (Z i)) κ).congr (hfae i).symm).indicator measurableSet_closedBall
  have hmeas : ∀ i, AEMeasurable (F i) volume := fun i => (hsm i).enorm.pow_const p
  have hfin : ∫⁻ x, bd x ≠ ⊤ := by
    rw [hbd, lintegral_indicator measurableSet_closedBall]
    simp only [lintegral_const, Measure.restrict_apply MeasurableSet.univ, univ_inter]
    exact ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg hp0.le ENNReal.ofReal_ne_top)
      (measure_closedBall_lt_top).ne
  have hbound : ∀ᶠ i in l, ∀ x, F i x ≤ bd x := by
    filter_upwards [hB] with i hi x
    simp only [hF, hbd]
    by_cases hx : x ∈ K
    · simp only [Set.indicator_of_mem hx]
      refine ENNReal.rpow_le_rpow ?_ hp0.le
      rw [Real.enorm_eq_ofReal_abs]
      refine ENNReal.ofReal_le_ofReal ((hC (Z i) x).trans ?_)
      exact mul_le_mul_of_nonneg_left hi hC0
    · simp [Set.indicator_of_notMem hx, ENNReal.zero_rpow_of_pos hp0]
  have hlimit : ∀ x, Tendsto (fun i => F i x) l (𝓝 0) := by
    intro x
    by_cases hx : x ∈ K
    · have h1 : Tendsto (fun i => f i x) l (𝓝 0) := by
        have := hw (sa16y4_rhox_cc (d := d) n x)
        refine this.congr fun i => ?_
        exact (sa16y4_mol_comp_eq k n (Z i) κ x).symm
      have h2 : Tendsto (fun i => ‖f i x‖ₑ) l (𝓝 0) := by
        have := (continuous_enorm.tendsto (0 : ℝ)).comp h1
        simpa [Function.comp_def] using this
      have h3 := (ENNReal.continuous_rpow_const (y := p)).tendsto 0
      rw [ENNReal.zero_rpow_of_pos hp0] at h3
      have := h3.comp h2
      simpa [hF, Set.indicator_of_mem hx, Function.comp_def] using this
    · simp only [hF, Set.indicator_of_notMem hx, enorm_zero]
      simpa [ENNReal.zero_rpow_of_pos hp0] using tendsto_const_nhds
  have hlim := tendsto_lintegral_filter_of_dominated_convergence' (μ := (volume : Measure (EuclideanSpace ℝ (Fin d))))
    (F := F) (f := fun _ => 0) bd (Eventually.of_forall hmeas)
    (hbound.mono fun i hi => Eventually.of_forall hi) hfin
    (Eventually.of_forall hlimit)
  simp only [lintegral_zero] at hlim
  have h2 : Tendsto (fun i => (∫⁻ x, F i x) ^ (1 / p)) l (𝓝 0) := by
    have := (ENNReal.continuous_rpow_const (y := 1 / p)).tendsto 0
    rw [ENNReal.zero_rpow_of_pos (by positivity)] at this
    exact this.comp hlim
  have h3 : Tendsto (fun i => (eLpNorm (K.indicator (sa16y4_comp k (R (Z i)) κ)) (ENNReal.ofReal p) volume)) l (𝓝 0) := by
    refine h2.congr fun i => ?_
    rw [hind i, eLpNorm_eq_lintegral_rpow_enorm_toReal hP0 hPt (hsm i), hPr]
  have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h3
  simpa [Function.comp_def] using this
end Ct12

end HRS.Whole.AppendixA.Phase2SA16R
