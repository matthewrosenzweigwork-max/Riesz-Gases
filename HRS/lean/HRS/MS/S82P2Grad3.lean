import HRS.MS.S82P2Grad1
import HRS.MS.S82P2QF1
import HRS.MS.S82P2Mar3

/-!
# S8.2 (S82P2): measurable gradient model, generic row bound, non-collision (UNCOMPILED DRAFT)
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S82P2
open HRS HRS.Whole HRS.MS.Phase2S82

/-- A measurable model of `Phase2S82.pairGradX Q`: it agrees with `Phase2S82.pairGradX Q` off the diagonal. -/
def s82p2_gt {d : ℕ} (Q : Euc d → Euc d → ℝ) (x z : Euc d) : Euc d :=
  if x ≠ z then (InnerProductSpace.toDual ℝ (Euc d)).symm
    ((fderiv ℝ (Function.uncurry Q) (x, z)).comp (ContinuousLinearMap.inl ℝ (Euc d) (Euc d)))
  else 0

lemma s82p2_gt_measurable {d : ℕ} (Q : Euc d → Euc d → ℝ) :
    Measurable (Function.uncurry (s82p2_gt Q)) := by
  unfold s82p2_gt Function.uncurry
  refine Measurable.ite (isOpen_ne_fun continuous_fst continuous_snd).measurableSet ?_
    measurable_const
  have h1 : Measurable (fun p : Euc d × Euc d => fderiv ℝ (Function.uncurry Q) p) :=
    measurable_fderiv ℝ (Function.uncurry Q)
  have h2 : Continuous (fun L : (Euc d × Euc d) →L[ℝ] ℝ =>
      (InnerProductSpace.toDual ℝ (Euc d)).symm (L.comp (ContinuousLinearMap.inl ℝ (Euc d) (Euc d)))) :=
    (InnerProductSpace.toDual ℝ (Euc d)).symm.continuous.comp
      (continuous_id.clm_comp continuous_const)
  exact h2.measurable.comp h1

lemma s82p2_gt_eq {d : ℕ} {a beta M A : ℝ} {rho : Euc d → ℝ} {f : Euc d → ℝ}
    {Q : Euc d → Euc d → ℝ} (hQ : PairCorrector a beta rho M A f Q) (x z : Euc d) (hxz : x ≠ z) :
    s82p2_gt Q x z = Phase2S82.pairGradX Q x z := by
  unfold s82p2_gt Phase2S82.pairGradX gradient
  rw [if_pos hxz]
  congr 1
  have hopen : IsOpen {p : Euc d × Euc d | p.1 ≠ p.2} := isOpen_ne_fun continuous_fst continuous_snd
  have hΦ : DifferentiableAt ℝ (Function.uncurry Q) (x, z) :=
    (hQ.smooth.differentiableOn (by norm_num)).differentiableAt (hopen.mem_nhds hxz)
  have h2 : HasFDerivAt (fun x' : Euc d => (x', z)) (ContinuousLinearMap.inl ℝ (Euc d) (Euc d)) x :=
    (hasFDerivAt_id x).prodMk (hasFDerivAt_const z x)
  exact ((hΦ.hasFDerivAt.comp x h2).fderiv).symm

lemma s82p2_gt_norm_le {d : ℕ} {a beta M A : ℝ} {rho : Euc d → ℝ} {f : Euc d → ℝ}
    {Q : Euc d → Euc d → ℝ} (hQ : PairCorrector a beta rho M A f Q) (x z : Euc d) (hxz : x ≠ z) :
    ‖s82p2_gt Q x z‖ ≤ A * pairWeight M x z * (1 + smallRadius x z ^ (1 - criticalS d)) := by
  rw [s82p2_gt_eq hQ x z hxz]
  have h := hQ.gradient x z hxz
  have := norm_nonneg (Phase2S82.pairGradY Q x z)
  linarith

/-- Non-collision at site `i` holds almost surely under the weak reference law. -/
lemma s82p2_noncollision {d : ℕ} (hd : 2 ≤ d) {a beta C0 : ℝ} {rho : Euc d → ℝ} {q : Euc d → ℝ}
    {h : ℕ → Euc d → ℝ} [IsProbabilityMeasure (HRS.Whole.withDensityReal rho)]
    (hW : WeakReferenceSetup d a beta rho q h C0) {m : ℕ} (hm : 1 ≤ m) (i : Fin (m + 1)) :
    referenceLaw q h (HRS.Whole.withDensityReal rho) beta (m + 1) (m + 1)
      (fun i : Fin 0 => i.elim0) {X | ∃ j, j ≠ i ∧ X j = X i} = 0 := by
  set mu := HRS.Whole.withDensityReal rho with hmudef
  have hN : 2 ≤ m + 1 := by omega
  let pins0 : Fin 0 → Euc d := fun i => i.elim0
  have hprob0 : IsProbabilityMeasure (referenceLaw q h mu beta (m + 1) (m + 1) pins0) :=
    hW.probability (m + 1) hN 0 (m + 1) (by omega) (by omega) pins0
  have hprob1 : ∀ z : Euc d, IsProbabilityMeasure (referenceLaw q h mu beta (m + 1) m
      (Fin.cons z pins0 : Fin (0 + 1) → Euc d)) := fun z =>
    hW.probability (m + 1) hN (0 + 1) m (by omega) (by omega) _
  set bad : Set (EucConfig d (m + 1)) := {X | ∃ j, j ≠ i ∧ X j = X i} with hbaddef
  have hbad : MeasurableSet bad := by
    have : bad = ⋃ j : Fin (m + 1), ⋃ (_ : j ≠ i), {X : EucConfig d (m + 1) | X j = X i} := by
      ext X; simp [bad]
    rw [this]
    exact MeasurableSet.iUnion fun j => MeasurableSet.iUnion fun _ =>
      measurableSet_eq_fun (measurable_pi_apply j) (measurable_pi_apply i)
  have hdis := s82p2_disintegration (mu := mu) hW.short.measurable hW.short.even beta (m + 1)
    (hW.hmeas (m + 1)) pins0 i hprob0 hprob1 (bad.indicator 1) (measurable_one.indicator hbad)
  rw [← lintegral_indicator_one hbad, hdis]
  refine le_antisymm ?_ bot_le
  calc ∫⁻ x, ∫⁻ X' : Fin m → Euc d, bad.indicator 1 (i.insertNth x X')
        ∂referenceLaw q h mu beta (m + 1) m (Fin.cons x pins0 : Fin (0 + 1) → Euc d)
        ∂((referenceLaw q h mu beta (m + 1) (m + 1) pins0).map (fun X => X i))
      ≤ ∫⁻ x, (0 : ℝ≥0∞) ∂((referenceLaw q h mu beta (m + 1) (m + 1) pins0).map (fun X => X i)) := by
        refine lintegral_mono fun x => ?_
        have hle : ∀ X' : Fin m → Euc d, bad.indicator (1 : EucConfig d (m + 1) → ℝ≥0∞)
            (i.insertNth x X') ≤ (⋃ k : Fin m, {X' : Fin m → Euc d | X' k = x}).indicator 1 X' := by
          intro X'
          by_cases hX : i.insertNth x X' ∈ bad
          · obtain ⟨j, hj, hjx⟩ := hX
            obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hj
            have hk : X' k = x := by
              simpa [Fin.insertNth_apply_succAbove, Fin.insertNth_apply_same] using hjx
            have : X' ∈ ⋃ k : Fin m, {X' : Fin m → Euc d | X' k = x} :=
              Set.mem_iUnion.2 ⟨k, hk⟩
            rw [Set.indicator_of_mem this]
            exact (Set.indicator_le_self' (fun _ _ => bot_le) _).trans le_rfl
          · simp [Set.indicator_of_notMem hX]
        refine (lintegral_mono hle).trans ?_
        have hU : MeasurableSet (⋃ k : Fin m, {X' : Fin m → Euc d | X' k = x}) :=
          MeasurableSet.iUnion fun k => measurableSet_eq_fun (measurable_pi_apply k) measurable_const
        rw [lintegral_indicator_one hU]
        refine le_of_eq (measure_iUnion_null fun k => ?_)
        have hset : {X' : Fin m → Euc d | X' k = x} = (fun X' : Fin m → Euc d => X' k) ⁻¹' {x} := rfl
        rw [hset, ← Measure.map_apply (measurable_pi_apply k) (measurableSet_singleton x)]
        exact s82p2_marg_ac q h mu beta (m + 1) _ k (s82p2_mu_singleton hd rho x)
    _ = 0 := by simp

end HRS.MS.S82P2
