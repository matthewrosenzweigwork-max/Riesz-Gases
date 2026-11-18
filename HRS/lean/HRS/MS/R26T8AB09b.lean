import HRS.MS.R26T8AB09a
import HRS.MS.R26T8AB04c
import HRS.MS.R26T8AB02d

/-!
# S8.2 T8A B09b: measurability of the drift integral at a fixed observed time

For continuous `age, tm : ℝ → ℝ` with `age ≥ 0`, `0 ≤ tm ≤ H` on a measurable `I`, the map
`w ↦ ∫_{I} VAge i (age r) (X (tm r) w) dr` is a.e. measurable.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators ContDiff
namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82

theorem r26t8a_b09_Vslice (d N : ℕ) (hd : 2 ≤ d) (hN : 2 ≤ N) (a beta m M C Cf c : ℝ)
    (ha : 0 < a) (hbeta : 0 < beta) (hM : 0 ≤ M) (hC : 0 ≤ C)
    (rho : Euc d → ℝ) (hrho : IsThermalEquilibrium d (criticalS d) a beta rho)
    (Psi : (Euc d → ℝ) → Euc d → Euc d → ℝ)
    (hPsi : r26t8a_NormalFormFamily d a beta M C rho Psi)
    (horb : r26t8a_FeatureOrbits d a beta m Cf c rho) (alpha : MultiIndex d) (i : ℕ) (hi : i ≤ 1)
    {Omega : Type} [mOmega : MeasurableSpace Omega] (P : Measure Omega) [IsProbabilityMeasure P]
    (X0 : Omega → EucConfig d N) (W : ℝ≥0 → Omega → Fin N → Euc d) (X : ℝ≥0 → Omega → EucConfig d N)
    (hX : IsCanonicalRealization d (criticalS d) a beta N P X0 W X)
    (age tm : ℝ → ℝ) (hage : Continuous age) (htm : Continuous tm) (I : Set ℝ) (hI : MeasurableSet I) (H : ℝ)
    (hIb : ∀ r ∈ I, 0 ≤ age r ∧ 0 ≤ tm r ∧ tm r ≤ H) :
    AEMeasurable (fun w => ∫ r in I, r26t8a_VAge a beta m rho Psi alpha i (age r) (X (tm r).toNNReal w)) P := by
  classical
  obtain ⟨F, W', hfilt⟩ := hX.filtered
  have hXmeas := r26t8a_o04_X_meas hfilt.progressive
  set U : Set (EucConfig d N) := (eucCollisionSet d N)ᶜ with hU
  have hUo : IsOpen U := r26t8a_o03b_coll_closed.isOpen_compl
  have hVc := r26t8a_b02_VAge_cont d N hd hN a beta m M C Cf c ha hbeta hM hC rho hrho Psi hPsi horb alpha i hi
  set Hf : ℝ × EucConfig d N → ℝ := fun q => r26t8a_VAge a beta m rho Psi alpha i q.1 q.2 with hHf
  have hpw : Measurable ((Set.Ici (0 : ℝ) ×ˢ U).piecewise Hf (fun _ => 0)) :=
    ContinuousOn.measurable_piecewise hVc continuousOn_const (measurableSet_Ici.prod hUo.measurableSet)
  have hmeas : Measurable (fun p : ℝ × Omega =>
      (Set.Ici (0 : ℝ) ×ˢ U).piecewise Hf (fun _ => 0) (age p.1, X (tm p.1).toNNReal p.2)) := by
    refine hpw.comp (Measurable.prodMk (hage.measurable.comp measurable_fst) ?_)
    exact hXmeas.comp (((htm.measurable).comp measurable_fst).prodMk measurable_snd)
  set ν : Measure ℝ := volume.restrict I with hν
  have hae : AEStronglyMeasurable (fun p : ℝ × Omega =>
      r26t8a_VAge a beta m rho Psi alpha i (age p.1) (X (tm p.1).toNNReal p.2)) (ν.prod P) := by
    refine hmeas.aestronglyMeasurable.congr ?_
    have h1 : ∀ᵐ r ∂ν, r ∈ I := ae_restrict_mem hI
    have h2 := r26t8a_b02_ae_good d N a beta P X0 W X hX H
    have h1' : ∀ᵐ p ∂(ν.prod P), p.1 ∈ I := (Measure.quasiMeasurePreserving_fst (μ := ν) (ν := P)).ae h1
    have h2' : ∀ᵐ p ∂(ν.prod P), ∀ r : ℝ, 0 ≤ r → r ≤ H → X r.toNNReal p.2 ∉ eucCollisionSet d N :=
      (Measure.quasiMeasurePreserving_snd (μ := ν) (ν := P)).ae h2
    filter_upwards [h1', h2'] with p hp1 hp2
    obtain ⟨hA0, hT0, hTH⟩ := hIb p.1 hp1
    have hmem : (age p.1, X (tm p.1).toNNReal p.2) ∈ Set.Ici (0 : ℝ) ×ˢ U := ⟨hA0, hp2 _ hT0 hTH⟩
    simp only [hHf]
    rw [Set.piecewise_eq_of_mem _ _ _ hmem]
  have := hae.prod_swap.integral_prod_right'
  exact this.aemeasurable

end HRS.MS.R26T8A

end
