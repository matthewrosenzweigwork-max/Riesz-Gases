import HRS.MC.CepP3Aux15

/-!
# Packet P3, Aux16: the cube formulas relating the lifted measure and the measure on `ℝ × Config`
-/

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MC.CepP3

open HRS

variable {d N : ℕ}

/-- `ℝ × [0,1)^{N d}`. -/
def cubeSet (d N : ℕ) : Set (ℝ × (Fin N → Euc d)) := univ ×ˢ cubeQ d N

theorem measurableSet_cubeSet : MeasurableSet (cubeSet d N) :=
  MeasurableSet.univ.prod measurableSet_cubeQ

/-- The map `(t, Y) ↦ (t, mkC Y)`. -/
def Gm (p : ℝ × (Fin N → Euc d)) : ℝ × Config d N := (p.1, mkC p.2)

theorem measurable_Gm : Measurable (Gm : ℝ × (Fin N → Euc d) → ℝ × Config d N) :=
  measurable_fst.prodMk (measurable_mkC.comp measurable_snd)

/-- The cube lift of a set `S ⊆ ℝ × Config`. -/
def lift0 (S : Set (ℝ × Config d N)) : Set (ℝ × (Fin N → Euc d)) := Gm ⁻¹' S ∩ cubeSet d N

theorem measurableSet_lift0 {S : Set (ℝ × Config d N)} (hS : MeasurableSet S) :
    MeasurableSet (lift0 S) :=
  (measurable_Gm hS).inter measurableSet_cubeSet

theorem cube_shift {Y : Fin N → Euc d} {w : Fin N → Lattice d} (hY : Y ∈ cubeQ d N)
    (hYw : Y + lat w ∈ cubeQ d N) : w = 0 := by
  have h1 : flo Y = 0 := flo_eq_iff.2 (by rw [lat_zero, sub_zero]; exact hY)
  have h2 : flo (Y + lat w) = 0 := flo_eq_iff.2 (by rw [lat_zero, sub_zero]; exact hYw)
  rw [flo_add_lat, h1, zero_add] at h2
  exact h2

theorem psi_zero_apply (q : ℝ × Config d N) : psi 0 q = (q.1, repC q.2) := by
  simp [psi, lat_zero]

theorem psi_zero_preimage_lift0 (S : Set (ℝ × Config d N)) : psi 0 ⁻¹' lift0 S = S := by
  ext q
  have hm : mkC (repC q.2) = q.2 := by
    exact mk_repC q.2
  constructor
  · intro h
    have h1 : (psi 0 q).1 = q.1 := by rw [psi_zero_apply]
    have h2 := h.1
    simp only [mem_preimage, Gm, psi_zero_apply] at h2
    rw [hm] at h2
    exact h2
  · intro h
    refine ⟨?_, ?_⟩
    · simp only [mem_preimage, Gm, psi_zero_apply]
      rw [hm]; exact h
    · simp only [cubeSet, mem_prod, mem_univ, true_and, psi_zero_apply]
      exact repC_mem_cubeQ q.2

theorem rhoCov_cube (ρ : Measure (ℝ × Config d N)) {A : Set (ℝ × (Fin N → Euc d))}
    (hA : MeasurableSet A) (hsub : A ⊆ cubeSet d N) : rhoCov ρ A = ρ (psi 0 ⁻¹' A) := by
  unfold rhoCov
  rw [Measure.sum_apply _ hA, tsum_eq_single (0 : Fin N → Lattice d)]
  · rw [Measure.map_apply (measurable_psi 0) hA]
  · intro w hw
    rw [Measure.map_apply (measurable_psi w) hA]
    have : psi w ⁻¹' A = ∅ := by
      ext q
      simp only [mem_preimage, mem_empty_iff_false, iff_false]
      intro hq
      have h1 := (hsub hq).2
      have h2 : repC q.2 ∈ cubeQ d N := repC_mem_cubeQ _
      exact hw (cube_shift h2 h1)
    rw [this]; simp

theorem measurePreserving_Gm_cube :
    MeasurePreserving (Gm : ℝ × (Fin N → Euc d) → ℝ × Config d N)
      (volume.restrict (cubeSet d N)) ((volume : Measure ℝ).prod (volume : Measure (Config d N))) := by
  have h1 : MeasurePreserving (Prod.map (id : ℝ → ℝ) (mkC : (Fin N → Euc d) → Config d N))
      ((volume : Measure ℝ).prod (volume.restrict (cubeQ d N)))
      ((volume : Measure ℝ).prod (volume : Measure (Config d N))) :=
    (MeasurePreserving.id (volume : Measure ℝ)).prod mkC_measurePreserving_cube
  have h2 : (volume : Measure ℝ).prod (volume.restrict (cubeQ d N))
      = (volume : Measure (ℝ × (Fin N → Euc d))).restrict (cubeSet d N) := by
    have := Measure.prod_restrict (μ := (volume : Measure ℝ)) (ν := (volume : Measure (Fin N → Euc d)))
      univ (cubeQ d N)
    rw [Measure.restrict_univ] at this
    exact this
  rw [h2] at h1
  exact h1

theorem lintegral_lift0 {F : ℝ × Config d N → ℝ≥0∞} (hF : Measurable F)
    {S : Set (ℝ × Config d N)} (hS : MeasurableSet S) :
    ∫⁻ p in lift0 S, F (Gm p) = ∫⁻ y in S, F y ∂((volume : Measure ℝ).prod (volume : Measure (Config d N))) := by
  have := (measurePreserving_Gm_cube (d := d) (N := N)).setLIntegral_comp_preimage hS hF
  rw [← this, Measure.restrict_restrict (measurable_Gm hS)]
  rfl

end HRS.MC.CepP3
