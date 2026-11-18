import HRS.MC.CepP3Aux4

/-!
# Packet P3, Aux5: the periodic lift `ρ̃` of the space-time measure to the covering space
-/

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MC.CepP3

open HRS

variable {d N : ℕ}

/-- The section-and-shift map `(t, x) ↦ (t, repC x + lat w)`. -/
def psi (w : Fin N → Lattice d) (q : ℝ × Config d N) : ℝ × (Fin N → Euc d) :=
  (q.1, repC q.2 + lat w)

theorem psi_eq (w : Fin N → Lattice d) (q : ℝ × Config d N) : psi w q = tau w (psi 0 q) := by
  simp [psi, tau, lat_zero]

theorem measurable_psi (w : Fin N → Lattice d) : Measurable (psi (d := d) (N := N) w) :=
  measurable_fst.prodMk ((measurable_repC.comp measurable_snd).add_const _)

/-- The periodic lift of a measure on `ℝ × Config d N` to `ℝ × (Fin N → Euc d)`. -/
def rhoCov (ρ : Measure (ℝ × Config d N)) : Measure (ℝ × (Fin N → Euc d)) :=
  Measure.sum fun w : Fin N → Lattice d => Measure.map (psi w) ρ

theorem norm_repC_le (x : Config d N) : ‖repC x‖ ≤ Real.sqrt d := by
  rw [pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)]
  intro i
  exact rep_norm_le _

theorem norm_psi_zero_snd_le (q : ℝ × Config d N) : ‖(psi 0 q).2‖ ≤ Real.sqrt d := by
  simp only [psi, lat_zero, add_zero]
  exact norm_repC_le _

theorem exists_finset_uniform (R : ℝ) :
    ∃ S : Finset (Fin N → Lattice d), ∀ (q : ℝ × Config d N) (w : Fin N → Lattice d), w ∉ S →
      R < ‖tau w (psi 0 q)‖ := by
  refine ⟨(finite_lat_ball (d := d) (N := N) (R + Real.sqrt d)).toFinset, fun q w hw => ?_⟩
  have hw' : R + Real.sqrt d < ‖lat w‖ := by
    by_contra h
    exact hw ((Set.Finite.mem_toFinset _).2 (not_lt.1 h))
  have h1 := norm_psi_zero_snd_le q
  have h2 : ‖lat w‖ ≤ ‖(psi 0 q).2 + lat w‖ + ‖(psi 0 q).2‖ := by
    have := norm_le_norm_add_norm_sub' (lat w) (-(psi 0 q).2)
    have e : lat w - -(psi 0 q).2 = (psi 0 q).2 + lat w := by abel
    rw [e, norm_neg] at this
    linarith [this]
  have h3 : ‖(psi 0 q).2 + lat w‖ ≤ ‖tau w (psi 0 q)‖ := by
    show ‖(psi 0 q).2 + lat w‖ ≤ ‖((psi 0 q).1, (psi 0 q).2 + lat w)‖
    exact le_max_right _ _
  linarith

theorem rhoCov_apply_compact (ρ : Measure (ℝ × Config d N)) [IsFiniteMeasure ρ]
    {K : Set (ℝ × (Fin N → Euc d))} (hK : IsCompact K) : rhoCov ρ K < ⊤ := by
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
  obtain ⟨S, hS⟩ := exists_finset_uniform (d := d) (N := N) R
  unfold rhoCov
  rw [Measure.sum_apply _ hK.isClosed.measurableSet]
  rw [tsum_eq_sum (s := S)]
  · refine ENNReal.sum_lt_top.2 fun w _ => ?_
    rw [Measure.map_apply (measurable_psi w) hK.isClosed.measurableSet]
    exact measure_lt_top _ _
  · intro w hw
    rw [Measure.map_apply (measurable_psi w) hK.isClosed.measurableSet]
    have : psi w ⁻¹' K = ∅ := by
      ext q
      simp only [mem_preimage, mem_empty_iff_false, iff_false]
      intro hq
      have := hR hq
      rw [mem_closedBall_zero_iff, psi_eq] at this
      exact absurd (hS q w hw) (not_lt.2 this)
    rw [this]; simp

theorem integral_rhoCov (ρ : Measure (ℝ × Config d N)) [IsFiniteMeasure ρ]
    {F : ℝ × (Fin N → Euc d) → ℝ} {R : ℝ} (hc : Continuous F) (hS : Supp R F) :
    ∫ p, F p ∂(rhoCov ρ) = ∫ q, per F (psi 0 q) ∂ρ := by
  have : IsFiniteMeasureOnCompacts (rhoCov ρ) := ⟨fun K hK => rhoCov_apply_compact ρ hK⟩
  have hcs : HasCompactSupport F := by
    refine HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : ℝ × (Fin N → Euc d)) R) ?_
    intro p hp
    by_contra h
    exact hp (hS p (by simpa using h))
  have hint : Integrable F (rhoCov ρ) := hc.integrable_of_hasCompactSupport hcs
  obtain ⟨S, hSS⟩ := exists_finset_uniform (d := d) (N := N) R
  obtain ⟨C, hC⟩ := hc.bounded_above_of_compact_support hcs
  have hmeas : ∀ w, Measurable fun q => F (psi (d := d) (N := N) w q) := fun w =>
    hc.measurable.comp (measurable_psi w)
  have hintw : ∀ w, Integrable (fun q => F (psi (d := d) (N := N) w q)) ρ := fun w =>
    Integrable.of_bound (C := C) (hmeas w).aestronglyMeasurable (Eventually.of_forall fun q => hC _)
  unfold rhoCov at hint ⊢
  rw [integral_sum_measure hint]
  have hz : ∀ w ∉ S, ∫ p, F p ∂(Measure.map (psi (d := d) (N := N) w) ρ) = 0 := by
    intro w hw
    rw [integral_map (measurable_psi w).aemeasurable hc.aestronglyMeasurable]
    have : ∀ q, F (psi w q) = 0 := fun q => by
      rw [psi_eq]; exact hS _ (hSS q w hw)
    simp [this]
  rw [tsum_eq_sum (s := S) hz]
  have : ∀ w, ∫ p, F p ∂(Measure.map (psi (d := d) (N := N) w) ρ) = ∫ q, F (psi w q) ∂ρ :=
    fun w => integral_map (measurable_psi w).aemeasurable hc.aestronglyMeasurable
  simp only [this]
  rw [← integral_finsetSum _ (fun w _ => hintw w)]
  refine integral_congr_ae (Eventually.of_forall fun q => ?_)
  show ∑ w ∈ S, F (psi w q) = per F (psi 0 q)
  rw [per_eq_sum hS (fun w hw => hSS q w hw)]
  exact Finset.sum_congr rfl fun w _ => by rw [psi_eq]

end HRS.MC.CepP3
