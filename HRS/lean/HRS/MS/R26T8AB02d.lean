import HRS.MS.R26T8AB02c
import HRS.MS.R26T8AO04b
import HRS.MS.R26T8AB02b

/-!
# S8.2 T8A B02d: joint measurability of the drift field along the process

`(t, r, w) ↦ VAge i (a0 + t - r) (X r w)` is a.e. strongly measurable for `t ∈ [0,T]`, `r ∈ [l,h]`, `0 ≤ l`, `h ≤ a0`,
`i ≤ 1` (continuity of `VAge i` on `Ici 0 × (collision set)ᶜ`, joint measurability of the process, no collisions).
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators ContDiff
namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82

/-- `VAge i` is continuous on `Ici 0 × (collision set)ᶜ` for `i ≤ 1` -/
theorem r26t8a_b02_VAge_cont (d N : ℕ) (hd : 2 ≤ d) (hN : 2 ≤ N) (a beta m M C Cf c : ℝ)
    (ha : 0 < a) (hbeta : 0 < beta) (hM : 0 ≤ M) (hC : 0 ≤ C)
    (rho : Euc d → ℝ) (hrho : IsThermalEquilibrium d (criticalS d) a beta rho)
    (Psi : (Euc d → ℝ) → Euc d → Euc d → ℝ)
    (hPsi : r26t8a_NormalFormFamily d a beta M C rho Psi)
    (horb : r26t8a_FeatureOrbits d a beta m Cf c rho) (alpha : MultiIndex d) (i : ℕ) (hi : i ≤ 1) :
    ContinuousOn (fun q : ℝ × EucConfig d N => r26t8a_VAge a beta m rho Psi alpha i q.1 q.2)
      (Set.Ici 0 ×ˢ (eucCollisionSet d N)ᶜ) := by
  obtain ⟨-, -, hD, -⟩ := r26t8a_normal_age_FTC d N hd hN a beta m M C Cf c ha hbeta hM hC rho hrho Psi hPsi
    horb alpha i hi
  have hQ := r26t8a_b02_QAge_cont d N hd hN a beta m M C Cf c ha hbeta hM hC rho hrho Psi hPsi horb alpha (i + 1)
    (by omega)
  exact hD.sub hQ

theorem r26t8a_b02_ae_good {Omega : Type} [mOmega : MeasurableSpace Omega] (d N : ℕ) (a beta : ℝ)
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X0 : Omega → EucConfig d N) (W : ℝ≥0 → Omega → Fin N → Euc d) (X : ℝ≥0 → Omega → EucConfig d N)
    (hX : IsCanonicalRealization d (criticalS d) a beta N P X0 W X) (h : ℝ) :
    ∀ᵐ w ∂P, ∀ r : ℝ, 0 ≤ r → r ≤ h → X r.toNNReal w ∉ eucCollisionSet d N := by
  filter_upwards [(hX.solution h).no_collision] with w hw r hr hrh
  exact hw r.toNNReal (by rw [Real.coe_toNNReal r hr]; exact hrh)

theorem r26t8a_b02_Vmeas (d N : ℕ) (hd : 2 ≤ d) (hN : 2 ≤ N) (a beta m M C Cf c : ℝ)
    (ha : 0 < a) (hbeta : 0 < beta) (hM : 0 ≤ M) (hC : 0 ≤ C)
    (rho : Euc d → ℝ) (hrho : IsThermalEquilibrium d (criticalS d) a beta rho)
    (Psi : (Euc d → ℝ) → Euc d → Euc d → ℝ)
    (hPsi : r26t8a_NormalFormFamily d a beta M C rho Psi)
    (horb : r26t8a_FeatureOrbits d a beta m Cf c rho) (alpha : MultiIndex d) (i : ℕ) (hi : i ≤ 1)
    {Omega : Type} [mOmega : MeasurableSpace Omega] (P : Measure Omega) [IsProbabilityMeasure P]
    (X0 : Omega → EucConfig d N) (W : ℝ≥0 → Omega → Fin N → Euc d) (X : ℝ≥0 → Omega → EucConfig d N)
    (hX : IsCanonicalRealization d (criticalS d) a beta N P X0 W X) (a0 l h T : ℝ) (hl : 0 ≤ l) (hha : h ≤ a0) :
    AEStronglyMeasurable (fun p : (ℝ × ℝ) × Omega =>
      r26t8a_VAge a beta m rho Psi alpha i (a0 + p.1.1 - p.1.2) (X p.1.2.toNNReal p.2))
      (((volume.restrict (Set.Icc 0 T)).prod (volume.restrict (Set.Icc l h))).prod P) := by
  classical
  obtain ⟨F, W', hfilt⟩ := hX.filtered
  have hXmeas := r26t8a_o04_X_meas hfilt.progressive
  set U : Set (EucConfig d N) := (eucCollisionSet d N)ᶜ with hU
  have hUo : IsOpen U := r26t8a_o03b_coll_closed.isOpen_compl
  have hVc := r26t8a_b02_VAge_cont d N hd hN a beta m M C Cf c ha hbeta hM hC rho hrho Psi hPsi horb alpha i hi
  set Hf : ℝ × EucConfig d N → ℝ := fun q => r26t8a_VAge a beta m rho Psi alpha i q.1 q.2 with hHf
  have hpw : Measurable ((Set.Ici (0 : ℝ) ×ˢ U).piecewise Hf (fun _ => 0)) :=
    ContinuousOn.measurable_piecewise hVc continuousOn_const (measurableSet_Ici.prod hUo.measurableSet)
  have hmeas : Measurable (fun p : (ℝ × ℝ) × Omega =>
      (Set.Ici (0 : ℝ) ×ˢ U).piecewise Hf (fun _ => 0) (a0 + p.1.1 - p.1.2, X p.1.2.toNNReal p.2)) := by
    refine hpw.comp (Measurable.prodMk ?_ ?_)
    · exact (measurable_const.add (measurable_fst.comp measurable_fst)).sub (measurable_snd.comp measurable_fst)
    · exact hXmeas.comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd)
  refine hmeas.aestronglyMeasurable.congr ?_
  set ρ2 : Measure (ℝ × ℝ) := (volume.restrict (Set.Icc 0 T)).prod (volume.restrict (Set.Icc l h)) with hρ2
  have h1 : ∀ᵐ q ∂ρ2, q.1 ∈ Set.Icc (0 : ℝ) T ∧ q.2 ∈ Set.Icc l h := by
    rw [hρ2, Measure.prod_restrict]
    filter_upwards [ae_restrict_mem (measurableSet_Icc.prod measurableSet_Icc)] with q hq using hq
  have h2 := r26t8a_b02_ae_good d N a beta P X0 W X hX h
  have h1' : ∀ᵐ p ∂(ρ2.prod P), p.1.1 ∈ Set.Icc (0 : ℝ) T ∧ p.1.2 ∈ Set.Icc l h :=
    (Measure.quasiMeasurePreserving_fst (μ := ρ2) (ν := P)).ae h1
  have h2' : ∀ᵐ p ∂(ρ2.prod P), ∀ r : ℝ, 0 ≤ r → r ≤ h → X r.toNNReal p.2 ∉ eucCollisionSet d N :=
    (Measure.quasiMeasurePreserving_snd (μ := ρ2) (ν := P)).ae h2
  filter_upwards [h1', h2'] with p hp1 hp2
  have hr0 : 0 ≤ p.1.2 := hl.trans hp1.2.1
  have hmem : (a0 + p.1.1 - p.1.2, X p.1.2.toNNReal p.2) ∈ Set.Ici (0 : ℝ) ×ˢ U :=
    ⟨by simp only [Set.mem_Ici]; linarith [hp1.1.1, hp1.2.2], hp2 p.1.2 hr0 hp1.2.2⟩
  simp only [hHf]
  rw [Set.piecewise_eq_of_mem _ _ _ hmem]

end HRS.MS.R26T8A

end
