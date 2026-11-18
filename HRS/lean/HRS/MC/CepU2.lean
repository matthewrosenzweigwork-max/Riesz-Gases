import HRS.MC.CepU2Aux4

/-!
# Packet CEPU2: pathwise uniqueness among cyclically ordered contact flows (second half of `cepa_log_flow`)

Relocated proof of `HRS.MC.Cepa.cep_U2_flow_unique` (`HRS/MC/CepaSpec.lean`); the tie is
`HRS/MC/CepU2Tie.lean`.  The spec file is not imported here, so `cep_IsC11` is the duplicate
`HRS.MC.CepK2.cep_IsC11` (same body).

Route: for a.e. `ω`, take the continuous ordered lifts `Yc, Yc'` of the two flows; the noise cancels in the
difference of the integrated equations (`cepu2_transfer` moves the increment equation to the continuous
lifts via U1); after a lattice shift both lifts lie in one closed chamber (U1b) with equal initial point;
a.e. time both are contact free (`occupation`), so K2 gives one-sided Lipschitz dissipativity and K3 (Gronwall)
gives equality.
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.CepU2

open HRS

theorem cep_U2_flow_unique_proof {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {N : ℕ}
    {D : DynData 1} (hs : D.s = 0) {a : ℝ} (ha : 0 < a)
    (hM : D.M = -(a • (1 : Matrix (Fin 1) (Fin 1) ℝ))) (hV : HRS.MC.CepK2.cep_IsC11 D.V)
    {X₀ : Ω → Config 1 N} (hdist : ∀ᵐ ω ∂P, X₀ ω ∉ collisionSet 1 N)
    {W : ℝ≥0 → Ω → (Fin N → Euc 1)} {T : ℝ} {X X' : ℝ≥0 → Ω → Config 1 N}
    (hX : IsCepaLepingleFlow P D T X₀ W X) (hX' : IsCepaLepingleFlow P D T X₀ W X') :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ) ≤ T → X t ω = X' t ω := by
  by_cases hT : 0 ≤ T
  swap
  · exact Filter.Eventually.of_forall fun ω t ht => absurd (t.2.trans ht) hT
  obtain ⟨Y, hY, hXY⟩ := hX.toContact.lift
  obtain ⟨Y', hY', hXY'⟩ := hX'.toContact.lift
  subst hXY hXY'
  obtain ⟨π, -, hπ⟩ := hX.ordered
  obtain ⟨π', -, hπ'⟩ := hX'.ordered
  filter_upwards [hY, hY', hπ, hπ', hX.occupation, hX'.occupation, hX.toContact.init,
    hX'.toContact.init, hdist] with ω hYω hY'ω hπω hπ'ω hocc hocc' hi hi' hd
  obtain ⟨Yc, hYc1, hYc2, hYc3⟩ := hπω
  obtain ⟨Yc', hYc1', hYc2', hYc3'⟩ := hπ'ω
  have hT' : (((T.toNNReal : ℝ≥0)) : ℝ) = T := Real.coe_toNNReal T hT
  -- the drifts as functions of time
  let bX : ℝ → Fin N → Euc 1 := fun s i => particleDrift D (projectPath Y s.toNNReal ω) i
  let bX' : ℝ → Fin N → Euc 1 := fun s i => particleDrift D (projectPath Y' s.toNNReal ω) i
  have hbX : ∀ i, IntegrableOn (fun s => bX s i) (Set.Icc 0 T) := by
    intro i
    have := (hYω T.toNNReal (by rw [hT']))
    rw [hT'] at this
    exact this.1 i
  have hbX' : ∀ i, IntegrableOn (fun s => bX' s i) (Set.Icc 0 T) := by
    intro i
    have := (hY'ω T.toNNReal (by rw [hT']))
    rw [hT'] at this
    exact this.1 i
  have hbXt : ∀ t : ℝ≥0, (t : ℝ) ≤ T → ∀ i, IntegrableOn (fun s => bX s i) (Set.Icc 0 (t : ℝ)) :=
    fun t ht i => (hbX i).mono_set (Set.Icc_subset_Icc le_rfl ht)
  have hbXt' : ∀ t : ℝ≥0, (t : ℝ) ≤ T → ∀ i, IntegrableOn (fun s => bX' s i) (Set.Icc 0 (t : ℝ)) :=
    fun t ht i => (hbX' i).mono_set (Set.Icc_subset_Icc le_rfl ht)
  let F : ℝ → Fin N → Euc 1 := fun s i => bX s i - bX' s i
  have hFi : ∀ i, IntervalIntegrable (fun s => F s i) volume 0 T := by
    intro i
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hT]
    exact (hbX i).sub (hbX' i)
  have hAB : ∀ t : ℝ≥0, (t : ℝ) ≤ T → ∀ i,
      Y t ω i - Y' t ω i = (Y 0 ω i - Y' 0 ω i) + ∫ s in (0 : ℝ)..t, F s i := by
    intro t ht i
    have e1 := (hYω t ht).2 i
    have e2 := (hY'ω t ht).2 i
    have hint : ∫ s in (0 : ℝ)..t, F s i =
        (∫ s in Set.Icc (0 : ℝ) t, bX s i) - ∫ s in Set.Icc (0 : ℝ) t, bX' s i := by
      rw [intervalIntegral.integral_of_le (NNReal.coe_nonneg t), ← MeasureTheory.integral_Icc_eq_integral_Ioc]
      exact MeasureTheory.integral_sub (hbXt t ht i) (hbXt' t ht i)
    rw [hint]
    have e1' : Y t ω i = Y 0 ω i + (∫ s in Set.Icc (0 : ℝ) t, bX s i) +
        Real.sqrt (2 * D.invβ) • (W t ω i - W 0 ω i) := by
      exact e1
    have e2' : Y' t ω i = Y' 0 ω i + (∫ s in Set.Icc (0 : ℝ) t, bX' s i) +
        Real.sqrt (2 * D.invβ) • (W t ω i - W 0 ω i) := by
      exact e2
    rw [e1', e2']
    abel
  have hmkA : ∀ t : ℝ≥0, (t : ℝ) ≤ T →
      (fun i => Torus.mk (Y t ω i)) = fun i => Torus.mk (Yc t i) := by
    intro t ht
    rw [← hYc1 t ht]
    rfl
  have hmkB : ∀ t : ℝ≥0, (t : ℝ) ≤ T →
      (fun i => Torus.mk (Y' t ω i)) = fun i => Torus.mk (Yc' t i) := by
    intro t ht
    rw [← hYc1' t ht]
    rfl
  have hP := cepu2_transfer hT hFi hYc2 hYc2' hmkA hmkB hAB
  have h00 : ((0 : ℝ≥0) : ℝ) ≤ T := by simpa using hT
  have hinit : (fun i => Torus.mk (Yc 0 i)) = fun i => Torus.mk (Yc' 0 i) := by
    rw [← hYc1 0 h00, ← hYc1' 0 h00, hi, hi']
  have hfree0 : (fun i => Torus.mk (Yc 0 i)) ∉ collisionSet 1 N := by
    rw [← hYc1 0 h00, hi]; exact hd
  have hF : ∀ s : ℝ, 0 ≤ s → s ≤ T →
      F s = liftedDrift D (Yc s.toNNReal) - liftedDrift D (Yc' s.toNNReal) := by
    intro s hs0 hsT
    have hle : ((s.toNNReal : ℝ≥0) : ℝ) ≤ T := by rw [Real.coe_toNNReal s hs0]; exact hsT
    funext i
    simp only [F, bX, bX', liftedDrift, Pi.sub_apply, hYc1 _ hle, hYc1' _ hle]
  have hfree : ∀ᵐ s ∂(volume.restrict (Set.Icc 0 T)),
      (fun i => Torus.mk (Yc s.toNNReal i)) ∉ collisionSet 1 N ∧
      (fun i => Torus.mk (Yc' s.toNNReal i)) ∉ collisionSet 1 N := by
    rw [ae_restrict_iff' measurableSet_Icc]
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hocc, measure_eq_zero_iff_ae_notMem.1 hocc']
      with s h1 h2 hs'
    have hle : ((s.toNNReal : ℝ≥0) : ℝ) ≤ T := by rw [Real.coe_toNNReal s hs'.1]; exact hs'.2
    refine ⟨?_, ?_⟩
    · rw [← hYc1 _ hle]; exact fun hc => h1 ⟨hs', hc⟩
    · rw [← hYc1' _ hle]; exact fun hc => h2 ⟨hs', hc⟩
  have hcore := cepu2_core hs ha hM hV hT hYc3 hYc3' hinit hfree0 hFi hP hF hfree
  intro t ht
  rw [hYc1 t ht, hYc1' t ht]
  exact hcore t ht

end HRS.MC.CepU2
