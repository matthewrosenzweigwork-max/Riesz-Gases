import HRS.MC.CepU2Aux3

/-!
# Packet CEPU2 (aux 4): deterministic core of the uniqueness (K2 + K3 + U1b in one chamber)
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.CepU2

open HRS

theorem cepu2_core {N : ℕ} {D : DynData 1} (hs : D.s = 0) {a : ℝ} (ha : 0 < a)
    (hM : D.M = -(a • (1 : Matrix (Fin 1) (Fin 1) ℝ))) (hV : HRS.MC.CepK2.cep_IsC11 D.V)
    {T : ℝ} (hT : 0 ≤ T) {π π' : Equiv.Perm (Fin N)} {Y1 Y2 : ℝ≥0 → Fin N → Euc 1}
    (o1 : ∀ t : ℝ≥0, (t : ℝ) ≤ T → CyclicallyOrdered π (Y1 t))
    (o2 : ∀ t : ℝ≥0, (t : ℝ) ≤ T → CyclicallyOrdered π' (Y2 t))
    (hinit : (fun i => Torus.mk (Y1 0 i)) = fun i => Torus.mk (Y2 0 i))
    (hfree0 : (fun i => Torus.mk (Y1 0 i)) ∉ collisionSet 1 N)
    {F : ℝ → Fin N → Euc 1}
    (hFi : ∀ i, IntervalIntegrable (fun s => F s i) volume 0 T)
    (hP : ∀ t : ℝ≥0, (t : ℝ) ≤ T → ∀ i,
      Y1 t i - Y2 t i = (Y1 0 i - Y2 0 i) + ∫ s in (0 : ℝ)..t, F s i)
    (hF : ∀ s : ℝ, 0 ≤ s → s ≤ T →
      F s = liftedDrift D (Y1 s.toNNReal) - liftedDrift D (Y2 s.toNNReal))
    (hfree : ∀ᵐ s ∂(volume.restrict (Set.Icc 0 T)),
      (fun i => Torus.mk (Y1 s.toNNReal i)) ∉ collisionSet 1 N ∧
      (fun i => Torus.mk (Y2 s.toNNReal i)) ∉ collisionSet 1 N) :
    ∀ t : ℝ≥0, (t : ℝ) ≤ T → (fun i => Torus.mk (Y1 t i)) = fun i => Torus.mk (Y2 t i) := by
  have h00 : ((0 : ℝ≥0) : ℝ) ≤ T := by simpa using hT
  obtain ⟨w, hw, hw'⟩ := exists_lattice_shift (fun i => congrFun hinit i)
  have hs1 := cepu2_strict (o1 0 h00) hfree0
  have hs2 : HRS.MC.CepK0.cep_StrictlyOrdered π' (Y1 0 + w) := by
    rw [← hw']
    exact cepu2_strict (o2 0 h00) (by rw [← hinit]; exact hfree0)
  have chamber := HRS.MC.CepK0.cep_U1b_chamber_unique_proof hw hs1 hs2
  have ord2 : ∀ t : ℝ≥0, (t : ℝ) ≤ T → CyclicallyOrdered π (Y2 t - w) := fun t ht =>
    chamber _ (by rw [sub_add_cancel]; exact o2 t ht)
  obtain ⟨Λ, hΛ⟩ := HRS.MC.CepK2.cep_K2_drift_dissipative_proof (N := N) hs ha.le hM hV
  have hZ0 : (fun s : ℝ => Y1 s.toNNReal - (Y2 s.toNNReal - w)) 0 = 0 := by
    simp only [Real.toNNReal_zero]
    rw [hw']
    abel
  have hmain := cepu2_gronwall (Λ := Λ) hT (Z := fun s : ℝ => Y1 s.toNNReal - (Y2 s.toNNReal - w)) hFi
    (by
      intro t ht i
      simp only [Real.toNNReal_zero]
      have hP' := hP t.toNNReal (by rw [Real.coe_toNNReal t ht.1]; exact ht.2) i
      rw [Real.coe_toNNReal t ht.1] at hP'
      show Y1 t.toNNReal i - (Y2 t.toNNReal i - w i) = (Y1 0 i - (Y2 0 i - w i)) + _
      have h1 : Y1 t.toNNReal i - Y2 t.toNNReal i + w i =
          (Y1 0 i - Y2 0 i) + (∫ s in (0 : ℝ)..t, F s i) + w i := by rw [hP']
      have h2 : Y2 0 i = Y1 0 i + w i := by rw [hw']; rfl
      rw [h2] at h1
      calc Y1 t.toNNReal i - (Y2 t.toNNReal i - w i)
          = Y1 t.toNNReal i - Y2 t.toNNReal i + w i := by abel
        _ = _ := by rw [h1, h2]; abel)
    hZ0
    (by
      filter_upwards [hfree, ae_restrict_mem measurableSet_Icc] with s hs' hmem
      have hc : ((s.toNNReal : ℝ≥0) : ℝ) = s := Real.coe_toNNReal s hmem.1
      have hle : ((s.toNNReal : ℝ≥0) : ℝ) ≤ T := by rw [hc]; exact hmem.2
      have hfree2 : (fun i => Torus.mk ((Y2 s.toNNReal - w) i)) ∉ collisionSet 1 N := by
        rw [cepu2_mk_sub_lattice hw]; exact hs'.2
      have key := hΛ π (Y1 s.toNNReal) (Y2 s.toNNReal - w) (o1 _ hle) (ord2 _ hle) hs'.1 hfree2
      have hld : liftedDrift D (Y2 s.toNNReal - w) = liftedDrift D (Y2 s.toNNReal) := by
        unfold liftedDrift
        rw [cepu2_mk_sub_lattice hw]
      rw [hld] at key
      have hFs := hF s hmem.1 hmem.2
      simp only [hFs, Pi.sub_apply]
      exact key)
  intro t ht
  have := hmain (t : ℝ) ⟨t.2, ht⟩
  simp only [Real.toNNReal_coe] at this
  have h3 : Y1 t = Y2 t - w := sub_eq_zero.1 this
  rw [h3, cepu2_mk_sub_lattice hw]

end HRS.MC.CepU2
