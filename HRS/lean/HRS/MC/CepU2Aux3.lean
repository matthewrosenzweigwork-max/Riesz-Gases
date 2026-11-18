import HRS.MC.CepU2Aux2

/-!
# Packet CEPU2 (aux 3): transfer of the increment equation to continuous lifts
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.CepU2

open HRS

/-- If two (not necessarily continuous) lifts `A, B` satisfy the increment equation of the difference, and
`Y1, Y2` are continuous lifts of the same torus paths, the same increment equation holds for `Y1, Y2`
(U1 applied to the clipped primitive). -/
theorem cepu2_transfer {N : ℕ} {T : ℝ} (hT : 0 ≤ T) {F : ℝ → Fin N → Euc 1}
    (hFi : ∀ i, IntervalIntegrable (fun s => F s i) volume 0 T)
    {Y1 Y2 A B : ℝ≥0 → Fin N → Euc 1} (h1 : Continuous Y1) (h2 : Continuous Y2)
    (hA : ∀ t : ℝ≥0, (t : ℝ) ≤ T → (fun i => Torus.mk (A t i)) = fun i => Torus.mk (Y1 t i))
    (hB : ∀ t : ℝ≥0, (t : ℝ) ≤ T → (fun i => Torus.mk (B t i)) = fun i => Torus.mk (Y2 t i))
    (hAB : ∀ t : ℝ≥0, (t : ℝ) ≤ T → ∀ i,
      A t i - B t i = (A 0 i - B 0 i) + ∫ s in (0 : ℝ)..t, F s i) :
    ∀ t : ℝ≥0, (t : ℝ) ≤ T → ∀ i,
      Y1 t i - Y2 t i = (Y1 0 i - Y2 0 i) + ∫ s in (0 : ℝ)..t, F s i := by
  let Qc : ℝ≥0 → Fin N → Euc 1 := fun t i => (A 0 i - B 0 i) + ∫ s in (0 : ℝ)..min (t : ℝ) T, F s i
  have hQc : Continuous Qc := by
    refine continuous_pi fun i => continuous_const.add ?_
    have hg : ContinuousOn (fun u : ℝ => ∫ s in (0 : ℝ)..u, F s i) (Set.Icc 0 T) := by
      have := intervalIntegral.continuousOn_primitive_interval' (hFi i) (a := 0) (by simp [Set.mem_uIcc, hT])
      simpa [Set.uIcc_of_le hT] using this
    refine hg.comp_continuous (by fun_prop) fun t => ?_
    exact ⟨le_min t.2 hT, min_le_right _ _⟩
  have hP : Continuous (Y1 - Y2) := h1.sub h2
  have hQ : ∀ t : ℝ≥0, (t : ℝ) ≤ T → ∀ i, Qc t i = A t i - B t i := by
    intro t ht i
    simp only [Qc, min_eq_left ht]
    exact (hAB t ht i).symm
  obtain ⟨v, hv, hvt⟩ := HRS.MC.CepK0.cep_U1_lift_const_proof hT hQc hP (by
    intro t ht
    funext i
    have e1 := congrFun (hA t ht) i
    have e2 := congrFun (hB t ht) i
    rw [hQ t ht i]
    show Torus.mk (A t i - B t i) = Torus.mk (Y1 t i - Y2 t i)
    rw [cepu2_mk_sub, cepu2_mk_sub, e1, e2])
  intro t ht i
  have h0 : (0 : ℝ) ≤ T := hT
  have e0 := congrFun (hvt 0 (by simpa using h0)) i
  have et := congrFun (hvt t ht) i
  have q0 : Qc 0 i = A 0 i - B 0 i := by
    simp only [Qc, NNReal.coe_zero, min_eq_left hT]
    simp
  have qt : Qc t i = (A 0 i - B 0 i) + ∫ s in (0 : ℝ)..t, F s i := by
    simp only [Qc, min_eq_left ht]
  rw [Pi.sub_apply] at et e0
  rw [Pi.add_apply] at et e0
  rw [Pi.sub_apply] at et e0
  rw [qt] at et
  rw [q0] at e0
  rw [et, e0]
  abel

end HRS.MC.CepU2
