import HRS.MH.ScreenedDefs

/-! Packet F3 of `B:lem:screened` (S.B.4): proof of the statement of `flowCell_geometry` in `ScreenedSpec.lean`. -/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff FourierTransform

namespace HRS.MH.Screened

open HRS HRS.Whole

variable {d : ℕ}

theorem f3_box_norm_le (v : Euc d) (hv : ∀ i, 0 ≤ v i ∧ v i ≤ 1) : ‖v‖ ≤ Real.sqrt d := by
  rw [EuclideanSpace.norm_eq]
  apply Real.sqrt_le_sqrt
  calc ∑ i, ‖v i‖ ^ 2 ≤ ∑ _i : Fin d, (1 : ℝ) := Finset.sum_le_sum fun i _ => by
        rw [Real.norm_eq_abs, sq_abs]; nlinarith [hv i]
    _ = d := by simp

theorem f3_sub_apply (x : Euc d) (z : Fin d → ℤ) (i : Fin d) :
    (x - latticePt z) i = x i - (z i : ℝ) := by
  simp [latticePt]

theorem f3_box_closed (z : Fin d → ℤ) :
    IsClosed {y : Euc d | ∀ i, 0 ≤ (y - latticePt z) i ∧ (y - latticePt z) i ≤ 1} := by
  have h : {y : Euc d | ∀ i, 0 ≤ (y - latticePt z) i ∧ (y - latticePt z) i ≤ 1} =
      ⋂ i, ({y : Euc d | 0 ≤ (y - latticePt z) i} ∩ {y : Euc d | (y - latticePt z) i ≤ 1}) := by
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_inter_iff]
  rw [h]
  refine isClosed_iInter fun i => IsClosed.inter ?_ ?_
  · exact isClosed_le continuous_const (by fun_prop)
  · exact isClosed_le (by fun_prop) continuous_const

/-- **F3** (size S).  Cells and preimages of balls for a bijective `L`-Lipschitz map `Ψ τ`:
the cells cover and are measurable, lie in `closedBall (Ψ τ (z)) (L √d)` (so have volume at most that of this
ball), `y ∈ cell z ↔ invFun y ∈ unit cube at z`, and `{x | ‖Φ x - z‖ < r} ⊆ closedBall (Ψ τ z) (L r)`. -/
theorem flowCell_geometry_proof (Ψ : ℝ → Euc d → Euc d) (τ : ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hbij : Function.Bijective (Ψ τ)) (hlip : ∀ x y, ‖Ψ τ x - Ψ τ y‖ ≤ L * ‖x - y‖) :
    (⋃ z : Fin d → ℤ, flowCell Ψ τ z) = univ ∧ (∀ z, MeasurableSet (flowCell Ψ τ z)) ∧
    (∀ z, flowCell Ψ τ z ⊆ Metric.closedBall (Ψ τ (latticePt z)) (L * Real.sqrt d)) ∧
    (∀ z (y : Euc d), y ∈ flowCell Ψ τ z ↔
      ∀ i, 0 ≤ (Function.invFun (Ψ τ) y - latticePt z) i ∧ (Function.invFun (Ψ τ) y - latticePt z) i ≤ 1) ∧
    (∀ (c : Euc d) (r : ℝ), 0 ≤ r →
      {x : Euc d | ‖Function.invFun (Ψ τ) x - c‖ < r} ⊆ Metric.closedBall (Ψ τ c) (L * r)) := by
  have hcont : Continuous (Ψ τ) := by
    have hL' : LipschitzWith (Real.toNNReal L) (Ψ τ) :=
      LipschitzWith.of_dist_le_mul fun x y => by
        rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ hL]; exact hlip x y
    exact hL'.continuous
  have hK : ∀ z : Fin d → ℤ,
      IsCompact {x : Euc d | ∀ i, 0 ≤ (x - latticePt z) i ∧ (x - latticePt z) i ≤ 1} := by
    intro z
    refine IsCompact.of_isClosed_subset (isCompact_closedBall (latticePt z) (Real.sqrt d))
      (f3_box_closed z) ?_
    intro x hx
    rw [Metric.mem_closedBall, dist_eq_norm]
    exact f3_box_norm_le _ hx
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · ext y
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    refine ⟨fun i => ⌊(Function.invFun (Ψ τ) y) i⌋, ?_⟩
    unfold flowCell
    refine ⟨Function.invFun (Ψ τ) y, ?_, Function.rightInverse_invFun hbij.surjective y⟩
    intro i
    rw [f3_sub_apply]
    constructor
    · exact sub_nonneg.2 (Int.floor_le _)
    · linarith [Int.lt_floor_add_one (Function.invFun (Ψ τ) y i)]
  · intro z
    exact ((hK z).image hcont).isClosed.measurableSet
  · intro z y hy
    unfold flowCell at hy
    obtain ⟨x, hx, rfl⟩ := hy
    rw [Metric.mem_closedBall, dist_eq_norm]
    calc ‖Ψ τ x - Ψ τ (latticePt z)‖ ≤ L * ‖x - latticePt z‖ := hlip _ _
      _ ≤ L * Real.sqrt d := mul_le_mul_of_nonneg_left (f3_box_norm_le _ hx) hL
  · intro z y
    unfold flowCell
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [Function.leftInverse_invFun hbij.injective x]
      exact hx
    · intro h
      exact ⟨Function.invFun (Ψ τ) y, h, Function.rightInverse_invFun hbij.surjective y⟩
  · intro c r hr x hx
    have hx' : ‖Function.invFun (Ψ τ) x - c‖ < r := hx
    rw [Metric.mem_closedBall, dist_eq_norm]
    have hxeq : Ψ τ (Function.invFun (Ψ τ) x) = x := Function.rightInverse_invFun hbij.surjective x
    calc ‖x - Ψ τ c‖ = ‖Ψ τ (Function.invFun (Ψ τ) x) - Ψ τ c‖ := by rw [hxeq]
      _ ≤ L * ‖Function.invFun (Ψ τ) x - c‖ := hlip _ _
      _ ≤ L * r := mul_le_mul_of_nonneg_left hx'.le hL

end HRS.MH.Screened
