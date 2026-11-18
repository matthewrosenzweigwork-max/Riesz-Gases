import HRS.MS.SA12X3C7C7

/-!
# S.A.12 C7 (SA12X3), part C8 (7C): flowed cubes

Compactness of flowed cubes, the cover of a shifted flowed cube by `2^d` unshifted ones, the resulting integral bound,
and the volume of a flowed cube.
-/

set_option autoImplicit false
set_option maxHeartbeats 3200000

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12Near

open HRS HRS.Whole HRS.MH.AdjointRd

variable {d : ℕ}

theorem sa12x3_cube_compact (c : Euc d) :
    IsCompact {y : Euc d | ∀ i, 0 ≤ (y - c) i ∧ (y - c) i ≤ 1} := by
  have hcl : IsClosed {y : Euc d | ∀ i, 0 ≤ (y - c) i ∧ (y - c) i ≤ 1} := by
    have : {y : Euc d | ∀ i, 0 ≤ (y - c) i ∧ (y - c) i ≤ 1} =
        ⋂ i, {y : Euc d | 0 ≤ (y - c) i ∧ (y - c) i ≤ 1} := by ext y; simp
    rw [this]
    refine isClosed_iInter fun i => ?_
    have hc : Continuous (fun y : Euc d => (y - c) i) :=
      (EuclideanSpace.proj i).continuous.comp (continuous_id.sub continuous_const)
    exact (isClosed_le continuous_const hc).inter (isClosed_le hc continuous_const)
  refine Metric.isCompact_of_isClosed_isBounded hcl ?_
  refine (Metric.isBounded_closedBall (x := c) (r := Real.sqrt d)).subset fun y hy => ?_
  rw [mem_closedBall_iff_norm, EuclideanSpace.norm_eq]
  refine Real.sqrt_le_sqrt ?_
  calc ∑ i, ‖(y - c) i‖ ^ 2 ≤ ∑ _i : Fin d, (1 : ℝ) := by
        refine Finset.sum_le_sum fun i _ => ?_
        have := hy i
        rw [Real.norm_eq_abs, abs_of_nonneg this.1]
        nlinarith [this.1, this.2]
    _ = d := by simp

theorem sa12x3_flowCellAt_compact {Ψ : ℝ → Euc d → Euc d} {τ : ℝ} (hΨ : Continuous (Ψ τ)) (c : Euc d) :
    IsCompact (flowCellAt Ψ τ c) := (sa12x3_cube_compact c).image hΨ

theorem sa12x3_flowCell_compact {Ψ : ℝ → Euc d → Euc d} {τ : ℝ} (hΨ : Continuous (Ψ τ)) (z : Fin d → ℤ) :
    IsCompact (flowCell Ψ τ z) := (sa12x3_cube_compact (latticePt z)).image hΨ

/-- A shifted flowed cube lies in the union of `2^d` unshifted flowed cubes. -/
theorem sa12x3_cell_cover (Ψ : ℝ → Euc d → Euc d) (τ : ℝ) (z : Fin d → ℤ) {e : Euc d}
    (he0 : ∀ i, 0 ≤ e i) (he1 : ∀ i, e i < 1) :
    flowCellAt Ψ τ (latticePt z + e) ⊆
      ⋃ ε : Fin d → Fin 2, flowCell Ψ τ (z + fun i => ((ε i : ℕ) : ℤ)) := by
  rintro _ ⟨y, hy, rfl⟩
  set ε : Fin d → Fin 2 := fun i => if (y - latticePt z) i ≤ 1 then 0 else 1 with hε
  refine Set.mem_iUnion.2 ⟨ε, ?_⟩
  refine ⟨y, fun i => ?_, rfl⟩
  have h := hy i
  have e1 : (y - (latticePt z + e)) i = (y - latticePt z) i - e i := by simp; ring
  rw [e1] at h
  have e2 : (y - latticePt (z + fun i => ((ε i : ℕ) : ℤ))) i = (y - latticePt z) i - ((ε i : ℕ) : ℝ) := by
    simp [latticePt]; ring
  rw [e2]
  have hei := he0 i
  have hei1 := he1 i
  by_cases hc : (y - latticePt z) i ≤ 1
  · have : (ε i : ℕ) = 0 := by simp only [hε, if_pos hc]; rfl
    rw [this]
    constructor <;> push_cast <;> linarith [h.1, h.2]
  · have : (ε i : ℕ) = 1 := by simp only [hε, if_neg hc]; rfl
    rw [this]
    push_neg at hc
    constructor <;> push_cast <;> linarith [h.1, h.2]

/-- Volume bound of a flowed cube from a Lipschitz bound. -/
theorem sa12x3_flowCell_vol {Ψ : ℝ → Euc d → Euc d} {τ : ℝ} {Lp : ℝ} (hL : ∀ x y, ‖Ψ τ x - Ψ τ y‖ ≤ Lp * ‖x - y‖)
    (hLp : 0 ≤ Lp) (z : Fin d → ℤ) :
    volume (flowCell Ψ τ z) ≤ volume (closedBall (0 : Euc d) (Lp * Real.sqrt d)) := by
  have hsub : flowCell Ψ τ z ⊆ closedBall (Ψ τ (latticePt z)) (Lp * Real.sqrt d) := by
    rintro _ ⟨y, hy, rfl⟩
    rw [mem_closedBall_iff_norm]
    have h1 := hL y (latticePt z)
    have h2 : ‖y - latticePt z‖ ≤ Real.sqrt d := by
      rw [EuclideanSpace.norm_eq]
      refine Real.sqrt_le_sqrt ?_
      calc ∑ i, ‖(y - latticePt z) i‖ ^ 2 ≤ ∑ _i : Fin d, (1 : ℝ) := by
            refine Finset.sum_le_sum fun i _ => ?_
            have := hy i
            rw [Real.norm_eq_abs, abs_of_nonneg this.1]
            nlinarith [this.1, this.2]
        _ = d := by simp
    calc ‖Ψ τ y - Ψ τ (latticePt z)‖ ≤ Lp * ‖y - latticePt z‖ := h1
      _ ≤ Lp * Real.sqrt d := mul_le_mul_of_nonneg_left h2 hLp
  calc volume (flowCell Ψ τ z) ≤ volume (closedBall (Ψ τ (latticePt z)) (Lp * Real.sqrt d)) := measure_mono hsub
    _ = volume (closedBall (0 : Euc d) (Lp * Real.sqrt d)) := Measure.addHaar_closedBall_center volume (Ψ τ (latticePt z)) _

end HRS.MH.AdjointRd.Phase2SA12Near
