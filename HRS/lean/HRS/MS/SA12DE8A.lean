import HRS.MS.SA12DE7O
import HRS.MS.SA12C11
import HRS.MS.SA12BuildC20

/-!
# S.A.12(c), packet E7.08 (worker S82Z2), part A: box energy of periodic functions on the centred cell, and the `H^m` bound
for distributional limits

`sa12de8_centered_integral`: the integral of an `L`-periodic function over the centred cell `[-L/2,L/2)^d` equals the one over
`[0,L)^d`.  `sa12de8_boxEnergy_eq`: the box energy is the weighted jet energy of the zero extension to `ℝ^d` of the centred cell.
`sa12de8_Hm_of_box_energy`: smooth `L_n`-periodic functions `F n` (`L_n → ∞`) with `boxEnergy m (L n) (F n) ≤ B²` and
`∫ F n ψ → ∫ u ψ` for all real `C_c^∞` tests `ψ` have a limit `u ∈ H^m` with `‖u‖_{H^m} ≤ B` (`sa12de7_Hm_bound_of_weak_limit`).
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.SA12DE8

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MH.AdjointRd
  HRS.MH.AdjointRd.Phase2SA12C HRS.MH.AdjointRd.Phase2SA12Construction HRS.MS.SA12DE7

variable {d : ℕ}

theorem sa12de8_centered_integral {L : ℝ} (hL : 0 < L) {Φ : Euc d → ℝ}
    (hper : ∀ (x : Euc d) (k : Fin d → ℤ), Φ (x + L • latticePt k) = Φ x) :
    ∫ z in centeredBox d L, Φ z = ∫ z in periodBox d L, Φ z := by
  have h := sa12c20_cell_shift L hL hper (WithLp.toLp 2 fun _ : Fin d => -(L / 2))
  have hset : centeredBox d L = {z : Euc d | ∀ i, (WithLp.toLp 2 fun _ : Fin d => -(L / 2) : Euc d) i ≤ z i ∧
      z i < (WithLp.toLp 2 fun _ : Fin d => -(L / 2) : Euc d) i + L} := by
    ext z
    simp only [centeredBox, Set.mem_setOf_eq]
    refine forall_congr' fun i => ?_
    constructor <;> rintro ⟨h1, h2⟩ <;> refine ⟨h1, ?_⟩ <;> linarith
  rw [hset]
  exact h

theorem sa12de8_centeredBox_measurable (L : ℝ) : MeasurableSet (centeredBox d L) := by
  have : centeredBox d L = ⋂ i : Fin d, {y : Euc d | -(L / 2) ≤ y i} ∩ {y : Euc d | y i < L / 2} := by
    ext y
    simp only [centeredBox, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_inter_iff]
  rw [this]
  refine MeasurableSet.iInter fun i => ?_
  have hm : Measurable fun y : Euc d => y i := (EuclideanSpace.proj (𝕜 := ℝ) i).continuous.measurable
  exact (measurableSet_le measurable_const hm).inter (measurableSet_lt hm measurable_const)

theorem sa12de8_centeredBox_bounded (L : ℝ) :
    ∀ x ∈ centeredBox d L, ‖x‖ ≤ Real.sqrt ((d : ℝ) * (L / 2) ^ 2) := by
  intro x hx
  rw [EuclideanSpace.norm_eq]
  apply Real.sqrt_le_sqrt
  calc ∑ i, ‖x i‖ ^ 2 ≤ ∑ _i : Fin d, (L / 2) ^ 2 := by
        refine Finset.sum_le_sum fun i _ => ?_
        have h := hx i
        rw [Real.norm_eq_abs, sq_abs]
        exact sq_le_sq.2 (by rw [abs_of_nonneg (by linarith [h.1, h.2] : (0 : ℝ) ≤ L / 2)]
                             exact abs_le.2 ⟨h.1, h.2.le⟩)
    _ = (d : ℝ) * (L / 2) ^ 2 := by simp

theorem sa12de8_boxEnergy_eq {L : ℝ} (hL : 0 < L) (m : ℕ) {F : Euc d → ℝ}
    (hper : ∀ (x : Euc d) (k : Fin d → ℤ), F (x + L • latticePt k) = F x) :
    boxEnergy m L F = ∑ j ∈ Finset.range (m + 1), (m.choose j : ℝ) *
      ∑ idx : Fin j → Fin d, ∫ x, ((centeredBox d L).indicator (partialDeriv idx F) x) ^ 2 := by
  unfold boxEnergy
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  refine Finset.sum_congr rfl fun idx _ => ?_
  have h1 : ∀ x, ((centeredBox d L).indicator (partialDeriv idx F) x) ^ 2 =
      (centeredBox d L).indicator (fun x => (partialDeriv idx F x) ^ 2) x := by
    intro x
    by_cases hx : x ∈ centeredBox d L <;> simp [hx]
  simp_rw [h1]
  rw [integral_indicator (sa12de8_centeredBox_measurable L)]
  exact (sa12de8_centered_integral hL (Φ := fun x => (partialDeriv idx F x) ^ 2)
    (fun x k => by rw [sa12c_pd_periodic hper idx x k])).symm

end HRS.MS.SA12DE8
