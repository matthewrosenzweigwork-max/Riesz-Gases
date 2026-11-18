import HRS.MS.R26T8AR3b

/-!
# S8.2 T8A R3c: nested jets of a linear family `Y ↦ G(b(Y))(w)`
`r26t8a_R3_nest_lin`: if `B ↦ D^q (G B) (z)` is linear on a finite-dimensional space `V` with `‖D^q (G B) z‖ ≤ K ‖B‖`, then for `b ∈ C^p`:
`‖nest p q (fun (Y,w) => G (b Y) w) X z‖ ≤ K ‖D^p b X‖` (the `X`-derivatives only hit the coefficient `b`).
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

variable {d : ℕ}

theorem r26t8a_R3_nest_lin {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (G : V → Euc d → ℝ) (z : Euc d) (q : ℕ) (K : ℝ) (hK0 : 0 ≤ K)
    (hadd : ∀ B1 B2, iteratedFDeriv ℝ q (G (B1 + B2)) z =
      iteratedFDeriv ℝ q (G B1) z + iteratedFDeriv ℝ q (G B2) z)
    (hsmul : ∀ (c : ℝ) B, iteratedFDeriv ℝ q (G (c • B)) z = c • iteratedFDeriv ℝ q (G B) z)
    (hbound : ∀ B, ‖iteratedFDeriv ℝ q (G B) z‖ ≤ K * ‖B‖)
    (p : ℕ) (b : Euc d → V) (hb : ContDiff ℝ p b) (X : Euc d) :
    ‖r26t8a_nest p q (fun Yw : Euc d × Euc d => G (b Yw.1) Yw.2) X z‖ ≤ K * ‖iteratedFDeriv ℝ p b X‖ := by
  let T : V →ₗ[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin q => Euc d) ℝ :=
    { toFun := fun B => iteratedFDeriv ℝ q (G B) z
      map_add' := hadd
      map_smul' := hsmul }
  let T' : V →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin q => Euc d) ℝ := LinearMap.toContinuousLinearMap T
  have hT' : ‖T'‖ ≤ K := ContinuousLinearMap.opNorm_le_bound _ hK0 fun B => hbound B
  have e : (fun Y => iteratedFDeriv ℝ q (fun w => G (b Y) w) z) = T' ∘ b := rfl
  unfold r26t8a_nest
  rw [e]
  refine (T'.norm_iteratedFDeriv_comp_left hb.contDiffAt le_rfl).trans ?_
  exact mul_le_mul_of_nonneg_right hT' (norm_nonneg _)

end HRS.MS.R26T8A
