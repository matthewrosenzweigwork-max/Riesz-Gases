import HRS.MS.S21G2_S12C
import HRS.MS.S21G2_S12E

/-!
# S21G2 S12 (part F) -- coordinate maps between `ℝ^{n+m}`, `ℝ^n × ℝ^m` and the Euclidean space (R26-T3.S12)

Helpers `s21g2_s12_`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.R26T3

theorem s21g2_s12_cg_map {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F] [BorelSpace F]
    {γ : Measure E} (hγ : HRS.IsCenteredGaussian γ) (T : E →L[ℝ] F) :
    HRS.IsCenteredGaussian (γ.map T) := by
  have := hγ.1
  refine ⟨ProbabilityTheory.isGaussian_map T, fun L => ?_⟩
  rw [integral_map T.continuous.measurable.aemeasurable L.continuous.aestronglyMeasurable]
  exact hγ.2 (L.comp T)

/-- Splitting `ℝ^{n+m}` as `ℝ^n × ℝ^m`. -/
def s21g2_s12_Tv (n m : ℕ) : (Fin (n + m) → ℝ) →L[ℝ] (Fin n → ℝ) × (Fin m → ℝ) :=
  ContinuousLinearMap.prod
    (ContinuousLinearMap.pi fun i : Fin n => ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (n + m) => ℝ) (Fin.castAdd m i))
    (ContinuousLinearMap.pi fun j : Fin m => ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (n + m) => ℝ) (Fin.natAdd n j))

theorem s21g2_s12_Tv_apply (n m : ℕ) (w : Fin (n + m) → ℝ) :
    s21g2_s12_Tv n m w = (fun i : Fin n => w (Fin.castAdd m i), fun j : Fin m => w (Fin.natAdd n j)) := rfl

theorem s21g2_s12_lin_expand {n m : ℕ} (L : ((Fin n → ℝ) × (Fin m → ℝ)) →L[ℝ] ℝ) :
    ∃ α : Fin (n + m) → ℝ, ∀ w, L (s21g2_s12_Tv n m w) = ∑ k, α k * w k := by
  classical
  refine ⟨fun k => (L.comp (s21g2_s12_Tv n m)) (fun j => if k = j then 1 else 0), fun w => ?_⟩
  have := (L.comp (s21g2_s12_Tv n m)).toLinearMap.pi_apply_eq_sum_univ w
  simp only [ContinuousLinearMap.coe_coe, ContinuousLinearMap.comp_apply, smul_eq_mul] at this
  rw [this]
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

end HRS.MS.R26T3
