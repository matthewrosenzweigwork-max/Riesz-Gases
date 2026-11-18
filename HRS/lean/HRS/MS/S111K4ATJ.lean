import HRS.MS.S111K4ATH
import HRS.MS.R2InterpAux3

/-!
# S11.1 / all-tests boundary (S111K4AT), piece J: evaluation functionals of Hermite sections and the tensor limit

`k4ell τ n φ` is the evaluation functional `w ↦ w(τ)(φ_n)` of the section `φ_n`; it converges in operator norm to any functional
`l` representing `w ↦ w(τ)(φ)`; and `J(l1_n ⊗ l2_n) → J(l1 ⊗ l2)` for every `J` in the projective tensor space.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S111K4AT

open HRS HRS.Whole HRS.MS.R2Interp

variable {d : ℕ} {m T : ℝ}

/-- The evaluation functional `w ↦ w(τ)(φ_n)` on the path space. -/
def k4ell (τ : Set.Icc (0 : ℝ) T) (n : ℕ) (φ : Euc d → ℝ) : StrongDual ℝ (OscPath d m T) :=
  ∑ α ∈ (multiIndex_sublevel_finite d n).toFinset,
    (oscEigenvalue d α ^ (m / 2) * hermiteCoeff φ α) • s102_ell τ α

theorem k4ell_apply (τ : Set.Icc (0 : ℝ) T) (n : ℕ) (φ : Euc d → ℝ) (w : OscPath d m T) :
    k4ell τ n φ w = OscDual.eval (OscPath.at' w τ) (k4hs m n φ) := by
  rw [k4hs_eval]
  simp [k4ell, s102_ell_apply, ContinuousLinearMap.sum_apply]

theorem k4ell_dist (τ : Set.Icc (0 : ℝ) T) (n : ℕ) {φ : Euc d → ℝ} (hφ : MemOsc m φ)
    {l : StrongDual ℝ (OscPath d m T)} (hl : ∀ w, l w = OscDual.eval (OscPath.at' w τ) φ) :
    ‖k4ell τ n φ - l‖ ≤ ‖OscSpace.ofFun m (k4hs m n φ) - OscSpace.ofFun m φ‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun w => ?_
  have hn : MemOsc m (k4hs m n φ) := (k4hs_osc m n φ).2
  have h1 : (k4ell (m := m) τ n φ - l) w =
      OscDual.toDual (OscPath.at' w τ) (OscSpace.ofFun m (k4hs m n φ) - OscSpace.ofFun m φ) := by
    rw [sub_apply, k4ell_apply, hl, map_sub, OscDual.toDual_ofFun _ _ hn,
      OscDual.toDual_ofFun _ _ hφ]
  rw [h1]
  refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
  rw [LinearIsometryEquiv.norm_map]
  have h2 : ‖OscPath.at' w τ‖ ≤ ‖w‖ :=
    ContinuousMap.norm_coe_le_norm (show C(Set.Icc (0 : ℝ) T, OscDual d m) from w) τ
  rw [mul_comm]
  exact mul_le_mul_of_nonneg_left h2 (norm_nonneg _)

/-- The bilinear form `(w₁, w₂) ↦ a(w₁) b(w₂)` on the path space. -/
def k4M (a b : StrongDual ℝ (OscPath d m T)) : (OscPath d m T) [×2]→L[ℝ] ℝ :=
  (ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 2) ℝ).compContinuousLinearMap ![a, b]

theorem k4M_sub (a1 a2 b1 b2 : StrongDual ℝ (OscPath d m T)) :
    k4M a1 b1 - k4M a2 b2 = k4M (a1 - a2) b1 + k4M a2 (b1 - b2) := by
  ext w
  simp [k4M, Fin.prod_univ_two]
  ring

theorem k4M_norm (a b : StrongDual ℝ (OscPath d m T)) : ‖k4M a b‖ ≤ ‖a‖ * ‖b‖ := by
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  have h1 : ‖ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 2) ℝ‖ ≤ 1 :=
    ContinuousMultilinearMap.norm_mkPiAlgebra_le
  simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  calc _ ≤ 1 * (‖a‖ * ‖b‖) := mul_le_mul_of_nonneg_right h1 (by positivity)
    _ = _ := one_mul _

theorem k4J_tendsto (J : projTensor (OscPath d m T) 2) {l1 l2 : StrongDual ℝ (OscPath d m T)}
    {l1n l2n : ℕ → StrongDual ℝ (OscPath d m T)}
    (h1 : Tendsto (fun n => ‖l1n n - l1‖) atTop (𝓝 0))
    (h2 : Tendsto (fun n => ‖l2n n - l2‖) atTop (𝓝 0)) :
    Tendsto (fun n => (J : TensorDual (OscPath d m T) 2) (k4M (l1n n) (l2n n))) atTop
      (𝓝 ((J : TensorDual (OscPath d m T) 2) (k4M l1 l2))) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hb : ∀ n, ‖(J : TensorDual (OscPath d m T) 2) (k4M (l1n n) (l2n n)) -
      (J : TensorDual (OscPath d m T) 2) (k4M l1 l2)‖ ≤
      ‖(J : TensorDual (OscPath d m T) 2)‖ * (‖l1n n - l1‖ * (‖l2‖ + ‖l2n n - l2‖) + ‖l1‖ * ‖l2n n - l2‖) := by
    intro n
    rw [← map_sub]
    refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    rw [k4M_sub]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · refine (k4M_norm _ _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
      calc ‖l2n n‖ = ‖(l2n n - l2) + l2‖ := by rw [sub_add_cancel]
        _ ≤ ‖l2n n - l2‖ + ‖l2‖ := norm_add_le _ _
        _ = _ := add_comm _ _
    · exact (k4M_norm _ _).trans le_rfl
  refine squeeze_zero (fun n => norm_nonneg _) hb ?_
  have : Tendsto (fun n => ‖(J : TensorDual (OscPath d m T) 2)‖ *
      (‖l1n n - l1‖ * (‖l2‖ + ‖l2n n - l2‖) + ‖l1‖ * ‖l2n n - l2‖)) atTop
      (𝓝 (‖(J : TensorDual (OscPath d m T) 2)‖ * (0 * (‖l2‖ + 0) + ‖l1‖ * 0))) :=
    ((h1.mul (h2.const_add ‖l2‖)).add (h2.const_mul ‖l1‖)).const_mul _
  simpa using this

end HRS.MS.S111K4AT
