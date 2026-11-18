import HRS.MS.PROS13CommonFactorGaussian
import HRS.MS.S21T4ProdAJ
import HRS.MS.S21T4ProdBE

/-!
# S13: squared Euclidean error norm for finite joint Gaussian families

The first n empirical coordinates are unchanged. The remaining m error
coordinates have an exact squared L² norm given by the sum of coordinate
second moments.
-/
set_option autoImplicit false
set_option maxHeartbeats 6400000
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T3
open HRS HRS.Whole HRS.MS.R2Chaos

theorem pro_s13_euclidean_append_zero_norm_sq
    {n m : ℕ} (g : Fin m → ℝ) :
    ‖(WithLp.toLp 2 (Fin.append
      (fun _ : Fin n => (0 : ℝ)) g) : EuclideanSpace ℝ (Fin (n + m)))‖ ^ 2 =
        ∑ k : Fin m, g k ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  simp [Fin.sum_univ_add, Real.norm_eq_abs, sq_abs]

theorem pro_s13_euclidean_append_zero_lintegral
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {n m : ℕ} (g : Fin m → Ω → ℝ)
    (hg : ∀ k, MemLp (g k) 2 P) :
    (∫⁻ ω, ‖(WithLp.toLp 2 (Fin.append
      (fun _ : Fin n => (0 : ℝ)) (fun k : Fin m => g k ω)) :
        EuclideanSpace ℝ (Fin (n + m)))‖ₑ ^ 2 ∂P) =
      ENNReal.ofReal (∑ k : Fin m, ∫ ω, (g k ω) ^ 2 ∂P) := by
  have hnorm : ∀ ω,
      ‖(WithLp.toLp 2 (Fin.append
        (fun _ : Fin n => (0 : ℝ)) (fun k : Fin m => g k ω)) :
          EuclideanSpace ℝ (Fin (n + m)))‖ₑ ^ 2 =
        ENNReal.ofReal (∑ k : Fin m, g k ω ^ 2) := by
    intro ω
    rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_pow (norm_nonneg _)]
    exact congrArg ENNReal.ofReal
      (pro_s13_euclidean_append_zero_norm_sq (n := n) (fun k => g k ω))
  simp_rw [hnorm]
  have hInt : Integrable (fun ω => ∑ k : Fin m, g k ω ^ 2) P :=
    integrable_finsetSum _ (fun k _ => (hg k).integrable_sq)
  have hNonneg : ∀ ω, 0 ≤ (∑ k : Fin m, g k ω ^ 2) :=
    fun ω => Finset.sum_nonneg (fun k _ => sq_nonneg _)
  rw [← ofReal_integral_eq_lintegral_ofReal hInt (ae_of_all _ hNonneg)]
  rw [integral_finset_sum _ (fun k _ => (hg k).integrable_sq)]

end HRS.MS.R26T3
