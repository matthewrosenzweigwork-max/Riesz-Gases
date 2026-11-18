import HRS.Sections.ScrnAux32

/-!
# Packet SCRN, part 33: from `d3DistE` to `smoothDist 3`, and the PSD of the particle covariance

* `scrn_smoothDist_le_d3`: `d3DistE μ ν ≤ ofReal B → smoothDist 3 μ ν ≤ B` (`CbUnitBall 3 ⊆ D3TestClass`).
* `scrn_gram_psd`: Gram matrices of continuous functions on the torus are positive semidefinite.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace HRS

variable {d : ℕ}

local notation "ℝ^" p => EuclideanSpace ℝ (Fin p)

theorem scrn_smoothDist_le_d3 {p : ℕ} (μ ν : Measure (ℝ^p)) {B : ℝ} (hB : 0 ≤ B)
    (h : d3DistE μ ν ≤ ENNReal.ofReal B) : smoothDist 3 μ ν ≤ B := by
  have : Nonempty (CbUnitBall (ℝ^p) 3) := ⟨⟨0, zero_mem_cbUnitBall 3⟩⟩
  refine Real.iSup_le (fun Φ => ?_) hB
  have hΦ : Φ.1 ∈ D3TestClass p := by
    refine ⟨⟨Φ.2.1, Φ.2.2.1⟩, fun j hj1 hj3 x => ?_⟩
    exact iteratedFDeriv_norm_le_of_mem Φ.2 hj3 x
  have h1 : ENNReal.ofReal |∫ x, Φ.1 x ∂μ - ∫ x, Φ.1 x ∂ν| ≤ d3DistE μ ν :=
    le_iSup (fun h : D3TestClass p => ENNReal.ofReal |∫ x, h.1 x ∂μ - ∫ x, h.1 x ∂ν|) ⟨Φ.1, hΦ⟩
  exact (ENNReal.ofReal_le_ofReal_iff hB).1 (h1.trans h)

theorem scrn_gram_psd {p : ℕ} (c : Fin p → Torus d → ℝ) (hc : ∀ a, Continuous (c a)) :
    (Matrix.of fun a b => ∫ y, c a y * c b y ∂(volume : Measure (Torus d))).PosSemidef := by
  have hint : ∀ a b, Integrable (fun y => c a y * c b y) (volume : Measure (Torus d)) := fun a b =>
    ((hc a).mul (hc b)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
  · refine Matrix.IsHermitian.ext fun a b => ?_
    simp only [star_trivial, Matrix.of_apply]
    exact integral_congr_ae (Filter.Eventually.of_forall fun y => mul_comm _ _)
  · simp only [star_trivial, dotProduct, Matrix.mulVec, Matrix.of_apply]
    have e : ∑ a, x a * ∑ b, (∫ y, c a y * c b y) * x b =
        ∫ y, ∑ a, ∑ b, (x a * x b) * (c a y * c b y) := by
      rw [integral_finsetSum _ (fun a _ => integrable_finsetSum _ fun b _ => (hint a b).const_mul _)]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [integral_finsetSum _ (fun b _ => (hint a b).const_mul _), Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [integral_const_mul]; ring
    rw [e]
    refine integral_nonneg fun y => ?_
    have : ∑ a, ∑ b, (x a * x b) * (c a y * c b y) = (∑ a, x a * c a y) ^ 2 := by
      rw [sq, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
    rw [this]; exact sq_nonneg _

end HRS
