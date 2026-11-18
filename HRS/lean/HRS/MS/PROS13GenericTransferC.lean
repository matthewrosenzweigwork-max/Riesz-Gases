import HRS.MS.PROS13GenericTransferB
import HRS.MS.S21H2_S14aD1

/-!
# Additivity of the iterated mean for arbitrary product-L² kernels

No pointwise row integrability is postulated. The row integrals are
integrable at almost every point, exactly as follows from product L².
-/
set_option autoImplicit false
set_option maxHeartbeats 6400000
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T3
open HRS HRS.Whole HRS.MS.R2Chaos
variable {d : ℕ} {μ : Measure (Euc d)} [IsProbabilityMeasure μ]

theorem pro_s13_generic_double_mean_sub
    (h h' : Euc d → Euc d → ℝ)
    (hm : MemLp (fun z : Euc d × Euc d => h z.1 z.2) 2 (μ.prod μ))
    (hm' : MemLp (fun z : Euc d × Euc d => h' z.1 z.2) 2 (μ.prod μ)) :
    (∫ x, ∫ y, (h x y - h' x y) ∂μ ∂μ) =
    (∫ x, ∫ y, h x y ∂μ ∂μ) -
    (∫ x, ∫ y, h' x y ∂μ ∂μ) := by
  have hslice : ∀ᵐ x ∂μ,
      Integrable (fun y => h x y) μ ∧ Integrable (fun y => h' x y) μ := by
    filter_upwards [s21h2_slice_memLp μ hm, s21h2_slice_memLp μ hm'] with x h1 h2
    exact ⟨h1.integrable one_le_two, h2.integrable one_le_two⟩
  have hmL : MemLp (fun x => ∫ y, h x y ∂μ) 2 μ :=
    s21h2_m_memLp μ hm
  have hmL' : MemLp (fun x => ∫ y, h' x y ∂μ) 2 μ :=
    s21h2_m_memLp μ hm'
  rw [← integral_sub (hmL.integrable one_le_two)
    (hmL'.integrable one_le_two)]
  apply integral_congr_ae
  filter_upwards [hslice] with x hx
  exact integral_sub hx.1 hx.2

end HRS.MS.R26T3
