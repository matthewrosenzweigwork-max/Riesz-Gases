import HRS.MS.PROS13GenericTransferD
import HRS.MS.S21G2_S11

/-!
# Integrability of the actual pair energy at every particle number

For any Borel probability measure and any product-L² pair kernel, the
*original*, not merely modified, pairEnergy is an L² random variable under
an iid sample of arbitrary size, even N = 0 or 1. This uses the deleted
pair diagonal and the L² integrability of both particle-pair and row terms.
-/
set_option autoImplicit false
set_option maxHeartbeats 6400000
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T3
open HRS HRS.Whole HRS.MS.R2Chaos
variable {d : ℕ} {μ : Measure (Euc d)} [IsProbabilityMeasure μ]

theorem pro_s13_generic_pairEnergy_memLp
    {N : ℕ} (h : Euc d → Euc d → ℝ)
    (hh : MemLp (fun z : Euc d × Euc d => h z.1 z.2) 2 (μ.prod μ)) :
    MemLp (fun X : EucConfig d N => pairEnergy h X μ)
      2 (Measure.pi fun _ : Fin N => μ) := by
  let ν : Measure (EucConfig d N) := Measure.pi fun _ : Fin N => μ
  have hpair : ∀ i j : Fin N, j ∈ Finset.univ.erase i →
      MemLp (fun X : EucConfig d N => h (X i) (X j)) 2 ν := by
    intro i j hj
    exact s21g2_s11_memLp μ h hh (Finset.ne_of_mem_erase hj).symm
  have hsum : MemLp
      (fun X : EucConfig d N =>
        ∑ i : Fin N, ∑ j ∈ Finset.univ.erase i, h (X i) (X j)) 2 ν :=
    memLp_finsetSum _ fun i _ => memLp_finsetSum _ fun j hj => hpair i j hj
  have hm : MemLp (fun x => ∫ y, h x y ∂μ) 2 μ :=
    s21h2_m_memLp μ hh
  have hrow : ∀ i : Fin N, MemLp
      (fun X : EucConfig d N => ∫ y, h (X i) y ∂μ) 2 ν := by
    intro i
    have hi := hm.comp_measurePreserving
      (measurePreserving_eval (fun _ : Fin N => μ) i)
    simpa [Function.comp_def] using hi
  have hrowsum : MemLp
      (fun X : EucConfig d N => ∑ i : Fin N, ∫ y, h (X i) y ∂μ) 2 ν :=
    memLp_finsetSum _ fun i _ => hrow i
  have hresult :=
    ((hsum.const_mul (1 / (2 * (N : ℝ) ^ 2))).sub
      (hrowsum.const_mul (1 / (N : ℝ)))).add
      (memLp_const ((1 / 2 : ℝ) * ∫ x, ∫ y, h x y ∂μ ∂μ))
  convert hresult using 1
  funext X
  rfl

end HRS.MS.R26T3
