import HRS.MS.S21T4ProdBE
import HRS.MS.S21T4ProdF

/-!
# R26-T3.S13: uniqueness of the common-space Wick limit

Two Wick-chaos limits of the same kernel, computed with the same orthonormal
test basis on the canonical ProductGaussian probability space, agree almost
everywhere. This identifies independently constructed scalar limits without
adding an axiom or imposing any additional regularity on the kernel.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.R26T3
open HRS HRS.Whole HRS.MS.R2Chaos

variable {d : ℕ} {μ : Measure (Euc d)} [IsProbabilityMeasure μ]

theorem s21t4_product_wick_ae_unique
    (I : ProductGaussian μ) (a : ℕ → Euc d → ℝ)
    (ha : IsR2ZeroMeanONB μ a) (k : Euc d → Euc d → ℝ)
    (Q Q' : I.Ω → ℝ)
    (hQ : IsR2WickChaos I.P μ a (fun i => I.η (a i)) k Q)
    (hQ' : IsR2WickChaos I.P μ a (fun i => I.η (a i)) k Q') :
    Q =ᵐ[I.P] Q' := by
  letI := I.mΩ
  letI := I.prob
  have hz : S94GSeq I.P (fun i ω => I.η (a i) ω) 1 :=
    s21l_gseq (s21t4_product_eta_bundle I) ha.1 ha.2.1
  have hm : ∀ n, AEStronglyMeasurable
      (s94Sec I.P (fun i ω => I.η (a i) ω)
        (fun i j => r2WickCoeff μ a k i j) n) I.P :=
    fun n => (s94_sec_memLp hz _ n).aestronglyMeasurable
  exact TendstoL2.ae_unique hm hQ hQ'

end HRS.MS.R26T3
