import HRS.MS.S21T4ProdBL
import HRS.MS.S21T4ProdAZ

/-!
# R26-T3.S13: finite-family linearity of the physical centered Wick chaos

For any finite family of symmetric kernels in the integrable L²-domain, the
Wick chaos of their combined doubly centered kernel agrees almost everywhere
on the original ProductGaussian space with the corresponding linear combination.
This applies to singular Riesz kernels in the Hilbert-Schmidt regime.
-/

set_option autoImplicit false
set_option maxHeartbeats 6400000
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.R26T3
open HRS HRS.Whole HRS.MS.R2Chaos

variable {d : ℕ} {μ : Measure (Euc d)} [IsProbabilityMeasure μ]

theorem s21t4_product_centered_wick_family_linear
    (I : ProductGaussian μ) (a : ℕ → Euc d → ℝ)
    (ha : IsR2ZeroMeanONB μ a) {m : ℕ}
    (h : Fin m → Euc d → Euc d → ℝ)
    (hh : ∀ k, S94KOK μ (h k)) (α : Fin m → ℝ)
    (Q : Fin m → I.Ω → ℝ)
    (hQ : ∀ k, IsR2WickChaos I.P μ a (fun i => I.η (a i))
      (r2CenterKernel μ (h k)) (Q k))
    (R : I.Ω → ℝ)
    (hR : IsR2WickChaos I.P μ a (fun i => I.η (a i))
      (r2CenterKernel μ (fun x y => ∑ k, α k * h k x y)) R) :
    R =ᵐ[I.P] (fun ω => ∑ k : Fin m, α k * Q k ω) := by
  have hki : ∀ k, Integrable
      (fun z : Euc d × Euc d => h k z.1 z.2) (μ.prod μ) :=
    fun k => (hh k).memLp.integrable (by norm_num)
  have hcomb := s21t4_kernel_family_KOK h hh α
  have hci : Integrable
      (fun z : Euc d × Euc d => ∑ k : Fin m, α k * h k z.1 z.2) (μ.prod μ) :=
    hcomb.memLp.integrable (by norm_num)
  have hQ' : ∀ k, IsR2WickChaos I.P μ a (fun i => I.η (a i))
      (h k) (Q k) :=
    fun k => (s21t4_wick_center_iff I a ha.1 (h k) (hki k) (Q k)).mp (hQ k)
  have hR' : IsR2WickChaos I.P μ a (fun i => I.η (a i))
      (fun x y => ∑ k : Fin m, α k * h k x y) R :=
    (s21t4_wick_center_iff I a ha.1 _ hci R).mp hR
  exact s21t4_product_wick_family_linear I a ha h hh α Q hQ' R hR'

end HRS.MS.R26T3
