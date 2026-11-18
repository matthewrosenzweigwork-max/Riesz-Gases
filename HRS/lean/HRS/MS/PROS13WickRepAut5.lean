import HRS.MS.PROS13FamilyUnshiftedAut5
import HRS.MS.S21L_G11

/-!
# S13: measurable symmetric representatives of arbitrary product-L² kernels

The representative preserves both symmetry and the product-measure
almost-everywhere class. It is constructed on the same probability law
without any nonatomicity, density, or row-integrability hypothesis.
-/
set_option autoImplicit false
set_option maxHeartbeats 6400000
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T3
open HRS HRS.Whole HRS.MS.R2Chaos
variable {d : ℕ} {μ : Measure (Euc d)} [IsProbabilityMeasure μ]

theorem pro_s13_symmetric_measurable_representative
    (h : Euc d → Euc d → ℝ)
    (hh : MemLp (fun z : Euc d × Euc d => h z.1 z.2) 2 (μ.prod μ))
    (hs : ∀ x y, h x y = h y x) :
    ∃ K : Euc d → Euc d → ℝ,
      Measurable (fun z : Euc d × Euc d => K z.1 z.2) ∧
      (∀ x y, K x y = K y x) ∧
      MemLp (fun z : Euc d × Euc d => K z.1 z.2) 2 (μ.prod μ) ∧
      (fun z : Euc d × Euc d => K z.1 z.2) =ᵐ[μ.prod μ]
        (fun z => h z.1 z.2) := by
  classical
  have hm := hh.aestronglyMeasurable
  let G : Euc d × Euc d → ℝ :=
    hm.mk (fun z : Euc d × Euc d => h z.1 z.2)
  have hGm : Measurable G := hm.stronglyMeasurable_mk.measurable
  have e1 : (fun z : Euc d × Euc d => h z.1 z.2) =ᵐ[μ.prod μ] G :=
    hm.ae_eq_mk
  let K : Euc d → Euc d → ℝ :=
    fun x y => (1 / 2 : ℝ) * (G (x, y) + G (y, x))
  have hKm : Measurable (fun z : Euc d × Euc d => K z.1 z.2) :=
    (hGm.add (hGm.comp measurable_swap)).const_mul _
  have hKs : ∀ x y, K x y = K y x := by
    intro x y
    simp only [K, add_comm]
  have e2 : (fun z : Euc d × Euc d => h z.2 z.1) =ᵐ[μ.prod μ]
      (fun z => G (z.2, z.1)) :=
    (Measure.measurePreserving_swap (μ := μ) (ν := μ)).quasiMeasurePreserving.ae_eq_comp e1
  have hKH : (fun z : Euc d × Euc d => K z.1 z.2) =ᵐ[μ.prod μ]
      (fun z => h z.1 z.2) := by
    filter_upwards [e1, e2] with z h1 h2
    simp only [K]
    rw [← h1, ← h2, hs z.2 z.1]
    ring
  exact ⟨K, hKm, hKs, hh.ae_eq hKH.symm, hKH⟩

#print axioms pro_s13_symmetric_measurable_representative
end HRS.MS.R26T3
