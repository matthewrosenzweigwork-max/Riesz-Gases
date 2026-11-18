import HRS.MS.S21T4ProdO
import HRS.MS.S21G2_S11aC

/-! Finite Gaussian coordinate laws on the original common product-Gaussian probability space. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T3
open HRS HRS.Whole HRS.MS.R2Chaos
variable {d : ℕ} {μ : Measure (Euc d)} [IsProbabilityMeasure μ]

/-- The law of any finite family of the canonical Gaussian field is a centered
Gaussian law on the ORIGINAL product-Gaussian space. No existential
auxiliary Gaussian probability space is introduced here. -/
theorem s21t4_product_finite_gaussian_law (I : ProductGaussian μ) {n : ℕ}
    (f : Fin n → Euc d → ℝ) (hf : ∀ i, MemLp (f i) 2 μ) :
    HRS.IsCenteredGaussian
      (I.P.map (fun ω => fun i : Fin n => I.η (f i) ω)) := by
  letI := I.mΩ
  letI := I.prob
  have hη : S21LEta μ I.P I.η 1 := s21t4_product_eta_bundle I
  have hfm : S94GFam I.P (fun i ω => I.η (f i) ω) := s21l_gfam hη hf
  exact s21g2_s11a_gauss_of_laws
    (aemeasurable_pi_iff.mpr (fun i => hfm.meas i)) hfm.gauss

end HRS.MS.R26T3
