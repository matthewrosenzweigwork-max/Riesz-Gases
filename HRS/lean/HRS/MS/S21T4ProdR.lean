import HRS.MS.S21T4ProdQ
import HRS.MS.S21G2_S12F

/-! Finite joint Gaussian laws on the ORIGINAL common product-Gaussian space. -/
set_option autoImplicit false
set_option maxHeartbeats 6400000
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T3
open HRS HRS.Whole HRS.MS.R2Chaos
variable {d : ℕ} {μ : Measure (Euc d)} [IsProbabilityMeasure μ]

theorem s21t4_product_joint_gaussian_law (I : ProductGaussian μ) {n m : ℕ}
    (f : Fin n → Euc d → ℝ) (u : Fin m → Euc d → ℝ)
    (hf : ∀ i, MemLp (f i) 2 μ) (hu : ∀ j, MemLp (u j) 2 μ) :
    HRS.IsCenteredGaussian
      (I.P.map (fun ω => ((fun i => I.η (f i) ω), (fun j => I.η (u j) ω)))) := by
  letI := I.mΩ
  letI := I.prob
  let g : Fin (n + m) → Euc d → ℝ := Fin.append f u
  have hg : ∀ k, MemLp (g k) 2 μ := by
    intro k
    refine Fin.addCases (fun i => ?_) (fun j => ?_) k
    · simpa [g] using hf i
    · simpa [g] using hu j
  let Z : I.Ω → Fin (n + m) → ℝ := fun ω k => I.η (g k) ω
  have hG : HRS.IsCenteredGaussian (I.P.map Z) :=
    s21t4_product_finite_gaussian_law I g hg
  let T := s21g2_s12_Tv n m
  have hη : S21LEta μ I.P I.η 1 := s21t4_product_eta_bundle I
  have hSm : S94GFam I.P (fun k ω => I.η (g k) ω) := s21l_gfam hη hg
  have hZm : AEMeasurable Z I.P :=
    aemeasurable_pi_iff.mpr (fun k => hSm.meas k)
  have hmap : (I.P.map Z).map T = I.P.map (T ∘ Z) :=
    AEMeasurable.map_map_of_aemeasurable T.continuous.measurable.aemeasurable hZm
  have heq : (T ∘ Z) =
      (fun ω : I.Ω => ((fun i => I.η (f i) ω), (fun j => I.η (u j) ω))) := by
    funext ω
    apply Prod.ext
    · funext i
      simp [T, Z, g, s21g2_s12_Tv_apply]
    · funext j
      simp [T, Z, g, s21g2_s12_Tv_apply]
  rw [← heq, ← hmap]
  exact s21g2_s12_cg_map hG T

end HRS.MS.R26T3
