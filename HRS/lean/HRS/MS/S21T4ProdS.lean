import HRS.MS.S21T4ProdR

/-! Finite-dimensional joint Gaussian covariance on the original product probability space. -/
set_option autoImplicit false
set_option maxHeartbeats 6400000
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T3
open HRS HRS.Whole HRS.MS.R2Chaos
variable {d : ℕ} {μ : Measure (Euc d)} [IsProbabilityMeasure μ]

/-- Exact bilinear covariance for a pair of finite Gaussian test families on
the common isonormal ProductGaussian space. This matches the covariance
prescribed by the finite-rank product CLT of R26-T3.S12. -/
theorem s21t4_product_joint_covariance (I : ProductGaussian μ) {n m : ℕ}
    (f : Fin n → Euc d → ℝ) (u : Fin m → Euc d → ℝ)
    (hf : ∀ i, MemLp (f i) 2 μ) (hu : ∀ j, MemLp (u j) 2 μ)
    (L M : ((Fin n → ℝ) × (Fin m → ℝ)) →L[ℝ] ℝ) :
    (∫ z, L z * M z ∂(I.P.map
      (fun ω => ((fun i => I.η (f i) ω), (fun j => I.η (u j) ω))))) =
      ∫ x, L ((fun i => HRS.Whole.projMean μ (f i) x),
                  (fun j => HRS.Whole.projMean μ (u j) x)) *
             M ((fun i => HRS.Whole.projMean μ (f i) x),
                  (fun j => HRS.Whole.projMean μ (u j) x)) ∂μ := by
  letI := I.mΩ
  letI := I.prob
  let g : Fin (n + m) → Euc d → ℝ := Fin.append f u
  have hg : ∀ k, MemLp (g k) 2 μ := by
    intro k
    refine Fin.addCases (fun i => ?_) (fun j => ?_) k
    · simpa [g] using hf i
    · simpa [g] using hu j
  let Z : I.Ω → Fin (n + m) → ℝ := fun ω k => I.η (g k) ω
  let T := s21g2_s12_Tv n m
  have hη : S21LEta μ I.P I.η 1 := s21t4_product_eta_bundle I
  have hSm : S94GFam I.P (fun k ω => I.η (g k) ω) := s21l_gfam hη hg
  have hZm : AEMeasurable Z I.P := aemeasurable_pi_iff.mpr (fun k => hSm.meas k)
  have hF : (T ∘ Z) =
      (fun ω : I.Ω => ((fun i => I.η (f i) ω), (fun j => I.η (u j) ω))) := by
    funext ω
    apply Prod.ext
    · funext i
      simp [T, Z, g, s21g2_s12_Tv_apply]
    · funext j
      simp [T, Z, g, s21g2_s12_Tv_apply]
  have hΨ : ∀ x : Euc d,
      T (fun k => HRS.Whole.projMean μ (g k) x) =
        ((fun i => HRS.Whole.projMean μ (f i) x),
         (fun j => HRS.Whole.projMean μ (u j) x)) := by
    intro x
    apply Prod.ext
    · funext i
      simp [T, g, s21g2_s12_Tv_apply]
    · funext j
      simp [T, g, s21g2_s12_Tv_apply]
  obtain ⟨α, hα⟩ := s21g2_s12_lin_expand L
  obtain ⟨β, hβ⟩ := s21g2_s12_lin_expand M
  calc
    _ = ∫ ω, L (T (Z ω)) * M (T (Z ω)) ∂I.P := by
      rw [← hF]
      exact integral_map
        (T.continuous.measurable.comp_aemeasurable hZm)
        (L.continuous.mul M.continuous).aestronglyMeasurable
    _ = ∫ ω, (∑ k, α k * I.η (g k) ω) *
                  (∑ k, β k * I.η (g k) ω) ∂I.P := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun ω => by
        have hL : L (T (Z ω)) = ∑ k, α k * I.η (g k) ω := hα (Z ω)
        have hM : M (T (Z ω)) = ∑ k, β k * I.η (g k) ω := hβ (Z ω)
        change L (T (Z ω)) * M (T (Z ω)) =
          (∑ k, α k * I.η (g k) ω) * (∑ k, β k * I.η (g k) ω)
        rw [hL, hM]
    _ = ∫ x, (∑ k, α k * HRS.Whole.projMean μ (g k) x) *
                 (∑ k, β k * HRS.Whole.projMean μ (g k) x) ∂μ :=
      s21t4_product_finite_covariance I g hg α β
    _ = _ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by
        have hL : L ((fun i => HRS.Whole.projMean μ (f i) x),
            (fun j => HRS.Whole.projMean μ (u j) x)) =
              ∑ k, α k * HRS.Whole.projMean μ (g k) x := by
          rw [← hΨ x]
          exact hα (fun k => HRS.Whole.projMean μ (g k) x)
        have hM : M ((fun i => HRS.Whole.projMean μ (f i) x),
            (fun j => HRS.Whole.projMean μ (u j) x)) =
              ∑ k, β k * HRS.Whole.projMean μ (g k) x := by
          rw [← hΨ x]
          exact hβ (fun k => HRS.Whole.projMean μ (g k) x)
        change (∑ k, α k * HRS.Whole.projMean μ (g k) x) *
          (∑ k, β k * HRS.Whole.projMean μ (g k) x) =
          L ((fun i => HRS.Whole.projMean μ (f i) x),
            (fun j => HRS.Whole.projMean μ (u j) x)) *
          M ((fun i => HRS.Whole.projMean μ (f i) x),
            (fun j => HRS.Whole.projMean μ (u j) x))
        rw [hL, hM]

end HRS.MS.R26T3
