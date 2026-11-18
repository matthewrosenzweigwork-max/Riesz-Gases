import HRS.MS.R26T8AO06h

/-!
# S8.2 T8A O06 (part i): identification of the Itô integrand and of `correctorNoise` with the clipped `noiseAge`
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators ContDiff
namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MH.DualityRd

set_option maxHeartbeats 6400000 in
theorem r26t8a_o06_Phi_eq (d N : ℕ) (hd : 2 ≤ d) (a beta m M C Cf c : ℝ) (hC : 0 ≤ C)
    (rho : Euc d → ℝ) (Psi : (Euc d → ℝ) → Euc d → Euc d → ℝ)
    (hPsi : r26t8a_NormalFormFamily d a beta M C rho Psi)
    (horb : r26t8a_FeatureOrbits d a beta m Cf c rho) (alpha : MultiIndex d) (b : ℝ)
    {Omega : Type*} (X : ℝ≥0 → Omega → EucConfig d N) :
    itoIntegrand b (eucCollisionSet d N)ᶜ (fun r => r26t8a_QAge (N := N) a beta m rho Psi alpha 0 (b - r))
        (ofNNRealTime X) (fun _ _ => noiseDir (N := N) (quadraticGradientDyn d (criticalS d) a beta)) =
      r26t8a_clipIntegrand 0 b (r26t8a_noiseAge a beta m rho Psi alpha X 0 b) := by
  classical
  funext s w k
  rw [r26t8a_o06_itoIntegrand_apply]
  unfold r26t8a_clipIntegrand r26t8a_noiseAge
  by_cases hs : s ∈ Set.Icc (0 : ℝ) b
  · by_cases hx : X s.toNNReal w ∈ eucCollisionSet d N
    · have h1 : ¬ (s ∈ Set.Icc (0 : ℝ) b ∧ ofNNRealTime X s w ∈ (eucCollisionSet d N)ᶜ) := fun h => h.2 hx
      rw [if_neg h1, if_pos hs, if_neg (fun h => h.2.2 hx)]
    · have hxU : ofNNRealTime X s w ∈ (eucCollisionSet d N)ᶜ := hx
      rw [if_pos ⟨hs, hxU⟩, if_pos hs, if_pos ⟨hs.1, hs.2, hx⟩]
      obtain ⟨A, hA⟩ : ∃ A, TestBound (testOrder d) A (r26t8a_ageTest a beta m rho alpha 0 (b - s)) :=
        ⟨_, horb.bound alpha (b - s) (sub_nonneg.2 hs.2) 0 (by norm_num)⟩
      have hdiff : DifferentiableAt ℝ (r26t8a_QAge (N := N) a beta m rho Psi alpha 0 (b - s)) (X s.toNNReal w) :=
        (r26t8a_o03b_Q_contDiffAt N hd a beta M C hC rho Psi hPsi hA hx).differentiableAt (by norm_num)
      have := r26t8a_o06_noise_apply (quadraticGradientDyn d (criticalS d) a beta) hdiff k.1 k.2
      simp only [Prod.mk.eta] at this
      rw [show ofNNRealTime X s w = X s.toNNReal w from rfl, this]
      have e : (quadraticGradientDyn d (criticalS d) a beta).invβ = beta⁻¹ := rfl
      rw [e, show 2 * beta⁻¹ = 2 / beta by rw [div_eq_mul_inv]]
  · rw [if_neg (fun h => hs h.1), if_neg hs]

set_option maxHeartbeats 6400000 in
theorem r26t8a_o06_corrNoise_eq (d N : ℕ) (hd : 2 ≤ d) (a beta m M C Cf c : ℝ)
    (rho : Euc d → ℝ) (Psi : (Euc d → ℝ) → Euc d → Euc d → ℝ)
    (hPsi : r26t8a_NormalFormFamily d a beta M C rho Psi)
    (horb : r26t8a_FeatureOrbits d a beta m Cf c rho) (alpha : MultiIndex d) (b : ℝ)
    {Omega : Type*} (X : ℝ≥0 → Omega → EucConfig d N) :
    r26t8a_correctorNoise a beta m b rho Psi alpha X =
      r26t8a_clipIntegrand 0 b (r26t8a_noiseAge a beta m rho Psi alpha X 0 b) := by
  classical
  funext s w k
  unfold r26t8a_correctorNoise r26t8a_clipIntegrand r26t8a_noiseAge
  by_cases hs : s ∈ Set.Icc (0 : ℝ) b
  · rw [if_pos hs]
    by_cases hx : X s.toNNReal w ∈ eucCollisionSet d N
    · rw [if_neg (fun h => h.2 hx), if_neg (fun h => h.2.2 hx)]
    · rw [if_pos ⟨hs, hx⟩, if_pos ⟨hs.1, hs.2, hx⟩]
      have hq := (r26t8a_o06_prop_conv d N a beta m M C Cf c rho Psi hPsi horb alpha s b hs.1 hs.2).1
      have e : Phase2S82.configGrad (r26t8a_QAge (N := N) a beta m rho Psi alpha 0 (b - s)) =
          Phase2S82.configGrad (Phase2S82.pairStatistic
            (Psi (propagatorW (critCoeff d a beta rho) s b (oscTestFun m alpha)))) := by
        rw [← hq]
        exact r26t8a_o06_configGrad_sub_const _ _
      rw [e]
  · rw [if_neg (fun h => hs h.1), if_neg hs]

end HRS.MS.R26T8A

end
