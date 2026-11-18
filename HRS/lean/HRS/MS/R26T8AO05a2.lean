import HRS.MS.R26T8AO05a1

/-!
# S8.2 observed-time layer, packet T8A.O05a (helper 2): Itô drift terms in particle coordinates

With `noiseDir D (i,j) = √(2ν) e_{ij}`: `D F x (noiseDir D (i,j)) = √(2ν) (HRS.MS.Phase2S82.configGrad F x i)_j`,
`D F x (particleDriftW D x) = ∑_i ⟪particleDriftW D x i, HRS.MS.Phase2S82.configGrad F x i⟫`, and
`½ ∑_k D²F x (σ_k)(σ_k) = ν ∑_i Δ_i F(x)`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.PDE.ToolboxRd HRS.MH.DualityRd

theorem r26t8a_o05a2_single {d N : ℕ} (F : EucConfig d N → ℝ)
    (hF : ∀ y, HasFDerivAt F (fderiv ℝ F y) y) (x : EucConfig d N) (i : Fin N) (v : Euc d) :
    fderiv ℝ F x (Pi.single i v) = inner ℝ (HRS.MS.Phase2S82.configGrad F x i) v := by
  have h := r26t8a_o05a1_fderiv_update F hF x i (x i)
  have h2 : fderiv ℝ (fun z => F (Function.update x i z)) (x i) v = fderiv ℝ F x (Pi.single i v) := by
    rw [h]
    simp only [Function.update_eq_self, ContinuousLinearMap.comp_apply]
    congr 1
    funext k
    by_cases hk : k = i
    · subst hk; simp
    · simp [Pi.single_apply, hk]
  rw [← h2, da2_fderiv_eq_inner]
  rfl

theorem r26t8a_o05a2_noise {d N : ℕ} (D : WholeDyn d) (F : EucConfig d N → ℝ)
    (hF : ∀ y, HasFDerivAt F (fderiv ℝ F y) y) (x : EucConfig d N) (i : Fin N) (j : Fin d) :
    fderiv ℝ F x (noiseDir D (i, j)) = Real.sqrt (2 * D.invβ) * HRS.MS.Phase2S82.configGrad F x i j := by
  unfold noiseDir
  rw [map_smul, r26t8a_o05a2_single F hF, smul_eq_mul]
  congr 1
  simp [EuclideanSpace.inner_single_right]

theorem r26t8a_o05a2_drift {d N : ℕ} (D : WholeDyn d) (F : EucConfig d N → ℝ)
    (hF : ∀ y, HasFDerivAt F (fderiv ℝ F y) y) (x : EucConfig d N) :
    fderiv ℝ F x (particleDriftW D x) = ∑ i, inner ℝ (particleDriftW D x i) (HRS.MS.Phase2S82.configGrad F x i) := by
  have : particleDriftW D x = ∑ i, Pi.single i (particleDriftW D x i) :=
    (Finset.univ_sum_single (particleDriftW D x)).symm
  conv_lhs => rw [this]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [r26t8a_o05a2_single F hF, real_inner_comm]

theorem r26t8a_o05a2_hess {d N : ℕ} (D : WholeDyn d) (hnu : 0 ≤ D.invβ) (F : EucConfig d N → ℝ)
    (hF : ∀ y, HasFDerivAt F (fderiv ℝ F y) y) (x : EucConfig d N)
    (hF2 : HasFDerivAt (fderiv ℝ F) (fderiv ℝ (fderiv ℝ F) x) x) :
    (1 / 2) * ∑ k : Fin N × Fin d, fderiv ℝ (fderiv ℝ F) x (noiseDir D k) (noiseDir D k) =
      D.invβ * ∑ i, Laplacian.laplacian (fun y => F (Function.update x i y)) (x i) := by
  have hsq : Real.sqrt (2 * D.invβ) * Real.sqrt (2 * D.invβ) = 2 * D.invβ :=
    Real.mul_self_sqrt (by linarith)
  have hk : ∀ k : Fin N × Fin d, fderiv ℝ (fderiv ℝ F) x (noiseDir D k) (noiseDir D k) =
      (2 * D.invβ) * fderiv ℝ (fderiv ℝ F) x (Pi.single k.1 (EuclideanSpace.single k.2 (1 : ℝ)))
        (Pi.single k.1 (EuclideanSpace.single k.2 (1 : ℝ))) := by
    intro k
    unfold noiseDir
    simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
    linear_combination (fderiv ℝ (fderiv ℝ F) x (Pi.single k.1 (EuclideanSpace.single k.2 (1 : ℝ)))
      (Pi.single k.1 (EuclideanSpace.single k.2 (1 : ℝ)))) * hsq
  simp only [hk]
  rw [← Finset.mul_sum, Fintype.sum_prod_type]
  simp only [r26t8a_o05a1_lap F hF x hF2]
  ring

end HRS.MS.R26T8A

end
