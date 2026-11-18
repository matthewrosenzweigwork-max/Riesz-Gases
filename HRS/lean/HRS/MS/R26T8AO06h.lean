import HRS.MS.R26T8AO06g

/-!
# S8.2 T8A O06 (part h): the Itô integrand and `correctorNoise` are the clipped `noiseAge` of O04
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators ContDiff
namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MH.DualityRd

variable {d N : ℕ}

theorem r26t8a_o06_configGrad_sub_const (F : EucConfig d N → ℝ) (c : ℝ) :
    Phase2S82.configGrad (fun X => F X - c) = Phase2S82.configGrad F := by
  funext X i
  unfold Phase2S82.configGrad gradient
  have : (fun y : Euc d => F (Function.update X i y) - c) = fun y => F (Function.update X i y) - c := rfl
  rw [fderiv_sub_const]

theorem r26t8a_o06_noise_apply (D : WholeDyn d) {F : EucConfig d N → ℝ} {X : EucConfig d N}
    (hF : DifferentiableAt ℝ F X) (i : Fin N) (j : Fin d) :
    fderiv ℝ F X (noiseDir D (i, j)) = Real.sqrt (2 * D.invβ) * Phase2S82.configGrad F X i j := by
  have hι : r26t8a_o03b_iota d N i (EuclideanSpace.single j (1 : ℝ)) =
      Pi.single i (EuclideanSpace.single j (1 : ℝ)) := by
    funext k
    by_cases hk : k = i
    · subst hk; simp [r26t8a_o03b_iota]
    · simp [r26t8a_o03b_iota, hk]
  unfold noiseDir
  rw [map_smul, ← hι, r26t8a_o04_cg_coord hF i j, smul_eq_mul]

end HRS.MS.R26T8A

end
