import HRS.MS.R26T8AV10a
import HRS.MS.S113X2A1a

/-!
# S8.2 T8A.V11a: the generator of a compactly supported collision-free smooth function is measurable and bounded

`LF = ν ∑_i Δ_i F + ∑_i ⟨b_i, ∇_i F⟩`.  The Laplacian part is `∑ D²F(e_ij, e_ij)`, continuous with compact support.  The
drift part vanishes off `tsupport F` and is continuous on the compact `tsupport F` (which lies off the collisions, where
`b_i` is continuous), hence bounded.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff
namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.PDE.ToolboxRd

theorem r26t8a_v11a_drift_contOn (d N : ℕ) (s a beta : ℝ) (i : Fin N) :
    ContinuousOn (fun X : EucConfig d N => particleDriftW (quadraticGradientDyn d s a beta) X i)
      (eucCollisionSet d N)ᶜ := by
  have hk : ContinuousOn (rieszKernelGrad d s) {z : Euc d | z ≠ 0} := by
    intro z hz
    have h1 : ContDiffAt ℝ ∞ (rieszKernel d s) z :=
      rieszKernel_contDiffOn.contDiffAt (isOpen_ne.mem_nhds hz)
    have h2 : ContinuousAt (fderiv ℝ (rieszKernel d s)) z :=
      (h1.fderiv_right (m := 0) (by simp)).continuousAt
    unfold rieszKernelGrad gradient
    exact ((InnerProductSpace.toDual ℝ (Euc d)).symm.continuous.continuousAt.comp h2).continuousWithinAt
  have hmv : Continuous (Torus.matVec (quadraticGradientDyn d s a beta).M) :=
    LinearMap.continuous_of_finiteDimensional
      (Matrix.toEuclideanLin (quadraticGradientDyn d s a beta).M)
  have hV : ContDiff ℝ ∞ (quadraticGradientDyn d s a beta).V := by
    show ContDiff ℝ ∞ (confinement a)
    unfold confinement
    exact (contDiff_const.mul (contDiff_norm_sq ℝ)).div_const _
  have hg : Continuous (gradient (quadraticGradientDyn d s a beta).V) := by
    unfold gradient
    exact (InnerProductSpace.toDual ℝ (Euc d)).symm.continuous.comp
      (hV.continuous_fderiv (by simp))
  unfold particleDriftW
  refine ContinuousOn.sub ((continuous_const_smul (1 / (N : ℝ))).comp_continuousOn ?_)
    (hg.comp (continuous_apply i)).continuousOn
  refine continuousOn_finsetSum _ fun j hj => ?_
  refine hmv.comp_continuousOn ?_
  refine hk.comp (((continuous_apply i).sub (continuous_apply j)).continuousOn) ?_
  intro X hX
  exact sub_ne_zero.2 fun h => hX ⟨i, j, (Finset.mem_erase.1 hj).1.symm, h⟩

theorem r26t8a_v11a_LF (d N : ℕ) (s a beta : ℝ) (F : EucConfig d N → ℝ) (hF : ContDiff ℝ ∞ F)
    (hFc : HasCompactSupport F) (hFs : tsupport F ⊆ (eucCollisionSet d N)ᶜ) :
    Measurable (particleGenerator (quadraticGradientDyn d s a beta) F) ∧
      ∃ C : ℝ, ∀ X, |particleGenerator (quadraticGradientDyn d s a beta) F X| ≤ C := by
  classical
  set D := quadraticGradientDyn d s a beta with hD
  have hF1 : ContDiff ℝ 1 F := hF.of_le (by simp)
  have hF2 : ContDiff ℝ 2 F := hF.of_le (by simp)
  have hF' : ∀ y, HasFDerivAt F (fderiv ℝ F y) y := fun y =>
    (hF1.differentiable one_ne_zero y).hasFDerivAt
  have hFF' : ContDiff ℝ 1 (fderiv ℝ F) := hF2.fderiv_right (by norm_num)
  have hFF2 : ∀ y, HasFDerivAt (fderiv ℝ F) (fderiv ℝ (fderiv ℝ F) y) y := fun y =>
    (hFF'.differentiable one_ne_zero y).hasFDerivAt
  -- Laplacian part
  let Lap : EucConfig d N → ℝ := fun X => ∑ i : Fin N, ∑ j : Fin d,
    fderiv ℝ (fderiv ℝ F) X (Pi.single i (EuclideanSpace.single j (1 : ℝ)))
      (Pi.single i (EuclideanSpace.single j (1 : ℝ)))
  have hLapc : Continuous Lap := by
    refine continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ => ?_
    exact ((hFF'.continuous_fderiv one_ne_zero).clm_apply continuous_const).clm_apply continuous_const
  have hLap0 : ∀ X, X ∉ tsupport F → Lap X = 0 := by
    intro X hX
    have h1 : fderiv ℝ F =ᶠ[𝓝 X] 0 := by
      have : (tsupport F)ᶜ ∈ 𝓝 X := (isClosed_tsupport F).isOpen_compl.mem_nhds hX
      filter_upwards [this] with y hy using fderiv_of_notMem_tsupport (𝕜 := ℝ) hy
    have h2 : fderiv ℝ (fderiv ℝ F) X = 0 := by
      rw [h1.fderiv_eq]; simp
    simp [Lap, h2]
  have hLapcs : HasCompactSupport Lap :=
    HasCompactSupport.intro hFc.isCompact (fun X hX => hLap0 X hX)
  obtain ⟨CL, hCL⟩ := hLapc.bounded_above_of_compact_support hLapcs
  -- drift part
  let T2 : EucConfig d N → ℝ := fun X => ∑ i, inner ℝ (particleDriftW D X i) (HRS.MS.Phase2S82.configGrad F X i)
  have hT20 : ∀ X, X ∉ tsupport F → T2 X = 0 := by
    intro X hX
    have h1 : ∀ i, HRS.MS.Phase2S82.configGrad F X i = 0 := by
      intro i
      rw [r26t8a_v10a_eq F hF1 X i, fderiv_of_notMem_tsupport (𝕜 := ℝ) hX]
      simp
    simp [T2, h1]
  have hT2c : ContinuousOn T2 (tsupport F) := by
    refine continuousOn_finset_sum _ fun i _ => ?_
    exact ((r26t8a_v11a_drift_contOn d N s a beta i).mono hFs).inner
      (r26t8a_v10a_cont F hF1 i).continuousOn
  obtain ⟨CT, hCT⟩ := hFc.isCompact.exists_bound_of_continuousOn hT2c
  have hGen : ∀ X, particleGenerator D F X = D.invβ * Lap X + T2 X := by
    intro X
    unfold particleGenerator
    congr 2
    refine Finset.sum_congr rfl fun i _ => ?_
    exact r26t8a_o05a1_lap F hF' X (hFF2 X) i
  have hDrift : Measurable (fun Y : EucConfig d N => particleDriftW D Y) :=
    HRS.MS.S113X2.s113a_measurable_drift d s a beta N
  refine ⟨?_, ⟨|D.invβ| * |CL| + |CT|, fun X => ?_⟩⟩
  · have : particleGenerator D F = fun X => D.invβ * Lap X + T2 X := funext hGen
    rw [this]
    refine (measurable_const.mul hLapc.measurable).add ?_
    exact Finset.measurable_sum _ fun i _ =>
      (((measurable_pi_apply i).comp hDrift)).inner (r26t8a_v10a_cont F hF1 i).measurable
  · rw [hGen]
    have h1 : |Lap X| ≤ |CL| := by
      exact (by simpa [Real.norm_eq_abs] using hCL X : |Lap X| ≤ CL).trans (le_abs_self _)
    have h2 : |T2 X| ≤ |CT| := by
      by_cases hX : X ∈ tsupport F
      · exact (by simpa [Real.norm_eq_abs] using hCT X hX : |T2 X| ≤ CT).trans (le_abs_self _)
      · rw [hT20 X hX]; simp
    calc |D.invβ * Lap X + T2 X| ≤ |D.invβ * Lap X| + |T2 X| := abs_add_le _ _
      _ ≤ |D.invβ| * |CL| + |CT| := by
          rw [abs_mul]; gcongr

end HRS.MS.R26T8A

end
