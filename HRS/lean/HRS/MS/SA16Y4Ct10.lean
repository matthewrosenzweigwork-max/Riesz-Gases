import HRS.MS.SA16Y4Ct9

/-!
# S.A.16 (SA16Y4) Ct10: kernel formula for `R_n`

`sa16y4_R_kernel`: `(R_n Y)_κ =ᵐ ρ_n ⋆ Y_κ`.  Also the component helpers `sa16y4_comp`, `sa16y4_comp_memLp`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff Convolution

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Q Phase2SA16Evolution Phase2SA16Transfer

section Ct10
variable {d : ℕ} {p : ℝ} [Fact (2 ≤ p)]

/-- the `κ`-th component of an element of `WmpSpace` as a function -/
def sa16y4_comp (k : ℕ) (Y : WmpSpace d k p) (κ : WIndex d k) : EuclideanSpace ℝ (Fin d) → ℝ :=
  fun x => ((Y : WLp d k p) : EuclideanSpace ℝ (Fin d) → WIndex d k → ℝ) x κ

lemma sa16y4_comp_aesm (k : ℕ) (Y : WmpSpace d k p) (κ : WIndex d k) :
    AEStronglyMeasurable (sa16y4_comp k Y κ) volume :=
  (continuous_apply κ).comp_aestronglyMeasurable (Lp.aestronglyMeasurable (Y : WLp d k p))

lemma sa16y4_comp_memLp (k : ℕ) (Y : WmpSpace d k p) (κ : WIndex d k) :
    MemLp (sa16y4_comp k Y κ) (ENNReal.ofReal p) volume :=
  (Lp.memLp (Y : WLp d k p)).of_le (sa16y4_comp_aesm k Y κ)
    (Eventually.of_forall fun x => norm_le_pi_norm (((Y : WLp d k p) : EuclideanSpace ℝ (Fin d) → WIndex d k → ℝ) x) κ)

lemma sa16y4_comp_ellK (k : ℕ) (Y : WmpSpace d k p) (κ : WIndex d k) {N : EuclideanSpace ℝ (Fin d) → ℝ}
    (hN : IsCcInfty N) : sa16y4_ellK k κ hN Y = ∫ x, sa16y4_comp k Y κ x * N x :=
  sa16y4_ellK_apply k κ hN Y

theorem sa16y4_R_kernel (k n : ℕ) (R : WmpSpace d k p →L[ℝ] WmpSpace d k p)
    (hR : ∀ ψ : ccSub d, R (sa16r_Jcc d k p ψ) = sa16r_Jcc d k p ⟨sa16q_mol n ψ.1, sa16y4_mol_cc ψ.2 n⟩)
    (κ : WIndex d k) (Y : WmpSpace d k p) :
    sa16y4_comp k (R Y) κ =ᵐ[volume] sa16q_mol n (sa16y4_comp k Y κ) := by
  have hp1 : 1 ≤ ENNReal.ofReal p := ENNReal.one_le_ofReal.2 (le_trans one_le_two (Fact.out : 2 ≤ p))
  have hfl : LocallyIntegrable (sa16y4_comp k Y κ) volume := (sa16y4_comp_memLp k Y κ).locallyIntegrable hp1
  have hρ : Continuous (sa16y_rho d n) := (sa16y_rho_smooth n).continuous
  have hmol : sa16q_mol n (sa16y4_comp k Y κ) = (sa16y4_comp k Y κ) ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] (sa16y_rho d n) := by
    rw [sa16q_mol_eq]; funext x; rfl
  have hcont : Continuous (sa16q_mol n (sa16y4_comp k Y κ)) := by
    rw [hmol]
    exact (sa16y_rho_compact (d := d) n).continuous_convolution_right (ContinuousLinearMap.mul ℝ ℝ) hfl hρ
  refine ae_eq_of_integral_contDiff_smul_eq ((sa16y4_comp_memLp k (R Y) κ).locallyIntegrable hp1)
    hcont.locallyIntegrable (fun g hg hgc => ?_)
  have hgcc : IsCcInfty g := ⟨hg, hgc⟩
  have h1 := sa16y4_R_pair k n R hR κ hgcc Y
  rw [sa16y4_comp_ellK, sa16y4_comp_ellK] at h1
  simp only [smul_eq_mul]
  calc ∫ x, g x * sa16y4_comp k (R Y) κ x = ∫ x, sa16y4_comp k (R Y) κ x * g x := by simp_rw [mul_comm]
    _ = ∫ x, sa16y4_comp k Y κ x * sa16q_mol n g x := h1
    _ = ∫ x, sa16q_mol n (sa16y4_comp k Y κ) x * g x := (sa16y4_mol_dual_loc n hfl hgcc).symm
    _ = _ := by simp_rw [mul_comm]

end Ct10

end HRS.Whole.AppendixA.Phase2SA16R
