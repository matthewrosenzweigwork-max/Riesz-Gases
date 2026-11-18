import HRS.MS.R2ChaosAux20

/-!
# HRS.MS.R2ChaosAux21 -- convergence in law of the finite-rank (time-dependent coefficient) quadratic process

Packet S94, namespace `HRS.MS.R2Chaos`, helper prefix `s94_`.

Flat form: tests `ũ_1..ũ_n`, bounded measurable symmetric coefficients `C(t)`, kernel `h_t = ∑ C_ab(t) ũ_a ⊗ ũ_b`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false
set_option linter.style.haveILetI false
set_option linter.deprecated false

open MeasureTheory ProbabilityTheory Function Set Filter
open scoped ENNReal NNReal Topology

noncomputable section

namespace HRS.MS.R2Chaos

open HRS.Whole

variable {d : ℕ}

section L2Path

variable {T : ℝ}

theorem s94_r2L2Path_congr {f g : ℝ → ℝ} (h : ∀ t ∈ Set.Icc (0 : ℝ) T, f t = g t) :
    r2L2Path T f = r2L2Path T g := by
  have hae : f =ᵐ[volume.restrict (Set.Icc (0 : ℝ) T)] g :=
    (ae_restrict_iff' measurableSet_Icc).2 (ae_of_all _ h)
  by_cases hf : MemLp f 2 (volume.restrict (Set.Icc (0 : ℝ) T))
  · have hg : MemLp g 2 (volume.restrict (Set.Icc (0 : ℝ) T)) := (memLp_congr_ae hae).1 hf
    rw [s94_r2L2Path_eq hf, s94_r2L2Path_eq hg]
    exact MemLp.toLp_congr hf hg hae
  · have hg : ¬ MemLp g 2 (volume.restrict (Set.Icc (0 : ℝ) T)) := fun hg => hf ((memLp_congr_ae hae).2 hg)
    rw [s94_r2L2Path_eq_zero hf, s94_r2L2Path_eq_zero hg]

theorem s94_r2L2Path_sub {f g : ℝ → ℝ} (hf : MemLp f 2 (volume.restrict (Set.Icc (0 : ℝ) T)))
    (hg : MemLp g 2 (volume.restrict (Set.Icc (0 : ℝ) T))) :
    r2L2Path T f - r2L2Path T g = r2L2Path T (fun t => f t - g t) := by
  rw [s94_r2L2Path_eq hf, s94_r2L2Path_eq hg]
  exact (MemLp.toLp_sub hf hg).symm.trans (s94_r2L2Path_eq (hf.sub hg)).symm

theorem s94_norm_r2L2Path_sq {f : ℝ → ℝ} (hf : MemLp f 2 (volume.restrict (Set.Icc (0 : ℝ) T))) :
    ‖r2L2Path T f‖ ^ 2 = ∫ t, f t ^ 2 ∂(volume.restrict (Set.Icc (0 : ℝ) T)) := by
  rw [s94_r2L2Path_eq hf]
  show ‖(hf.toLp f : Lp ℝ 2 (volume.restrict (Set.Icc (0 : ℝ) T)))‖ ^ 2 = _
  rw [s94_Lp2_norm_sq]
  refine integral_congr_ae ?_
  filter_upwards [hf.coeFn_toLp] with t ht
  rw [ht]

end L2Path

end HRS.MS.R2Chaos
