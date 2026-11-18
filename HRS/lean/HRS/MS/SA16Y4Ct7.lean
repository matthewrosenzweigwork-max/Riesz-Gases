import HRS.MS.SA16Y4Ct6

/-!
# S.A.16 (SA16Y4) Ct7: duality of the mollifier

`sa16y4_mol_dual`: `∫ (ρ_n ⋆ f) g = ∫ f (ρ_n ⋆ g)` for `f, g ∈ C_c^∞` (the mollifier is even).
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Q Phase2SA16Evolution Phase2SA16Transfer

section Ct7
variable {d : ℕ}

lemma sa16y4_rho_even (n : ℕ) (x : EuclideanSpace ℝ (Fin d)) : sa16y_rho d n (-x) = sa16y_rho d n x :=
  ContDiffBump.normed_neg (μ := volume) (sa16y_bumpn d n) x

theorem sa16y4_mol_dual (n : ℕ) {f g : EuclideanSpace ℝ (Fin d) → ℝ} (hf : IsCcInfty f) (hg : IsCcInfty g) :
    ∫ x, sa16q_mol n f x * g x = ∫ x, f x * sa16q_mol n g x := by
  have hρc : Continuous (sa16y_rho d n) := (sa16y_rho_smooth n).continuous
  set H : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) → ℝ :=
    fun q => f q.2 * sa16y_rho d n (q.1 - q.2) * g q.1 with hH
  have hHc : Continuous H := by
    refine ((hf.1.continuous.comp continuous_snd).mul (hρc.comp (continuous_fst.sub continuous_snd))).mul
      (hg.1.continuous.comp continuous_fst)
  have hHs : HasCompactSupport H := by
    refine HasCompactSupport.intro (K := tsupport g ×ˢ tsupport f) (hg.2.prod hf.2) ?_
    intro q hq
    have : q.1 ∉ tsupport g ∨ q.2 ∉ tsupport f := by
      by_contra h; push Not at h; exact hq ⟨h.1, h.2⟩
    rcases this with h | h
    · simp [hH, image_eq_zero_of_notMem_tsupport h]
    · simp [hH, image_eq_zero_of_notMem_tsupport h]
  have hHi : Integrable H (volume.prod volume) := hHc.integrable_of_hasCompactSupport hHs
  have e1 : ∫ x, sa16q_mol n f x * g x = ∫ x, ∫ y, H (x, y) := by
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    dsimp only
    rw [sa16q_mol_eq]
    dsimp only
    rw [← integral_mul_const]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp [hH, sa16q_rhoS_apply]
  have e2 : ∫ x, f x * sa16q_mol n g x = ∫ y, ∫ x, H (x, y) := by
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    dsimp only
    rw [sa16q_mol_eq]
    dsimp only
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    have : sa16y_rho d n (y - x) = sa16y_rho d n (x - y) := by
      rw [← neg_sub, sa16y4_rho_even]
    simp only [hH, sa16q_rhoS_apply, this]; ring
  rw [e1, e2]
  exact integral_integral_swap hHi
end Ct7

end HRS.Whole.AppendixA.Phase2SA16R
