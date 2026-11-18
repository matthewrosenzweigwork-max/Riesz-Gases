import HRS.MS.SA16Y4Ct10

/-!
# S.A.16 (SA16Y4) Ct11: pointwise values and uniform bound of `ρ_n ⋆ Y_κ`

`sa16y4_rhox n x = ρ_n(x - ·) ∈ C_c^∞`; `sa16y4_mol_comp_eq`: `(ρ_n ⋆ Y_κ)(x) = ℓ_κ(ρ_x) Y`;
`sa16y4_mol_comp_bound`: `|(ρ_n ⋆ Y_κ)(x)| ≤ C ‖Y‖` with `C` independent of `x`, `Y`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff Convolution

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Q Phase2SA16Evolution Phase2SA16Transfer

section Ct11
variable {d : ℕ} {p : ℝ} [Fact (2 ≤ p)]

def sa16y4_rhox (d n : ℕ) (x : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) → ℝ :=
  fun y => sa16y_rho d n (x - y)

lemma sa16y4_rhox_cc (n : ℕ) (x : EuclideanSpace ℝ (Fin d)) : IsCcInfty (sa16y4_rhox d n x) :=
  ⟨(sa16y_rho_smooth n).comp (contDiff_const.sub contDiff_id),
    (sa16y_rho_compact (d := d) n).comp_homeomorph (Homeomorph.subLeft x)⟩

lemma sa16y4_mol_comp_eq (k n : ℕ) (Y : WmpSpace d k p) (κ : WIndex d k) (x : EuclideanSpace ℝ (Fin d)) :
    sa16q_mol n (sa16y4_comp k Y κ) x = sa16y4_ellK k κ (sa16y4_rhox_cc n x) Y := by
  rw [sa16y4_comp_ellK, sa16q_mol_eq]
  simp only [sa16q_rhoS_apply, sa16y4_rhox]

lemma sa16y4_mol_comp_bound (k n : ℕ) (κ : WIndex d k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (Y : WmpSpace d k p) (x : EuclideanSpace ℝ (Fin d)),
      |sa16q_mol n (sa16y4_comp k Y κ) x| ≤ C * ‖Y‖ := by
  set q := ENNReal.conjExponent (ENNReal.ofReal p) with hq
  set A : WLp d k p →L[ℝ] Lp ℝ q (volume : Measure (EuclideanSpace ℝ (Fin d))) →L[ℝ] ℝ :=
    ((ContinuousLinearMap.mul ℝ ℝ).comp
      (ContinuousLinearMap.proj κ : (WIndex d k → ℝ) →L[ℝ] ℝ)).lpPairing
      (volume : Measure (EuclideanSpace ℝ (Fin d))) (ENNReal.ofReal p) q with hA
  refine ⟨‖A.flip‖ * (eLpNorm (sa16y_rho d n) q volume).toReal, by positivity, fun Y x => ?_⟩
  rw [sa16y4_mol_comp_eq, sa16y4_ellK]
  set hc := (sa16y4_rhox_cc (d := d) n x)
  have hmem := hc.1.continuous.memLp_of_hasCompactSupport (p := q) (μ := (volume : Measure (EuclideanSpace ℝ (Fin d)))) hc.2
  have h1 : (sa16s_pair d k p κ hc.1.continuous hc.2) = A.flip (hmem.toLp _) := rfl
  have hnorm : ‖hmem.toLp (sa16y4_rhox d n x)‖ = (eLpNorm (sa16y_rho d n) q volume).toReal := by
    rw [Lp.norm_toLp]
    congr 1
    have := eLpNorm_comp_measurePreserving (p := q) (μ := (volume : Measure (EuclideanSpace ℝ (Fin d))))
      (g := sa16y_rho d n) (sa16y_rho_smooth (d := d) n).continuous.aestronglyMeasurable
      (Measure.measurePreserving_sub_left (volume : Measure (EuclideanSpace ℝ (Fin d))) x)
    exact this
  rw [← Real.norm_eq_abs, ContinuousLinearMap.comp_apply, h1]
  calc ‖(A.flip (hmem.toLp _)) ((Y : WLp d k p))‖
      ≤ ‖A.flip (hmem.toLp _)‖ * ‖(Y : WLp d k p)‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ (‖A.flip‖ * ‖hmem.toLp (sa16y4_rhox d n x)‖) * ‖Y‖ := by
        have e : ‖(Y : WLp d k p)‖ = ‖Y‖ := rfl
        rw [e]
        gcongr
        exact ContinuousLinearMap.le_opNorm _ _
    _ = _ := by rw [hnorm]
end Ct11

end HRS.Whole.AppendixA.Phase2SA16R
