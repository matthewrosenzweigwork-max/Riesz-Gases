import HRS.MS.R2SeAux35

/-!
# S9.9 `r2_static_edgeworth`, packet 36: regularity and bounds of the response functions and potentials

Worker S99, namespace `S99`.  `s99_ua`: for each `i`, `u = a_i` is `C¹` with `|u| ≤ K b_i`, `‖Du‖ ≤ K b_i`; its potential
`G_i = c + γ⁻¹ (φ_i - a_i)` is `C¹`, bounded with bounded derivative, and `D G_i = γ⁻¹ (D φ_i - D a_i)`.
-/

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace ContDiff

noncomputable section

namespace S99

open S45
open HRS.Whole
open HRS (Euc cbNorm MemCb)

variable {d N : ℕ}

section Ua

variable (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) {a β γ : ℝ} (ha : 0 < a)
  (hβ : 0 < β) (hγ : 0 < γ) {C c BU : ℝ} (hT : ThermalData d s a β C c BU)
  {φ : ℕ → Euc d → ℝ} (hφ : IsSummableFeatureFamily (J1 d) φ) (F : FamData d s a β γ φ)

include hd hs0 hs ha hβ hγ hT hφ F

theorem s99_ua (i : ℕ) :
    ContDiff ℝ 1 (aRep d s a β γ (φ i)) ∧
    (∀ x, |aRep d s a β γ (φ i) x| ≤ F.K * cbNorm (J1 d) (φ i)) ∧
    (∀ x, ‖fderiv ℝ (aRep d s a β γ (φ i)) x‖ ≤ F.K * cbNorm (J1 d) (φ i)) ∧
    ContDiff ℝ 1 (Gpot d s a β (aRep d s a β γ (φ i))) ∧
    (∃ MG : ℝ, ∀ x, |Gpot d s a β (aRep d s a β γ (φ i)) x| ≤ MG) ∧
    (∃ DG : ℝ, ∀ x, ‖fderiv ℝ (Gpot d s a β (aRep d s a β γ (φ i))) x‖ ≤ DG) ∧
    (∀ x e, fderiv ℝ (Gpot d s a β (aRep d s a β γ (φ i))) x e =
      γ⁻¹ * (fderiv ℝ (φ i) x e - fderiv ℝ (aRep d s a β γ (φ i)) x e)) := by
  have hJ1 : 1 ≤ J1 d := by unfold J1; omega
  have hk0 : 1 ≤ k0 d := k0_ge_one d
  have hu1 : ContDiff ℝ 1 (aRep d s a β γ (φ i)) := (F.amem i).1.of_le (by exact_mod_cast hk0)
  have hub : ∀ x, |aRep d s a β γ (φ i) x| ≤ F.K * cbNorm (J1 d) (φ i) := fun x => by
    have h1 := s99_norm_iter_le_cb (F.amem i) (Nat.zero_le _) x
    rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at h1
    exact h1.trans (F.anorm i)
  have hdb : ∀ x, ‖fderiv ℝ (aRep d s a β γ (φ i)) x‖ ≤ F.K * cbNorm (J1 d) (φ i) := fun x =>
    (s45_cb_deriv_le hk0 (F.amem i) x).trans (F.anorm i)
  have hφ1 : ContDiff ℝ 1 (φ i) := (hφ.1 i).1.of_le (by exact_mod_cast hJ1)
  have hφb : ∀ x, |φ i x| ≤ cbNorm (J1 d) (φ i) := fun x => by
    have := HRS.MS.Tc5.tc5_cb_sup_le (hφ.1 i) x
    rwa [Real.norm_eq_abs] at this
  have hφdb : ∀ x, ‖fderiv ℝ (φ i) x‖ ≤ cbNorm (J1 d) (φ i) := fun x => s45_cb_deriv_le hJ1 (hφ.1 i) x
  obtain ⟨c0, hc0⟩ := s99_Gpot_eq hd hs0 hs ha hβ hγ hT hφ F i
  have hGe : Gpot d s a β (aRep d s a β γ (φ i)) = fun x => c0 + γ⁻¹ * (φ i x - aRep d s a β γ (φ i) x) :=
    funext hc0
  have hG1 : ContDiff ℝ 1 (Gpot d s a β (aRep d s a β γ (φ i))) := by
    rw [hGe]; exact contDiff_const.add (contDiff_const.mul (hφ1.sub hu1))
  have hder : ∀ x, HasFDerivAt (Gpot d s a β (aRep d s a β γ (φ i)))
      (γ⁻¹ • (fderiv ℝ (φ i) x - fderiv ℝ (aRep d s a β γ (φ i)) x)) x := fun x => by
    rw [hGe]
    exact (((hφ1.differentiable one_ne_zero x).hasFDerivAt.sub
      (hu1.differentiable one_ne_zero x).hasFDerivAt).const_mul γ⁻¹).const_add c0
  have hfd : ∀ x e, fderiv ℝ (Gpot d s a β (aRep d s a β γ (φ i))) x e =
      γ⁻¹ * (fderiv ℝ (φ i) x e - fderiv ℝ (aRep d s a β γ (φ i)) x e) := fun x e => by
    rw [(hder x).fderiv]; simp
  refine ⟨hu1, hub, hdb, hG1, ⟨|c0| + γ⁻¹ * (cbNorm (J1 d) (φ i) + F.K * cbNorm (J1 d) (φ i)), fun x => ?_⟩,
    ⟨γ⁻¹ * (cbNorm (J1 d) (φ i) + F.K * cbNorm (J1 d) (φ i)), fun x => ?_⟩, hfd⟩
  · rw [hc0 x]
    calc |c0 + γ⁻¹ * (φ i x - aRep d s a β γ (φ i) x)| ≤ |c0| + |γ⁻¹ * (φ i x - aRep d s a β γ (φ i) x)| :=
          abs_add_le _ _
      _ ≤ |c0| + γ⁻¹ * (cbNorm (J1 d) (φ i) + F.K * cbNorm (J1 d) (φ i)) := by
          refine add_le_add le_rfl ?_
          rw [abs_mul, abs_of_nonneg (inv_nonneg.2 hγ.le)]
          exact mul_le_mul_of_nonneg_left ((abs_sub _ _).trans (add_le_add (hφb x) (hub x)))
            (inv_nonneg.2 hγ.le)
  · refine ContinuousLinearMap.opNorm_le_bound _ (by
      have := HRS.MS.Tc5.tc5_cb_nonneg (d := d) (J1 d) (φ i); have := F.hK
      positivity) fun e => ?_
    rw [hfd x e, Real.norm_eq_abs, abs_mul, abs_of_nonneg (inv_nonneg.2 hγ.le)]
    have h1 : |fderiv ℝ (φ i) x e| ≤ cbNorm (J1 d) (φ i) * ‖e‖ := by
      rw [← Real.norm_eq_abs]; exact (ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul_of_nonneg_right (hφdb x) (norm_nonneg _))
    have h2 : |fderiv ℝ (aRep d s a β γ (φ i)) x e| ≤ F.K * cbNorm (J1 d) (φ i) * ‖e‖ := by
      rw [← Real.norm_eq_abs]; exact (ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul_of_nonneg_right (hdb x) (norm_nonneg _))
    calc γ⁻¹ * |fderiv ℝ (φ i) x e - fderiv ℝ (aRep d s a β γ (φ i)) x e|
        ≤ γ⁻¹ * (cbNorm (J1 d) (φ i) * ‖e‖ + F.K * cbNorm (J1 d) (φ i) * ‖e‖) :=
          mul_le_mul_of_nonneg_left ((abs_sub _ _).trans (add_le_add h1 h2)) (inv_nonneg.2 hγ.le)
      _ = γ⁻¹ * (cbNorm (J1 d) (φ i) + F.K * cbNorm (J1 d) (φ i)) * ‖e‖ := by ring

end Ua

end S99

end
