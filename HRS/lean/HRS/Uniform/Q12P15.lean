import HRS.Uniform.Q12P14

/-!
# Q12, Peyre part 15: `W_2(g, f) ≤ π (E_u / m)^{1/2}` for the Moser data
-/

noncomputable section

open HRS MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators Real

namespace HRS.Uniform.Q12

variable {d : ℕ}

namespace PeyreData

variable (D : PeyreData d)

/-- The Dirichlet energy `∫ |∇u|²`. -/
def energy : ℝ := ∫ x : Torus d, ‖D.gradU (Torus.rep x)‖ ^ 2

lemma continuous_gradU_rep : Continuous fun x : Torus d => D.gradU (Torus.rep x) :=
  Torus.continuous_descend D.per_gradU D.contDiff_gradU.continuous

lemma energy_nonneg : 0 ≤ D.energy := integral_nonneg fun x => sq_nonneg _

/-- The kinetic energy bound along the path. -/
lemma kinetic (t : ℝ) :
    ∫ x : Torus d, ‖D.vf t (Torus.rep x)‖ ^ 2 ∂(D.muT t) ≤ π ^ 2 * D.energy / D.m := by
  obtain ⟨c₀, hc₀, -, hlow⟩ := D.exists_rho_lower
  rw [D.integral_muT]
  have hvc : Continuous fun x : Torus d => D.vf t (Torus.rep x) :=
    Torus.continuous_descend (D.per_vf t) (by
      have h := ContDiff.comp (g := fun p : ℝ × Euc d => D.vf p.1 p.2) (f := fun y : Euc d => (t, y))
        D.contDiff_vf_joint (contDiff_const.prodMk contDiff_id)
      exact h.continuous)
  have hgc := D.continuous_gradU_rep
  have hpt : ∀ x : Torus d, D.rhoT t x * ‖D.vf t (Torus.rep x)‖ ^ 2 ≤
      π ^ 2 / D.m * ‖D.gradU (Torus.rep x)‖ ^ 2 := by
    intro x
    have hr : D.rho t (Torus.rep x) = D.rhoT t x := D.rho_rep t x
    have hpos : 0 < D.rhoT t x := lt_of_lt_of_le hc₀ (hlow t x)
    obtain ⟨h0, h1⟩ := theta_mem t
    have hlow2 : (1 - theta t) * D.m ≤ D.rhoT t x := by
      unfold rhoT
      have := D.hgm x
      nlinarith [mul_le_mul_of_nonneg_left this (sub_nonneg.2 h1), mul_nonneg h0 (D.hf.nonneg x)]
    unfold PeyreData.vf
    rw [hr, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    have hm := D.hm
    have e : D.rhoT t x * ((theta' t / D.rhoT t x) ^ 2 * ‖D.gradU (Torus.rep x)‖ ^ 2) =
        theta' t ^ 2 / D.rhoT t x * ‖D.gradU (Torus.rep x)‖ ^ 2 := by
      field_simp
    rw [e]
    refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
    rw [div_le_div_iff₀ hpos hm, theta'_sq]
    have hπ : 0 ≤ π ^ 2 := sq_nonneg _
    nlinarith [mul_nonneg (mul_nonneg hπ (sub_nonneg.2 h1)) (mul_nonneg (sub_nonneg.2 h1) hm.le),
      mul_nonneg hπ (mul_nonneg (sub_nonneg.2 h1) hm.le), mul_nonneg hπ (sub_nonneg.2 hlow2)]
  calc ∫ x : Torus d, D.rhoT t x * ‖D.vf t (Torus.rep x)‖ ^ 2
      ≤ ∫ x : Torus d, π ^ 2 / D.m * ‖D.gradU (Torus.rep x)‖ ^ 2 := by
        refine integral_mono ?_ ?_ hpt
        · exact q12_integrable_cont ((D.continuous_rhoT t).mul (hvc.norm.pow 2))
        · exact q12_integrable_cont (continuous_const.mul (hgc.norm.pow 2))
    _ = π ^ 2 * D.energy / D.m := by
        rw [integral_const_mul]; unfold energy; ring

end PeyreData

end HRS.Uniform.Q12
