import HRS.Uniform.Q12P15

/-!
# Q12, Peyre part 16: the transport bound for the Moser data
-/

noncomputable section

open HRS MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators Real

namespace HRS.Uniform.Q12

variable {d : ℕ}

namespace PeyreData

variable (D : PeyreData d)

lemma rhoT_zero : D.rhoT 0 = D.g := by
  funext x; unfold rhoT; rw [theta_zero]; ring

lemma rhoT_one : D.rhoT 1 = D.f := by
  funext x; unfold rhoT; rw [theta_one]; ring

lemma contDiff_vf_t (t : ℝ) : ContDiff ℝ 2 (D.vf t) := by
  have h := ContDiff.comp (g := fun p : ℝ × Euc d => D.vf p.1 p.2) (f := fun y : Euc d => (t, y))
    D.contDiff_vf_joint (contDiff_const.prodMk contDiff_id)
  exact h

set_option maxHeartbeats 1000000 in
/-- `W_2(g, f) ≤ π (E_u / m)^{1/2}`. -/
theorem W2_data : torusWassersteinE 2 (withDensityReal D.g) (withDensityReal D.f) ≤
    ENNReal.ofReal (Real.sqrt (π ^ 2 * D.energy / D.m)) := by
  -- uniform bounds
  have hper : ∀ t, Torus.Per (fun y => (fun p : ℝ × Euc d => D.vf p.1 p.2) (t, y)) := fun t => D.per_vf t
  obtain ⟨B, hB⟩ := q12_unif_bounds D.contDiff_vf_joint hper
  have hF2 : ContDiff ℝ 2 (fun p : ℝ × Euc d => ‖D.vf p.1 p.2‖ ^ 2) :=
    (contDiff_norm_sq ℝ).comp D.contDiff_vf_joint
  have hper2 : ∀ t, Torus.Per (fun y => (fun p : ℝ × Euc d => ‖D.vf p.1 p.2‖ ^ 2) (t, y)) :=
    fun t y n => by
      show ‖D.vf t (y + Lattice.toEuc n)‖ ^ 2 = ‖D.vf t y‖ ^ 2
      rw [D.per_vf t y n]
  obtain ⟨Θ, hΘ⟩ := q12_unif_bounds hF2 hper2
  have h := q12_scheme_coupling (w := D.vf) (μ := D.muT) (V := B) (V₁ := B) (V₂ := B)
    (δ := π ^ 2) (Θ₂ := Θ) (a := π ^ 2 * D.energy / D.m)
    (fun t => D.contDiff_vf_t t) (fun t => D.per_vf t)
    (fun t ht y => (hB t ht y).1) (fun t ht y => (hB t ht y).2.1) (fun t ht y => (hB t ht y).2.2)
    (fun t _ => inferInstance) (sq_nonneg π)
    (fun t τ _ hτ0 _ _ Φ B' hp hC => D.weak_CE hτ0.le hp hC)
    (fun t ht => ⟨(D.contDiff_vf_t t).norm_sq ℝ, fun y => by
      obtain ⟨h1, h2, h3⟩ := hΘ t ht y
      refine ⟨?_, h2, h3⟩
      rw [Real.norm_eq_abs] at h1
      exact h1⟩)
    (fun t _ => D.kinetic t)
  rw [show D.muT 0 = withDensityReal D.g from by unfold muT; rw [rhoT_zero],
    show D.muT 1 = withDensityReal D.f from by unfold muT; rw [rhoT_one]] at h
  exact h

end PeyreData

end HRS.Uniform.Q12
