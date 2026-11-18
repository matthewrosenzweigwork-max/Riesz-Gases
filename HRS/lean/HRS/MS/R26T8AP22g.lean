import HRS.MS.R26T8AP22f

/-!
# S8.2 local Newton layer, packet T8A.P22 (part g): domination of the Laplacian of the cut-off leading inverse
`phi_eps = (1 - chi(w/eps)) * chi(w) * L_B(w)`; `r26t8a_p22_lap_phi_bound`: `|Δ phi_eps (w)| <= C ‖B‖ |w|^(-s')` for `0 < |w| <= 2`, uniformly in `eps > 0` and `B`;
`r26t8a_p22_lap_phi_zero`: `Δ phi_eps (w) = 0` for `|w| > 2`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ContDiff
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.S82N

namespace HRS.MS.R26T8A

variable {d : ℕ}

theorem r26t8a_p22_bdd_of_vanish {V : Type} [NormedAddCommGroup V] {h : Euc d → V} (hh : Continuous h)
    (hv : ∀ x : Euc d, 2 < ‖x‖ → h x = 0) : ∃ D : ℝ, 0 ≤ D ∧ ∀ x, ‖h x‖ ≤ D := by
  obtain ⟨D, hD⟩ := (isCompact_closedBall (0 : Euc d) 2).exists_bound_of_continuousOn hh.continuousOn
  refine ⟨max D 0, le_max_right _ _, fun x => ?_⟩
  by_cases hx : ‖x‖ ≤ 2
  · exact (hD x (by simpa using hx)).trans (le_max_left _ _)
  · rw [hv x (not_le.1 hx), norm_zero]; exact le_max_right _ _

theorem r26t8a_p22_chi_bounds {chi : Euc d → ℝ} (hchi : NewtonCutoff chi) :
    ∃ D1 D2 : ℝ, 0 ≤ D1 ∧ 0 ≤ D2 ∧ (∀ x, ‖fderiv ℝ chi x‖ ≤ D1) ∧ (∀ x, |Laplacian.laplacian chi x| ≤ D2) := by
  have hc2 := r26t8a_p22_chi_c2 hchi
  obtain ⟨D1, hD10, hD1⟩ := r26t8a_p22_bdd_of_vanish (h := fderiv ℝ chi) (hc2.continuous_fderiv (by norm_num))
    (fun x hx => (r26t8a_p22_chi_flat hchi (Or.inr hx.le)).1)
  obtain ⟨D2, hD20, hD2⟩ := r26t8a_p22_bdd_of_vanish (h := Laplacian.laplacian chi)
    (HRS.Parx.continuous_laplacian hc2) (fun x hx => (r26t8a_p22_chi_flat hchi (Or.inr hx.le)).2)
  exact ⟨D1, D2, hD10, hD20, hD1, fun x => by simpa using hD2 x⟩

theorem r26t8a_p22_grad_norm (f : Euc d → ℝ) (x : Euc d) : ‖gradient f x‖ = ‖fderiv ℝ f x‖ := by
  simp [gradient]

theorem r26t8a_p22_inner_le (f g : Euc d → ℝ) (x : Euc d) :
    |inner ℝ (gradient f x) (gradient g x)| ≤ ‖fderiv ℝ f x‖ * ‖fderiv ℝ g x‖ := by
  rw [← r26t8a_p22_grad_norm, ← r26t8a_p22_grad_norm]
  exact abs_real_inner_le_norm _ _

end HRS.MS.R26T8A
