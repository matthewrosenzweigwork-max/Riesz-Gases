import HRS.MC.CepH2Lip1

/-!
# CEPH2, G1 (a): lemmas for freezing the potential outside a tube
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.CepH2

open HRS HRS.MC.Cepa

variable {N : ℕ} [NeZero N]

theorem h2_fderiv2_far {φ : Ch N → ℝ} {R : ℝ} (hR : ∀ x, R < ‖h2_perp x‖ → φ x = 0) {x : Ch N}
    (hx : R < ‖h2_perp x‖) : fderiv ℝ (fderiv ℝ φ) x = 0 := by
  have hopen : IsOpen {y : Ch N | R < ‖h2_perp y‖} :=
    isOpen_lt continuous_const (h2_continuous_perp.norm)
  have h1 : ∀ y ∈ {y : Ch N | R < ‖h2_perp y‖}, fderiv ℝ φ y = 0 := fun y hy =>
    h2_fderiv_eq_zero_of_far hR hy
  have hev : fderiv ℝ φ =ᶠ[𝓝 x] fun _ => (0 : Ch N →L[ℝ] ℝ) :=
    Filter.mem_of_superset (hopen.mem_nhds hx) fun y hy => h1 y hy
  rw [hev.fderiv_eq]; simp

theorem h2_bdd_fderiv2 {φ : Ch N → ℝ} (hφ : ContDiff ℝ 2 φ) (hper : ∀ x, φ (x + cep_diag N) = φ x) {R : ℝ}
    (hR : ∀ x, R < ‖h2_perp x‖ → φ x = 0) : ∃ B : ℝ, 0 ≤ B ∧ ∀ x, ‖fderiv ℝ (fderiv ℝ φ) x‖ ≤ B := by
  have hc : Continuous (fderiv ℝ (fderiv ℝ φ)) := by
    have h1 : ContDiff ℝ 1 (fderiv ℝ φ) := hφ.fderiv_right (by norm_num)
    exact h1.continuous_fderiv (by norm_num)
  have hp1 : ∀ x, fderiv ℝ φ (x + cep_diag N) = fderiv ℝ φ x := h2_fderiv_periodic_gen hper
  have hp2 : ∀ x, fderiv ℝ (fderiv ℝ φ) (x + cep_diag N) = fderiv ℝ (fderiv ℝ φ) x :=
    h2_fderiv_periodic_gen hp1
  obtain ⟨C, hC⟩ := h2_bdd_tube hc hp2 R
  refine ⟨max C 0, le_max_right _ _, fun x => ?_⟩
  by_cases hx : ‖h2_perp x‖ ≤ R
  · exact (hC x hx).trans (le_max_left _ _)
  · rw [h2_fderiv2_far hR (not_le.1 hx)]
    exact (norm_zero (E := Ch N →L[ℝ] Ch N →L[ℝ] ℝ)).le.trans (le_max_right _ _)

/-- A `C²` function with bounded second derivative has a Lipschitz gradient. -/
theorem h2_lipschitz_gradient {φ : Ch N → ℝ} (hφ : ContDiff ℝ 2 φ) {B : ℝ} (hB : 0 ≤ B)
    (h : ∀ x, ‖fderiv ℝ (fderiv ℝ φ) x‖ ≤ B) : LipschitzWith (Real.toNNReal B) (gradient φ) := by
  have h1 : ContDiff ℝ 1 (fderiv ℝ φ) := hφ.fderiv_right (by norm_num)
  have hl : LipschitzWith (Real.toNNReal B) (fderiv ℝ φ) := by
    refine lipschitzWith_of_nnnorm_fderiv_le (fun x => (h1.differentiable (by simp)) x) fun x => ?_
    rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal _ hB]
    exact h x
  have hg : gradient φ = fun x => (InnerProductSpace.toDual ℝ (Ch N)).symm (fderiv ℝ φ x) := rfl
  rw [hg]
  have := (InnerProductSpace.toDual ℝ (Ch N)).symm.lipschitz.comp hl
  rw [one_mul] at this
  exact this

theorem h2_inner_perp (x w : Ch N) : inner ℝ (h2_perp x) (h2_perp w) = inner ℝ (h2_perp x) w := by
  have h : inner ℝ (h2_perp x) (h2_mean w • cep_diag N) = 0 := by
    rw [real_inner_smul_right]
    have : inner ℝ (h2_perp x) (cep_diag N) = 0 := by
      have hN : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne N)
      simp only [PiLp.inner_apply, h2_perp_eq, cep_diag_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul,
        RCLike.inner_apply, conj_trivial, mul_one]
      simp only [one_mul]
      rw [Finset.sum_sub_distrib]
      simp only [h2_mean, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp
      ring
    rw [this, mul_zero]
  have : h2_perp w = w - h2_mean w • cep_diag N := rfl
  rw [this, inner_sub_right, h, sub_zero]

end HRS.MC.CepH2
