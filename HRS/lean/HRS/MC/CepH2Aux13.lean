import HRS.MC.CepH2Aux12

/-!
# CEPH2, helper 13: potentials with Lipschitz gradient

Descent lemma `|U(x+w) - U(x) - ⟨∇U(x),w⟩| ≤ K‖w‖²/2`, growth bounds on the cylinder, and periodicity of `∇U`.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators Pointwise

noncomputable section

namespace HRS.MC.CepH2

open HRS HRS.MC.Cepa

variable {N : ℕ}

theorem h2_fderiv_eq_inner {U : Ch N → ℝ} (x w : Ch N) : fderiv ℝ U x w = inner ℝ (gradient U x) w := by
  show fderiv ℝ U x w = inner ℝ ((InnerProductSpace.toDual ℝ (Ch N)).symm (fderiv ℝ U x)) w
  rw [InnerProductSpace.toDual_symm_apply]

theorem h2_norm_gradient {U : Ch N → ℝ} (x : Ch N) : ‖gradient U x‖ = ‖fderiv ℝ U x‖ :=
  (InnerProductSpace.toDual ℝ (Ch N)).symm.norm_map _

theorem h2_hasDerivAt_line {U : Ch N → ℝ} (hU : ContDiff ℝ 1 U) (x w : Ch N) (s : ℝ) :
    HasDerivAt (fun s : ℝ => U (x + s • w)) (inner ℝ (gradient U (x + s • w)) w) s := by
  have h1 : HasDerivAt (fun s : ℝ => x + s • w) w s := by
    simpa using ((hasDerivAt_id s).smul_const w).const_add x
  have h := (hU.differentiable (by simp) (x + s • w)).hasFDerivAt.comp_hasDerivAt s h1
  rw [h2_fderiv_eq_inner] at h
  exact h

/-- Descent lemma. -/
theorem h2_U_quad {U : Ch N → ℝ} (hU : ContDiff ℝ 1 U) {K : ℝ≥0} (hK : LipschitzWith K (gradient U)) (x w : Ch N) :
    |U (x + w) - U x - inner ℝ (gradient U x) w| ≤ K * ‖w‖ ^ 2 / 2 := by
  have hc : ∀ s : ℝ, HasDerivAt (fun s : ℝ => U (x + s • w)) (inner ℝ (gradient U (x + s • w)) w) s :=
    h2_hasDerivAt_line hU x w
  have hlip : ∀ s : ℝ, 0 ≤ s → |inner ℝ (gradient U (x + s • w) - gradient U x) w| ≤ K * s * ‖w‖ ^ 2 := by
    intro s hs
    calc |inner ℝ (gradient U (x + s • w) - gradient U x) w| ≤ ‖gradient U (x + s • w) - gradient U x‖ * ‖w‖ := by
          rw [← Real.norm_eq_abs]; exact norm_inner_le_norm _ _
      _ ≤ (K * ‖(x + s • w) - x‖) * ‖w‖ := by
          refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
          have := hK.dist_le_mul (x + s • w) x
          rwa [dist_eq_norm, dist_eq_norm] at this
      _ = K * s * ‖w‖ ^ 2 := by
          rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg hs]; ring
  -- upper bound
  set a : ℝ := inner ℝ (gradient U x) w with ha
  have hup : U (x + w) - U x - a - K * ‖w‖ ^ 2 / 2 ≤ 0 := by
    set f : ℝ → ℝ := fun s => U (x + s • w) - U x - s * a - K * ‖w‖ ^ 2 * s ^ 2 / 2 with hf
    have hfd : ∀ s : ℝ, HasDerivAt f (inner ℝ (gradient U (x + s • w)) w - a - K * ‖w‖ ^ 2 * s) s := by
      intro s
      have := ((hc s).sub_const (U x)).sub ((hasDerivAt_id s).mul_const a)
      have h2 := this.sub (((hasDerivAt_pow 2 s).const_mul (K * ‖w‖ ^ 2)).div_const 2)
      have hfun : f = (((fun x_1 => U (x + x_1 • w) - U x) - fun y => id y * a) -
          fun x => K * ‖w‖ ^ 2 * x ^ 2 / 2) := by
        funext s; simp only [hf, Pi.sub_apply, id]
      rw [hfun]
      exact h2.congr_deriv (by simp; ring)
    have hmono : AntitoneOn f (Set.Icc 0 1) := by
      refine antitoneOn_of_deriv_nonpos (convex_Icc 0 1) (fun s _ => (hfd s).continuousAt.continuousWithinAt)
        (fun s _ => (hfd s).differentiableAt.differentiableWithinAt) ?_
      intro s hs
      rw [interior_Icc] at hs
      rw [(hfd s).deriv]
      have := hlip s hs.1.le
      rw [inner_sub_left] at this
      have := (abs_le.1 this).2
      nlinarith
    have := hmono (Set.mem_Icc.2 ⟨le_rfl, zero_le_one⟩) (Set.mem_Icc.2 ⟨zero_le_one, le_rfl⟩) zero_le_one
    simpa [hf] using this
  have hlow : 0 ≤ U (x + w) - U x - a + K * ‖w‖ ^ 2 / 2 := by
    set f : ℝ → ℝ := fun s => U (x + s • w) - U x - s * a + K * ‖w‖ ^ 2 * s ^ 2 / 2 with hf
    have hfd : ∀ s : ℝ, HasDerivAt f (inner ℝ (gradient U (x + s • w)) w - a + K * ‖w‖ ^ 2 * s) s := by
      intro s
      have := ((hc s).sub_const (U x)).sub ((hasDerivAt_id s).mul_const a)
      have h2 := this.add (((hasDerivAt_pow 2 s).const_mul (K * ‖w‖ ^ 2)).div_const 2)
      have hfun : f = (((fun x_1 => U (x + x_1 • w) - U x) - fun y => id y * a) +
          fun x => K * ‖w‖ ^ 2 * x ^ 2 / 2) := by
        funext s; simp only [hf, Pi.sub_apply, Pi.add_apply, id]
      rw [hfun]
      exact h2.congr_deriv (by simp; ring)
    have hmono : MonotoneOn f (Set.Icc 0 1) := by
      refine monotoneOn_of_deriv_nonneg (convex_Icc 0 1) (fun s _ => (hfd s).continuousAt.continuousWithinAt)
        (fun s _ => (hfd s).differentiableAt.differentiableWithinAt) ?_
      intro s hs
      rw [interior_Icc] at hs
      rw [(hfd s).deriv]
      have := hlip s hs.1.le
      rw [inner_sub_left] at this
      have := (abs_le.1 this).1
      nlinarith
    have := hmono (Set.mem_Icc.2 ⟨le_rfl, zero_le_one⟩) (Set.mem_Icc.2 ⟨zero_le_one, le_rfl⟩) zero_le_one
    simpa [hf] using this
  rw [abs_le]
  constructor <;> linarith

section
variable [NeZero N]

theorem h2_gradient_periodic {U : Ch N → ℝ} (hUper : ∀ z, U (z + cep_diag N) = U z) (z : Ch N) :
    gradient U (z + cep_diag N) = gradient U z := by
  show (InnerProductSpace.toDual ℝ (Ch N)).symm (fderiv ℝ U (z + cep_diag N)) =
    (InnerProductSpace.toDual ℝ (Ch N)).symm (fderiv ℝ U z)
  rw [h2_fderiv_periodic hUper]

theorem h2_grad_commutator {U : Ch N → ℝ} (hUper : ∀ z, U (z + cep_diag N) = U z) {K : ℝ≥0}
    (hK : LipschitzWith K (gradient U)) (x y : Ch N) (m : ℤ) :
    ‖gradient U y - gradient U x‖ ≤ K * ‖(x - y) + (m : ℝ) • cep_diag N‖ := by
  have h1 : gradient U (y + ((-m : ℤ) : ℝ) • cep_diag N) = gradient U y :=
    h2_periodic_gen (f := gradient U) (h2_gradient_periodic hUper) (-m) y
  have h2 := hK.dist_le_mul (y + ((-m : ℤ) : ℝ) • cep_diag N) x
  rw [h1, dist_eq_norm, dist_eq_norm] at h2
  have e : y + ((-m : ℤ) : ℝ) • cep_diag N - x = -((x - y) + (m : ℝ) • cep_diag N) := by
    push_cast; module
  rw [e, norm_neg] at h2
  exact h2

theorem h2_grad_growth {U : Ch N → ℝ} (hUper : ∀ z, U (z + cep_diag N) = U z) {K : ℝ≥0}
    (hK : LipschitzWith K (gradient U)) :
    ∃ a b : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ ∀ x, ‖gradient U x‖ ≤ a + b * ‖h2_perp x‖ := by
  refine ⟨‖gradient U 0‖ + K * Real.sqrt N, K * (1 + Real.sqrt N), by positivity, by positivity, fun x => ?_⟩
  have hx : cep_reduce x ∈ cep_cell N := h2_reduce_mem_cell x
  have hg : gradient U x = gradient U (cep_reduce x) := by
    rw [h2_reduce_eq]
    exact (h2_periodic_gen (f := gradient U) (h2_gradient_periodic hUper) _ x).symm
  have h1 : ‖gradient U (cep_reduce x)‖ ≤ ‖gradient U 0‖ + K * ‖cep_reduce x‖ := by
    have := hK.dist_le_mul (cep_reduce x) 0
    simp only [dist_eq_norm, sub_zero] at this
    have h3 := norm_le_norm_add_norm_sub' (gradient U (cep_reduce x)) (gradient U 0)
    have h4 := norm_sub_rev (gradient U 0) (gradient U (cep_reduce x))
    linarith
  have h2 := h2_cell_norm_le hx
  rw [h2_perp_reduce] at h2
  rw [hg]
  refine h1.trans ?_
  have : (K : ℝ) * ‖cep_reduce x‖ ≤ K * (‖h2_perp x‖ + Real.sqrt N * (1 + ‖h2_perp x‖)) :=
    mul_le_mul_of_nonneg_left h2 (by positivity)
  nlinarith

theorem h2_U_growth {U : Ch N → ℝ} (hU : ContDiff ℝ 1 U) (hUper : ∀ z, U (z + cep_diag N) = U z) {K : ℝ≥0}
    (hK : LipschitzWith K (gradient U)) :
    ∃ a b : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ ∀ x, |U x| ≤ a + b * ‖h2_perp x‖ ^ 2 := by
  set Q : ℝ := 2 * (1 + Real.sqrt N) ^ 2 with hQ
  refine ⟨|U 0| + ‖gradient U 0‖ ^ 2 / 2 + (‖gradient U 0‖ / 2 + K / 2 + 1 / 2) * (2 * N), 
    (‖gradient U 0‖ / 2 + K / 2 + 1 / 2) * Q, by positivity, by positivity, fun x => ?_⟩
  have hx : cep_reduce x ∈ cep_cell N := h2_reduce_mem_cell x
  have hUx : U x = U (cep_reduce x) := by
    rw [h2_reduce_eq]
    exact (h2_periodic_gen (f := U) hUper _ x).symm
  have hq := h2_U_quad hU hK 0 (cep_reduce x)
  rw [zero_add] at hq
  have h2 := h2_cell_norm_sq_le hx
  rw [h2_perp_reduce] at h2
  set w := cep_reduce x
  have hwn : ‖gradient U 0‖ * ‖w‖ ≤ ‖gradient U 0‖ ^ 2 / 2 + ‖w‖ ^ 2 / 2 := by
    nlinarith [sq_nonneg (‖gradient U 0‖ - ‖w‖)]
  have hup : U w ≤ U 0 + inner ℝ (gradient U 0) w + K * ‖w‖ ^ 2 / 2 := by
    have := (abs_le.1 hq).2; linarith
  have hlo : U 0 + inner ℝ (gradient U 0) w - K * ‖w‖ ^ 2 / 2 ≤ U w := by
    have := (abs_le.1 hq).1; linarith
  have hin2 : |inner ℝ (gradient U 0) w| ≤ ‖gradient U 0‖ * ‖w‖ := abs_real_inner_le_norm _ _
  have hin3 := abs_le.1 hin2
  rw [hUx]
  rw [abs_le]
  have hP : 0 ≤ ‖h2_perp x‖ ^ 2 := by positivity
  have hw2 : 0 ≤ ‖w‖ ^ 2 := by positivity
  have hK0 : (0 : ℝ) ≤ K := K.2
  have hn0 : 0 ≤ ‖gradient U 0‖ := norm_nonneg _
  constructor <;> nlinarith [abs_nonneg (U 0), neg_abs_le (U 0), le_abs_self (U 0), mul_nonneg hK0 hw2,
    mul_nonneg hn0 hw2]

end

end HRS.MC.CepH2
