import HRS.MC.CepH2Aux25

/-!
# CEPH2, helper 26: pointwise domination of the cut-off error integrand

For `R ≥ 1`: `|(ℓ_s(x)+1) B_{χ_R}(x,y)| ≤ C · 1_{R ≤ ‖P⊥x‖} ‖P⊥x‖ (a₁ + b₁ ‖P⊥y‖) Ĝ_{2v}(x-y)`.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators Pointwise

noncomputable section

namespace HRS.MC.CepH2

open HRS HRS.MC.Cepa

variable {N : ℕ} [NeZero N]

theorem h2_B_abs_le {v : ℝ} (hv : 0 < v) (θ : ℝ) (U : Ch N → ℝ) (φ : Ch N → ℝ) (x y : Ch N) :
    |h2_B θ v U φ x y| ≤ ‖fderiv ℝ φ x‖ * (|θ| * N * ‖h2_per1 v (x - y)‖ + ‖gradient U y‖ * h2_per v (x - y)) := by
  have hp := h2_per_nonneg hv (x - y)
  unfold h2_B
  refine le_trans (abs_add_le _ _) ?_
  have h1 : |θ * ∑ k, fderiv ℝ φ x (h2_e k) * h2_per1 v (x - y) (h2_e k)| ≤
      ‖fderiv ℝ φ x‖ * (|θ| * N * ‖h2_per1 v (x - y)‖) := by
    rw [abs_mul]
    calc |θ| * |∑ k, fderiv ℝ φ x (h2_e k) * h2_per1 v (x - y) (h2_e k)|
        ≤ |θ| * ∑ _k : Fin N, ‖fderiv ℝ φ x‖ * ‖h2_per1 v (x - y)‖ := by
          refine mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs _ _).trans
            (Finset.sum_le_sum fun k _ => ?_)) (abs_nonneg _)
          rw [abs_mul]
          refine mul_le_mul ?_ ?_ (abs_nonneg _) (norm_nonneg _)
          · rw [← Real.norm_eq_abs]
            calc ‖fderiv ℝ φ x (h2_e k)‖ ≤ ‖fderiv ℝ φ x‖ * ‖h2_e k‖ := ContinuousLinearMap.le_opNorm _ _
              _ = _ := by rw [h2_norm_e, mul_one]
          · rw [← Real.norm_eq_abs]
            calc ‖h2_per1 v (x - y) (h2_e k)‖ ≤ ‖h2_per1 v (x - y)‖ * ‖h2_e k‖ := ContinuousLinearMap.le_opNorm _ _
              _ = _ := by rw [h2_norm_e, mul_one]
      _ = ‖fderiv ℝ φ x‖ * (|θ| * N * ‖h2_per1 v (x - y)‖) := by simp; ring
  have h2 : |fderiv ℝ φ x (gradient U y) * h2_per v (x - y)| ≤ ‖fderiv ℝ φ x‖ * (‖gradient U y‖ * h2_per v (x - y)) := by
    rw [abs_mul, abs_of_nonneg hp]
    calc |fderiv ℝ φ x (gradient U y)| * h2_per v (x - y) ≤ (‖fderiv ℝ φ x‖ * ‖gradient U y‖) * h2_per v (x - y) := by
          refine mul_le_mul_of_nonneg_right ?_ hp
          rw [← Real.norm_eq_abs]; exact ContinuousLinearMap.le_opNorm _ _
      _ = _ := by ring
  calc _ ≤ _ := add_le_add h1 h2
    _ = _ := by ring

/-- Indicator of the shell `{R ≤ ‖P⊥x‖}`. -/
def h2_ind (R : ℝ) (x : Ch N) : ℝ := Set.indicator {x : Ch N | R ≤ ‖h2_perp x‖} (fun _ => (1 : ℝ)) x

theorem h2_ind_nonneg (R : ℝ) (x : Ch N) : 0 ≤ h2_ind R x := Set.indicator_nonneg (fun _ _ => zero_le_one) x

theorem h2_ind_le_one (R : ℝ) (x : Ch N) : h2_ind R x ≤ 1 := by
  unfold h2_ind
  by_cases hx : x ∈ {x : Ch N | R ≤ ‖h2_perp x‖}
  · rw [Set.indicator_of_mem hx]
  · rw [Set.indicator_of_notMem hx]; exact zero_le_one

theorem h2_ind_of_le {R : ℝ} {x : Ch N} (hx : R ≤ ‖h2_perp x‖) : h2_ind R x = 1 := by
  unfold h2_ind; rw [Set.indicator_of_mem (show x ∈ {x : Ch N | R ≤ ‖h2_perp x‖} from hx)]

theorem h2_ind_of_lt {R : ℝ} {x : Ch N} (hx : ‖h2_perp x‖ < R) : h2_ind R x = 0 := by
  unfold h2_ind
  rw [Set.indicator_of_notMem (show x ∉ {x : Ch N | R ≤ ‖h2_perp x‖} from not_le.2 hx)]

theorem h2_ind_periodic (R : ℝ) (x : Ch N) : h2_ind R (x + cep_diag N) = h2_ind R x := by
  unfold h2_ind
  simp only [Set.indicator, Set.mem_ofPred_eq, h2_perp_periodic]

theorem h2_measurable_ind (R : ℝ) : Measurable (h2_ind (N := N) R) :=
  measurable_const.indicator (measurableSet_le measurable_const h2_continuous_perp.norm.measurable)

section
variable {θ v : ℝ} {U : Ch N → ℝ} {K : ℝ≥0} {μ : ℝ → Measure (Ch N)} {T M : ℝ}

theorem H2Set.E_dom (S : H2Set θ v U K μ T M) :
    ∃ a₁ b₁ CE : ℝ, 0 ≤ a₁ ∧ 0 ≤ b₁ ∧ 0 ≤ CE ∧ ∀ (s R : ℝ) (x y : Ch N), 1 ≤ R →
      |(h2_ell θ v U (μ s) x + 1) * h2_B θ v U (h2_chi R) x y| ≤
        CE * (h2_ind R x * (‖h2_perp x‖ * (a₁ + b₁ * ‖h2_perp y‖)) * h2_per (2 * v) (x - y)) := by
  obtain ⟨cE, hcE, hE⟩ := S.ell_bound
  obtain ⟨L, hL0, hL⟩ := h2_fderiv_chi_bound (N := N)
  obtain ⟨a, b, ha, hb, hab⟩ := h2_grad_growth S.hUper S.hK
  have hv := S.hv
  have hc1 := h2_c1_nonneg (N := N) hv
  have hc2 : (0 : ℝ) ≤ (2 : ℝ) ^ ((N : ℝ) / 2) := by positivity
  refine ⟨|θ| * N * h2_c1 N v + a * (2 : ℝ) ^ ((N : ℝ) / 2), b * (2 : ℝ) ^ ((N : ℝ) / 2),
    2 * (cE + 1) * L, by positivity, by positivity, by positivity, fun s R x y hR => ?_⟩
  set r := ‖h2_perp x‖ with hr
  set r' := ‖h2_perp y‖ with hr'
  have hp2 := h2_per_nonneg (N := N) (by positivity : 0 < 2 * v) (x - y)
  have hp := h2_per_nonneg (N := N) hv (x - y)
  have hr0 : 0 ≤ r := norm_nonneg _
  have hr'0 : 0 ≤ r' := norm_nonneg _
  have ha₁ : 0 ≤ |θ| * N * h2_c1 N v + a * (2 : ℝ) ^ ((N : ℝ) / 2) := by positivity
  have hb₁ : 0 ≤ b * (2 : ℝ) ^ ((N : ℝ) / 2) := by positivity
  have hCE : 0 ≤ 2 * (cE + 1) * L := by positivity
  have hRHS : 0 ≤ (2 * (cE + 1) * L) * (h2_ind R x * (r * ((|θ| * N * h2_c1 N v + a * (2 : ℝ) ^ ((N : ℝ) / 2)) +
      b * (2 : ℝ) ^ ((N : ℝ) / 2) * r')) * h2_per (2 * v) (x - y)) :=
    mul_nonneg hCE (mul_nonneg (mul_nonneg (h2_ind_nonneg R x) (mul_nonneg hr0 (by positivity))) hp2)
  by_cases hx : r < R
  · have h0 : fderiv ℝ (h2_chi R) x = 0 := (hL (by linarith : 0 < R) x).1 hx.le
    have : h2_B θ v U (h2_chi R) x y = 0 := by simp [h2_B, h0]
    rw [this, mul_zero, abs_zero]
    exact hRHS
  · have hRr : R ≤ r := not_lt.1 hx
    rw [h2_ind_of_le hRr]
    have hR0 : 0 < R := by linarith
    have hB := h2_B_abs_le hv θ U (h2_chi R) x y
    have hdχ : ‖fderiv ℝ (h2_chi R) x‖ * r ≤ L := (hL hR0 x).2
    have hr1 : 1 ≤ r := by linarith
    have hr2 : 1 ≤ r ^ 2 := by nlinarith
    have hℓ : |h2_ell θ v U (μ s) x + 1| ≤ 2 * (cE + 1) * r ^ 2 := by
      refine (abs_add_le _ _).trans ?_
      rw [abs_one]
      have := hE s x
      nlinarith [mul_nonneg hcE (sq_nonneg r)]
    have hP : |θ| * N * ‖h2_per1 v (x - y)‖ + ‖gradient U y‖ * h2_per v (x - y) ≤
        ((|θ| * N * h2_c1 N v + a * (2 : ℝ) ^ ((N : ℝ) / 2)) + b * (2 : ℝ) ^ ((N : ℝ) / 2) * r') *
          h2_per (2 * v) (x - y) := by
      have e1 := h2_norm_per1_le_two hv (x - y)
      have e2 := h2_per_le_two hv (x - y)
      have e3 := hab y
      have t1 : |θ| * N * ‖h2_per1 v (x - y)‖ ≤ |θ| * N * (h2_c1 N v * h2_per (2 * v) (x - y)) :=
        mul_le_mul_of_nonneg_left e1 (by positivity)
      have t2 : ‖gradient U y‖ * h2_per v (x - y) ≤ (a + b * r') * ((2 : ℝ) ^ ((N : ℝ) / 2) * h2_per (2 * v) (x - y)) :=
        mul_le_mul e3 e2 hp (by positivity)
      nlinarith [t1, t2]
    have hdn := norm_nonneg (fderiv ℝ (h2_chi R) x)
    have hPnn : 0 ≤ ((|θ| * N * h2_c1 N v + a * (2 : ℝ) ^ ((N : ℝ) / 2)) + b * (2 : ℝ) ^ ((N : ℝ) / 2) * r') *
          h2_per (2 * v) (x - y) := by positivity
    rw [abs_mul]
    calc |h2_ell θ v U (μ s) x + 1| * |h2_B θ v U (h2_chi R) x y|
        ≤ |h2_ell θ v U (μ s) x + 1| * (‖fderiv ℝ (h2_chi R) x‖ * (|θ| * N * ‖h2_per1 v (x - y)‖ +
            ‖gradient U y‖ * h2_per v (x - y))) := mul_le_mul_of_nonneg_left hB (abs_nonneg _)
      _ ≤ (2 * (cE + 1) * r ^ 2) * (‖fderiv ℝ (h2_chi R) x‖ * (((|θ| * N * h2_c1 N v + a * (2 : ℝ) ^ ((N : ℝ) / 2)) +
            b * (2 : ℝ) ^ ((N : ℝ) / 2) * r') * h2_per (2 * v) (x - y))) :=
          mul_le_mul hℓ (mul_le_mul_of_nonneg_left hP hdn) (by positivity) (by positivity)
      _ = (2 * (cE + 1)) * (‖fderiv ℝ (h2_chi R) x‖ * r) * (r * (((|θ| * N * h2_c1 N v + a * (2 : ℝ) ^ ((N : ℝ) / 2)) +
            b * (2 : ℝ) ^ ((N : ℝ) / 2) * r') * h2_per (2 * v) (x - y))) := by ring
      _ ≤ (2 * (cE + 1)) * L * (r * (((|θ| * N * h2_c1 N v + a * (2 : ℝ) ^ ((N : ℝ) / 2)) +
            b * (2 : ℝ) ^ ((N : ℝ) / 2) * r') * h2_per (2 * v) (x - y))) := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hdχ (by positivity)) (by positivity)
      _ = _ := by ring

end

end HRS.MC.CepH2
