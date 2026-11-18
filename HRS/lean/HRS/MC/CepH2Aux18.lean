import HRS.MC.CepH2Aux17

/-!
# CEPH2, helper 18: parametric integrals against a narrowly continuous family

`H2Narrow μ`: `t ↦ ∫ g dμ_t` is continuous for bounded continuous diagonally periodic `g`.
`H2Good U H`: the integrands `H x y` we integrate in `y` against `μ_s`: jointly continuous, periodic in `y`,
bounded in `y` for fixed `x`, and dominated by `c (1 + ‖∇U y‖)` uniformly in `x`.  For such `H`,
`(s, x) ↦ ∫ H x y dμ_s(y)` is jointly measurable and continuous in each variable.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators Pointwise

noncomputable section

namespace HRS.MC.CepH2

open HRS HRS.MC.Cepa

variable {N : ℕ}

/-- Narrow continuity in time against bounded continuous periodic test functions. -/
def H2Narrow (μ : ℝ → Measure (Ch N)) : Prop :=
  ∀ g : Ch N → ℝ, Continuous g → (∀ z, g (z + cep_diag N) = g z) → (∃ C : ℝ, ∀ z, |g z| ≤ C) →
    Continuous (fun t => ∫ z, g z ∂(μ t))

/-- Good integrands. -/
def H2Good (U : Ch N → ℝ) (H : Ch N → Ch N → ℝ) : Prop :=
  Continuous (Function.uncurry H) ∧ (∀ x y, H x (y + cep_diag N) = H x y) ∧ (∀ x, ∃ C : ℝ, ∀ y, |H x y| ≤ C) ∧
    ∃ c : ℝ, ∀ x y, |H x y| ≤ c * (1 + ‖gradient U y‖)

theorem h2_sup_mul_exp {c : ℝ} (hc : 0 < c) {r : ℝ} (hr : 0 ≤ r) :
    (1 + r) * Real.exp (-c * r ^ 2) ≤ 2 + 2 / c := by
  have h1 : Real.exp (-c * r ^ 2) ≤ 1 := by
    rw [Real.exp_le_one_iff]; nlinarith [sq_nonneg r]
  have h2 := h2_sq_exp_le hc r
  have h3 : Real.exp (-(c / 2) * r ^ 2) ≤ 1 := by
    rw [Real.exp_le_one_iff]; nlinarith [sq_nonneg r]
  have h4 : (2 / c) * Real.exp (-(c / 2) * r ^ 2) ≤ 2 / c := mul_le_of_le_one_right (by positivity) h3
  have h5 : r * Real.exp (-c * r ^ 2) ≤ (1 + r ^ 2) * Real.exp (-c * r ^ 2) :=
    mul_le_mul_of_nonneg_right (by nlinarith [sq_nonneg (r - 1)]) (Real.exp_pos _).le
  nlinarith [Real.exp_pos (-c * r ^ 2)]

section
variable [NeZero N]

theorem h2_per_grad_bdd {v : ℝ} (hv : 0 < v) {U : Ch N → ℝ} (hUper : ∀ z, U (z + cep_diag N) = U z) {K : ℝ≥0}
    (hK : LipschitzWith K (gradient U)) (x : Ch N) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y, ‖h2_per v (x - y)‖ * (1 + ‖gradient U y‖) ≤ C ∧
      ‖h2_per1 v (x - y)‖ * (1 + ‖gradient U y‖) ≤ C ∧ ‖h2_per2 v (x - y)‖ * (1 + ‖gradient U y‖) ≤ C := by
  obtain ⟨B, hB0, hB⟩ := h2_per_bounds (N := N) hv
  obtain ⟨a, b, ha, hb, hab⟩ := h2_grad_growth hUper hK
  have hc : 0 < 1 / (4 * v) := by positivity
  set S : ℝ := 1 + a + b * ‖h2_perp x‖ + b with hS
  have hS0 : 0 ≤ S := by positivity
  refine ⟨B * S * (2 + 2 / (1 / (4 * v))), by positivity, fun y => ?_⟩
  set r : ℝ := ‖h2_perp (x - y)‖ with hr
  have hr0 : 0 ≤ r := norm_nonneg _
  have hy : ‖h2_perp y‖ ≤ ‖h2_perp x‖ + r := by
    have : h2_perp y = h2_perp x - h2_perp (x - y) := by rw [h2_perp_sub]; abel
    rw [this]; exact norm_sub_le _ _
  have hg : 1 + ‖gradient U y‖ ≤ S * (1 + r) := by
    have := hab y
    have h1 : b * ‖h2_perp y‖ ≤ b * (‖h2_perp x‖ + r) := mul_le_mul_of_nonneg_left hy hb
    nlinarith [mul_nonneg hb hr0, mul_nonneg hS0 hr0, norm_nonneg (h2_perp x), mul_nonneg hb (norm_nonneg (h2_perp x))]
  have key : ∀ q : ℝ, 0 ≤ q → q ≤ B * Real.exp (-(1 / (4 * v)) * r ^ 2) →
      q * (1 + ‖gradient U y‖) ≤ B * S * (2 + 2 / (1 / (4 * v))) := by
    intro q hq0 hq
    calc q * (1 + ‖gradient U y‖) ≤ (B * Real.exp (-(1 / (4 * v)) * r ^ 2)) * (S * (1 + r)) :=
          mul_le_mul hq hg (by positivity) (by positivity)
      _ = B * S * ((1 + r) * Real.exp (-(1 / (4 * v)) * r ^ 2)) := by ring
      _ ≤ B * S * (2 + 2 / (1 / (4 * v))) :=
          mul_le_mul_of_nonneg_left (h2_sup_mul_exp hc hr0) (by positivity)
  obtain ⟨h1, h2, h3⟩ := hB (x - y)
  exact ⟨key ‖h2_per v (x - y)‖ (norm_nonneg _) h1, key ‖h2_per1 v (x - y)‖ (norm_nonneg _) h2,
    key ‖h2_per2 v (x - y)‖ (ContinuousLinearMap.opNorm_nonneg _) h3⟩

theorem h2_sub_periodic_y {β : Type*} {f : Ch N → β} (hper : ∀ w, f (w + cep_diag N) = f w) (x y : Ch N) :
    f (x - (y + cep_diag N)) = f (x - y) := by
  rw [sub_add_eq_sub_sub]
  have := hper (x - y - cep_diag N)
  rw [sub_add_cancel] at this
  exact this.symm

theorem h2_A_bound {v : ℝ} (hv : 0 < v) (θ : ℝ) (U : Ch N → ℝ) :
    ∃ B2 : ℝ, 0 ≤ B2 ∧ ∀ x y, |h2_A θ v U x y| ≤ B2 * (1 + ‖gradient U y‖) := by
  obtain ⟨B, hB0, hB⟩ := h2_per_le (N := N) hv
  refine ⟨|θ| * N * B + B, by positivity, fun x y => ?_⟩
  have h1 : |h2_A θ v U x y| ≤ |θ| * (N * B) + B * ‖gradient U y‖ := by
    unfold h2_A
    refine le_trans (abs_add_le _ _) (add_le_add ?_ ?_)
    · rw [abs_mul]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      calc ∑ k, |h2_per2 v (x - y) (h2_e k) (h2_e k)| ≤ ∑ _k : Fin N, B := by
            refine Finset.sum_le_sum fun k _ => ?_
            rw [← Real.norm_eq_abs]
            calc ‖h2_per2 v (x - y) (h2_e k) (h2_e k)‖ ≤ ‖h2_per2 v (x - y)‖ * ‖h2_e k‖ * ‖h2_e k‖ :=
                  ContinuousLinearMap.le_opNorm₂ _ _ _
              _ ≤ B := by rw [h2_norm_e]; simpa using (hB _).2.2
        _ = N * B := by simp
    · rw [← Real.norm_eq_abs]
      calc ‖h2_per1 v (x - y) (gradient U y)‖ ≤ ‖h2_per1 v (x - y)‖ * ‖gradient U y‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ ≤ B * ‖gradient U y‖ := mul_le_mul_of_nonneg_right (hB _).2.1 (norm_nonneg _)
  have hg := norm_nonneg (gradient U y)
  have e : (|θ| * N * B + B) * (1 + ‖gradient U y‖) =
      |θ| * (N * B) + B * ‖gradient U y‖ + (|θ| * N * B * ‖gradient U y‖ + B) := by ring
  rw [e]
  have : 0 ≤ |θ| * N * B * ‖gradient U y‖ := by positivity
  linarith

theorem h2_good_per {v : ℝ} (hv : 0 < v) (U : Ch N → ℝ) : H2Good U (fun x y => h2_per v (x - y)) := by
  obtain ⟨B, hB0, hB⟩ := h2_per_le (N := N) hv
  refine ⟨(h2_continuous_per hv).comp (continuous_fst.sub continuous_snd), fun x y =>
    h2_sub_periodic_y (f := h2_per v) (h2_per_periodic v) x y, fun x => ⟨B, fun y => ?_⟩, ⟨B, fun x y => ?_⟩⟩
  · rw [← Real.norm_eq_abs]; exact (hB _).1
  · rw [← Real.norm_eq_abs]
    exact ((hB _).1).trans (le_mul_of_one_le_right hB0 (by linarith [norm_nonneg (gradient U y)]))

theorem h2_good_per1 {v : ℝ} (hv : 0 < v) (U : Ch N → ℝ) (w : Ch N) :
    H2Good U (fun x y => h2_per1 v (x - y) w) := by
  obtain ⟨B, hB0, hB⟩ := h2_per_le (N := N) hv
  have hb : ∀ z, |h2_per1 v z w| ≤ B * ‖w‖ := fun z => by
    rw [← Real.norm_eq_abs]
    exact (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right (hB z).2.1 (norm_nonneg _))
  refine ⟨((h2_continuous_per1 hv).comp (continuous_fst.sub continuous_snd)).clm_apply continuous_const,
    fun x y => by simp only [h2_sub_periodic_y (f := h2_per1 v) (h2_per1_periodic v) x y],
    fun x => ⟨B * ‖w‖, fun y => hb _⟩, ⟨B * ‖w‖, fun x y => ?_⟩⟩
  exact (hb _).trans (le_mul_of_one_le_right (by positivity) (by linarith [norm_nonneg (gradient U y)]))

theorem h2_good_A {v : ℝ} (hv : 0 < v) (θ : ℝ) {U : Ch N → ℝ} (hU : ContDiff ℝ 1 U)
    (hUper : ∀ z, U (z + cep_diag N) = U z) {K : ℝ≥0} (hK : LipschitzWith K (gradient U)) :
    H2Good U (fun x y => h2_A θ v U x y) := by
  obtain ⟨B2, hB2, hB⟩ := h2_A_bound hv θ U
  have hgc := h2_continuous_gradient hU
  have hsub : Continuous fun z : Ch N × Ch N => z.1 - z.2 := continuous_fst.sub continuous_snd
  refine ⟨?_, fun x y => ?_, fun x => ?_, ⟨B2, hB⟩⟩
  · unfold h2_A
    refine Continuous.add (continuous_const.mul (continuous_finsetSum _ fun k _ => ?_)) ?_
    · exact (((h2_continuous_per2 hv).comp hsub).clm_apply continuous_const).clm_apply continuous_const
    · exact ((h2_continuous_per1 hv).comp hsub).clm_apply (hgc.comp continuous_snd)
  · show h2_A θ v U x (y + cep_diag N) = h2_A θ v U x y
    unfold h2_A
    rw [h2_sub_periodic_y (f := h2_per2 v) (h2_per2_periodic v) x y,
      h2_sub_periodic_y (f := h2_per1 v) (h2_per1_periodic v) x y, h2_gradient_periodic hUper]
  · obtain ⟨C, hC0, hC⟩ := h2_per_grad_bdd hv hUper hK x
    refine ⟨|θ| * (N * C) + C, fun y => ?_⟩
    obtain ⟨c1, c2, c3⟩ := hC y
    have hg := norm_nonneg (gradient U y)
    have h1g : (1 : ℝ) ≤ 1 + ‖gradient U y‖ := by linarith
    have h2g : ‖gradient U y‖ ≤ 1 + ‖gradient U y‖ := by linarith
    have p2 : ‖h2_per2 v (x - y)‖ ≤ C := (le_mul_of_one_le_right (ContinuousLinearMap.opNorm_nonneg _) h1g).trans c3
    have p1 : ‖h2_per1 v (x - y)‖ * ‖gradient U y‖ ≤ C :=
      (mul_le_mul_of_nonneg_left h2g (norm_nonneg _)).trans c2
    unfold h2_A
    refine le_trans (abs_add_le _ _) (add_le_add ?_ ?_)
    · rw [abs_mul]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      calc ∑ k, |h2_per2 v (x - y) (h2_e k) (h2_e k)| ≤ ∑ _k : Fin N, C := by
            refine Finset.sum_le_sum fun k _ => ?_
            rw [← Real.norm_eq_abs]
            calc ‖h2_per2 v (x - y) (h2_e k) (h2_e k)‖ ≤ ‖h2_per2 v (x - y)‖ * ‖h2_e k‖ * ‖h2_e k‖ :=
                  ContinuousLinearMap.le_opNorm₂ _ _ _
              _ ≤ C := by rw [h2_norm_e]; simpa using p2
        _ = N * C := by simp
    · rw [← Real.norm_eq_abs]
      exact (ContinuousLinearMap.le_opNorm _ _).trans p1

theorem h2_good_B {v : ℝ} (hv : 0 < v) (θ : ℝ) {U : Ch N → ℝ} (hU : ContDiff ℝ 1 U)
    (hUper : ∀ z, U (z + cep_diag N) = U z) {K : ℝ≥0} (hK : LipschitzWith K (gradient U)) {φ : Ch N → ℝ}
    (hφ : ContDiff ℝ 1 φ) {c : ℝ} (hc : 0 ≤ c) (hφc : ∀ x, ‖fderiv ℝ φ x‖ ≤ c) :
    H2Good U (fun x y => h2_B θ v U φ x y) := by
  obtain ⟨B2, hB2, hB⟩ := h2_B_bound hv θ U
  have hgc := h2_continuous_gradient hU
  refine ⟨h2_continuous_B hv hU hφ, fun x y => ?_, fun x => ?_, ⟨c * B2, fun x y => ?_⟩⟩
  · show h2_B θ v U φ x (y + cep_diag N) = h2_B θ v U φ x y
    unfold h2_B
    rw [h2_sub_periodic_y (f := h2_per1 v) (h2_per1_periodic v) x y,
      h2_sub_periodic_y (f := h2_per v) (h2_per_periodic v) x y, h2_gradient_periodic hUper]
  · obtain ⟨C, hC0, hC⟩ := h2_per_grad_bdd hv hUper hK x
    refine ⟨c * (|θ| * (N * C)) + c * C, fun y => ?_⟩
    obtain ⟨c1, c2, c3⟩ := hC y
    have hg := norm_nonneg (gradient U y)
    have h1g : (1 : ℝ) ≤ 1 + ‖gradient U y‖ := by linarith
    have h2g : ‖gradient U y‖ ≤ 1 + ‖gradient U y‖ := by linarith
    have p0 : ‖h2_per v (x - y)‖ * ‖gradient U y‖ ≤ C :=
      (mul_le_mul_of_nonneg_left h2g (norm_nonneg _)).trans c1
    have p1 : ‖h2_per1 v (x - y)‖ ≤ C := (le_mul_of_one_le_right (norm_nonneg _) h1g).trans c2
    unfold h2_B
    refine le_trans (abs_add_le _ _) (add_le_add ?_ ?_)
    · rw [abs_mul]
      calc |θ| * |∑ k, fderiv ℝ φ x (h2_e k) * h2_per1 v (x - y) (h2_e k)|
          ≤ |θ| * ∑ _k : Fin N, c * C := by
            refine mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs _ _).trans
              (Finset.sum_le_sum fun k _ => ?_)) (abs_nonneg _)
            rw [abs_mul]
            refine mul_le_mul ?_ ?_ (abs_nonneg _) hc
            · rw [← Real.norm_eq_abs]
              calc ‖fderiv ℝ φ x (h2_e k)‖ ≤ ‖fderiv ℝ φ x‖ * ‖h2_e k‖ := ContinuousLinearMap.le_opNorm _ _
                _ ≤ c := by rw [h2_norm_e]; simpa using hφc x
            · rw [← Real.norm_eq_abs]
              calc ‖h2_per1 v (x - y) (h2_e k)‖ ≤ ‖h2_per1 v (x - y)‖ * ‖h2_e k‖ := ContinuousLinearMap.le_opNorm _ _
                _ ≤ C := by rw [h2_norm_e]; simpa using p1
        _ = c * (|θ| * (N * C)) := by simp; ring
    · rw [abs_mul]
      calc |fderiv ℝ φ x (gradient U y)| * |h2_per v (x - y)| ≤ (c * ‖gradient U y‖) * ‖h2_per v (x - y)‖ := by
            refine mul_le_mul ?_ ?_ (abs_nonneg _) (by positivity)
            · rw [← Real.norm_eq_abs]
              calc ‖fderiv ℝ φ x (gradient U y)‖ ≤ ‖fderiv ℝ φ x‖ * ‖gradient U y‖ := ContinuousLinearMap.le_opNorm _ _
                _ ≤ c * ‖gradient U y‖ := mul_le_mul_of_nonneg_right (hφc x) hg
            · rw [Real.norm_eq_abs]
        _ = c * (‖h2_per v (x - y)‖ * ‖gradient U y‖) := by ring
        _ ≤ c * C := mul_le_mul_of_nonneg_left p0 hc
  · exact hB φ x y c hc (hφc x)

/-! ### Parametric integrals -/

theorem h2_continuous_integral_x {μ : Measure (Ch N)} [IsFiniteMeasure μ] {U : Ch N → ℝ}
    {H : Ch N → Ch N → ℝ} (hH : H2Good U H) (hG1 : Integrable (fun y => ‖gradient U y‖) μ) :
    Continuous fun x => ∫ y, H x y ∂μ := by
  obtain ⟨hc, -, -, c, hdom⟩ := hH
  exact continuous_of_dominated (bound := fun y => c * (1 + ‖gradient U y‖))
    (fun x => (hc.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
    (fun x => ae_of_all _ fun y => by rw [Real.norm_eq_abs]; exact hdom x y)
    (((integrable_const 1).add hG1).const_mul c)
    (ae_of_all _ fun y => hc.comp (continuous_id.prodMk continuous_const))

theorem h2_continuous_integral_s {μ : ℝ → Measure (Ch N)} (hnar : H2Narrow μ) {U : Ch N → ℝ}
    {H : Ch N → Ch N → ℝ} (hH : H2Good U H) (x : Ch N) : Continuous fun s => ∫ y, H x y ∂μ s :=
  hnar (fun y => H x y) (hH.1.comp (continuous_const.prodMk continuous_id)) (hH.2.1 x) (hH.2.2.1 x)

theorem h2_measurable_param {μ : ℝ → Measure (Ch N)} [∀ s, IsFiniteMeasure (μ s)] (hnar : H2Narrow μ)
    {U : Ch N → ℝ} {H : Ch N → Ch N → ℝ} (hH : H2Good U H)
    (hG1 : ∀ s, Integrable (fun y => ‖gradient U y‖) (μ s)) :
    Measurable (Function.uncurry fun (s : ℝ) (x : Ch N) => ∫ y, H x y ∂μ s) :=
  measurable_uncurry_of_continuous_of_measurable (h2_continuous_integral_s hnar hH)
    (fun s => (h2_continuous_integral_x hH (hG1 s)).measurable)

end

end HRS.MC.CepH2
