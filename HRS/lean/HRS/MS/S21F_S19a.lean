import HRS.MS.S21F_S05
import HRS.MS.S21F_D02

/-!
# S21F, packet R26-T3.S19 (part a): polynomial moments of the actual reference and of `μ₀^{⊗N}`

(i) `‖x‖^m ∈ L¹(μ₀)` for every `m` (Gaussian bound of the `TcRef` datum); (ii) `(1+∑‖X_i‖)^m ≤ (N+1)^m (1+∑‖X_i‖^m)`;
(iii) `((1+∑‖X_i‖)^k)² ∈ L¹(μ₀^{⊗N})`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set InformationTheory
open scoped ENNReal NNReal BigOperators
open HRS HRS.Whole

namespace HRS.MS.R26T3

theorem s21f_poly_gauss {d : ℕ} {c : ℝ} (hc : 0 < c) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : Euc d, ‖x‖ ^ m * Real.exp (-c * ‖x‖ ^ 2) ≤ C * Real.exp (-(c / 2) * ‖x‖ ^ 2) := by
  have hc2 : 0 < c / 2 := by positivity
  refine ⟨1 + m.factorial * (1 / (c / 2)) ^ m, by positivity, fun x => ?_⟩
  set t := ‖x‖ with ht
  have ht0 : 0 ≤ t := norm_nonneg x
  have h1 : t ^ m ≤ 1 + t ^ (2 * m) := by
    rcases le_total t 1 with h | h
    · have := pow_le_one₀ ht0 h (n := m); linarith [pow_nonneg ht0 (2 * m)]
    · have := pow_le_pow_right₀ h (show m ≤ 2 * m by omega); linarith
  have h2 : t ^ (2 * m) ≤ m.factorial * (1 / (c / 2)) ^ m * Real.exp ((c / 2) * t ^ 2) := by
    have := Real.pow_div_factorial_le_exp ((c / 2) * t ^ 2) (by positivity) m
    rw [div_le_iff₀ (by positivity)] at this
    have e : ((c / 2) * t ^ 2) ^ m = (c / 2) ^ m * t ^ (2 * m) := by rw [mul_pow, ← pow_mul]
    rw [e] at this
    have hcm : 0 < (c / 2) ^ m := by positivity
    have h3 : t ^ (2 * m) ≤ Real.exp ((c / 2) * t ^ 2) * m.factorial / (c / 2) ^ m := by
      rw [le_div_iff₀ hcm]; nlinarith
    calc t ^ (2 * m) ≤ Real.exp ((c / 2) * t ^ 2) * m.factorial / (c / 2) ^ m := h3
      _ = m.factorial * (1 / (c / 2)) ^ m * Real.exp ((c / 2) * t ^ 2) := by
          rw [one_div, inv_pow]; field_simp
  have e1 : Real.exp (-c * t ^ 2) = Real.exp (-(c / 2) * t ^ 2) * Real.exp (-(c / 2) * t ^ 2) := by
    rw [← Real.exp_add]; ring_nf
  have e2 : Real.exp ((c / 2) * t ^ 2) * Real.exp (-(c / 2) * t ^ 2) = 1 := by
    rw [← Real.exp_add]; simp
  have hE : 0 < Real.exp (-(c / 2) * t ^ 2) := Real.exp_pos _
  have hE1 : Real.exp (-(c / 2) * t ^ 2) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg t])
  set A : ℝ := m.factorial * (1 / (c / 2)) ^ m with hA
  have hA0 : 0 ≤ A := by positivity
  calc t ^ m * Real.exp (-c * t ^ 2) ≤ (1 + A * Real.exp ((c / 2) * t ^ 2)) * Real.exp (-c * t ^ 2) :=
        mul_le_mul_of_nonneg_right (h1.trans (by linarith)) (Real.exp_pos _).le
    _ = Real.exp (-(c / 2) * t ^ 2) * Real.exp (-(c / 2) * t ^ 2) +
        A * (Real.exp ((c / 2) * t ^ 2) * Real.exp (-(c / 2) * t ^ 2)) * Real.exp (-(c / 2) * t ^ 2) := by
        rw [e1]; ring
    _ = Real.exp (-(c / 2) * t ^ 2) * Real.exp (-(c / 2) * t ^ 2) + A * Real.exp (-(c / 2) * t ^ 2) := by
        rw [e2]; ring
    _ ≤ (1 + A) * Real.exp (-(c / 2) * t ^ 2) := by nlinarith

theorem s21f_pow_sum_le {N : ℕ} (a : Fin N → ℝ) (ha : ∀ i, 0 ≤ a i) (m : ℕ) :
    (1 + ∑ i, a i) ^ m ≤ ((N : ℝ) + 1) ^ m * (1 + ∑ i, a i ^ m) := by
  rcases m with _ | n
  · simp
  · have hf : ∀ o ∈ (Finset.univ : Finset (Option (Fin N))), 0 ≤ (fun o : Option (Fin N) => o.elim 1 a) o :=
      fun o _ => by cases o <;> simp [ha]
    have h := pow_sum_le_card_mul_sum_pow hf n
    have hs : ∑ o : Option (Fin N), (fun o : Option (Fin N) => o.elim (1 : ℝ) a) o = 1 + ∑ i, a i := by
      simp [Fintype.sum_option]
    have hs2 : ∑ o : Option (Fin N), (fun o : Option (Fin N) => o.elim (1 : ℝ) a) o ^ (n + 1) =
        1 + ∑ i, a i ^ (n + 1) := by
      simp [Fintype.sum_option]
    rw [hs, hs2] at h
    have hcard : ((Finset.univ : Finset (Option (Fin N))).card : ℝ) = (N : ℝ) + 1 := by
      simp
    rw [hcard] at h
    refine h.trans ?_
    have h1 : ((N : ℝ) + 1) ^ n ≤ ((N : ℝ) + 1) ^ (n + 1) :=
      pow_le_pow_right₀ (by linarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]) (Nat.le_succ n)
    have h2 : 0 ≤ 1 + ∑ i, a i ^ (n + 1) := by
      have := Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) => pow_nonneg (ha i) (n + 1); linarith
    exact mul_le_mul_of_nonneg_right h1 h2

theorem s21f_moment_mu {d : ℕ} {ρ : Euc d → ℝ} {M₀ c S : ℝ} {N : ℕ} (hTc : HRS.MS.TcDefs.TcRef d ρ M₀ c S N)
    (hc : 0 < c) (m : ℕ) : Integrable (fun x : Euc d => ‖x‖ ^ m) (HRS.Whole.withDensityReal ρ) := by
  rw [HRS.MS.TcF.tc4_integrable_iff hTc.prob]
  obtain ⟨C, hC0, hC⟩ := s21f_poly_gauss (d := d) hc m
  refine ((HRS.MS.TcF.tc4_integrable_gauss (d := d) (half_pos hc)).const_mul (|M₀| * C)).mono' ?_
    (Eventually.of_forall fun y => ?_)
  · exact (hTc.prob.measurable.mul (measurable_norm.pow_const m)).aestronglyMeasurable
  · rw [Real.norm_of_nonneg (mul_nonneg (hTc.prob.nonneg y) (by positivity))]
    calc ρ y * ‖y‖ ^ m ≤ (M₀ * Real.exp (-c * ‖y‖ ^ 2)) * ‖y‖ ^ m :=
          mul_le_mul_of_nonneg_right (hTc.gauss y) (by positivity)
      _ ≤ (|M₀| * Real.exp (-c * ‖y‖ ^ 2)) * ‖y‖ ^ m :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _) (Real.exp_pos _).le)
            (by positivity)
      _ = |M₀| * (‖y‖ ^ m * Real.exp (-c * ‖y‖ ^ 2)) := by ring
      _ ≤ |M₀| * (C * Real.exp (-(c / 2) * ‖y‖ ^ 2)) :=
          mul_le_mul_of_nonneg_left (hC y) (abs_nonneg _)
      _ = |M₀| * C * Real.exp (-(c / 2) * ‖y‖ ^ 2) := by ring

theorem s21f_config_sq {d N : ℕ} {μ : Measure (Euc d)} [IsProbabilityMeasure μ]
    (hm : ∀ m : ℕ, Integrable (fun x : Euc d => ‖x‖ ^ m) μ) (k : ℕ) :
    Integrable (fun X : EucConfig d N => ((1 + ∑ i, ‖X i‖) ^ k) ^ 2) (Measure.pi fun _ : Fin N => μ) := by
  have hb : Integrable (fun X : EucConfig d N => ((N : ℝ) + 1) ^ (2 * k) * (1 + ∑ i, ‖X i‖ ^ (2 * k)))
      (Measure.pi fun _ : Fin N => μ) := by
    refine Integrable.const_mul ((integrable_const _).add (integrable_finset_sum _ fun i _ => ?_)) _
    exact integrable_comp_eval (μ := fun _ : Fin N => μ) (i := i) (f := fun x : Euc d => ‖x‖ ^ (2 * k)) (hm _)
  refine hb.mono' ?_ (Eventually.of_forall fun X => ?_)
  · refine ((measurable_const.add (Finset.measurable_sum _ fun i _ =>
      (measurable_norm.comp (measurable_pi_apply i)))).pow_const k).pow_const 2 |>.aestronglyMeasurable
  · rw [Real.norm_of_nonneg (sq_nonneg _), ← pow_mul, mul_comm k 2]
    exact s21f_pow_sum_le (fun i => ‖X i‖) (fun i => norm_nonneg _) (2 * k)

end HRS.MS.R26T3
