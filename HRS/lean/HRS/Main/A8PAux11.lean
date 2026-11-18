import HRS.Main.A8PAux10

/-!
# Packet A8P, part 11: the deterministic covariance density `Σ̄` (measurable, nonnegative, bounded)
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators MeasureTheory

namespace HRS.Main.A8P

open HRS.GF HRS.Uniform

local notation "ℝ^" p => EuclideanSpace ℝ (Fin p)

variable {d q : ℕ}

theorem a8p_s1Norm_le_sum (Q : Matrix (Fin q) (Fin q) ℝ) : s1Norm Q ≤ ∑ a, ∑ b, |Q a b| := by
  unfold s1Norm traceNormMatrix
  refine ciSup_le fun U => ?_
  have hU : ∀ a b, |(U : Matrix (Fin q) (Fin q) ℝ) a b| ≤ 1 := by
    intro a b
    have h1 := (Matrix.mem_orthogonalGroup_iff (Fin q) ℝ).1 U.2
    have h2 := congrFun (congrFun h1 a) a
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply_eq] at h2
    have h3 : ((U : Matrix (Fin q) (Fin q) ℝ) a b) ^ 2 ≤ 1 := by
      calc ((U : Matrix (Fin q) (Fin q) ℝ) a b) ^ 2 ≤ ∑ c, (U : Matrix (Fin q) (Fin q) ℝ) a c * (U : Matrix (Fin q) (Fin q) ℝ) a c := by
            have := Finset.single_le_sum (f := fun c => (U : Matrix (Fin q) (Fin q) ℝ) a c * (U : Matrix (Fin q) (Fin q) ℝ) a c)
              (fun c _ => mul_self_nonneg _) (Finset.mem_univ b)
            simpa [sq] using this
        _ = 1 := h2
    nlinarith [abs_nonneg ((U : Matrix (Fin q) (Fin q) ℝ) a b), sq_abs ((U : Matrix (Fin q) (Fin q) ℝ) a b)]
  have htr : Matrix.trace (Q.transpose * (U : Matrix (Fin q) (Fin q) ℝ)) =
      ∑ a, ∑ b, Q a b * (U : Matrix (Fin q) (Fin q) ℝ) a b := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply]
    rw [Finset.sum_comm]
  rw [htr]
  refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_
  calc Q a b * (U : Matrix (Fin q) (Fin q) ℝ) a b ≤ |Q a b * (U : Matrix (Fin q) (Fin q) ℝ) a b| := le_abs_self _
    _ = |Q a b| * |(U : Matrix (Fin q) (Fin q) ℝ) a b| := abs_mul _ _
    _ ≤ |Q a b| * 1 := mul_le_mul_of_nonneg_left (hU a b) (abs_nonneg _)
    _ = |Q a b| := mul_one _


/-- The deterministic covariance density `Σ̄_r^{ab} = 1_{0 ≤ r < min(t_a,t_b)} c ∫ ⟨G_a(r),G_b(r)⟩ ρ_r`. -/
def a8pSigBar (ts : Fin q → ℝ) (G : Fin q → ℝ → Torus d → Euc d) (ρ : ℝ → Torus d → ℝ) (c : ℝ)
    (r : ℝ) : Matrix (Fin q) (Fin q) ℝ :=
  Matrix.of fun a b => if 0 ≤ r ∧ r < min (ts a) (ts b) then
    c * ∫ x, inner ℝ (G a r x) (G b r x) * ρ r x else 0

section SigBar

variable {ts : Fin q → ℝ} {G : Fin q → ℝ → Torus d → Euc d} {ρ : ℝ → Torus d → ℝ} {c : ℝ}

theorem a8p_sigBar_integrand_meas (hGm : ∀ a, Measurable fun p : ℝ × Torus d => G a p.1 p.2)
    (hρm : Measurable fun p : ℝ × Torus d => ρ p.1 p.2) (a b : Fin q) :
    Measurable fun p : ℝ × Torus d => inner ℝ (G a p.1 p.2) (G b p.1 p.2) * ρ p.1 p.2 :=
  ((hGm a).inner (hGm b)).mul hρm

theorem a8p_sigBar_integrable (hGm : ∀ a, Measurable fun p : ℝ × Torus d => G a p.1 p.2)
    (hρm : Measurable fun p : ℝ × Torus d => ρ p.1 p.2) {B Λ : ℝ} (hGb : ∀ a r x, ‖G a r x‖ ≤ B)
    (hρ0 : ∀ r x, 0 ≤ ρ r x) (hρb : ∀ r x, ρ r x ≤ Λ) (a b : Fin q) (r : ℝ) :
    Integrable (fun x => inner ℝ (G a r x) (G b r x) * ρ r x) := by
  refine Integrable.of_bound (C := B * B * Λ)
    ((a8p_sigBar_integrand_meas hGm hρm a b).comp measurable_prodMk_left).aestronglyMeasurable
    (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hρ0 r x)]
  have h1 : |inner ℝ (G a r x) (G b r x)| ≤ B * B :=
    (abs_real_inner_le_norm _ _).trans (mul_le_mul (hGb a r x) (hGb b r x) (norm_nonneg _)
      ((norm_nonneg _).trans (hGb a r x)))
  exact mul_le_mul h1 (hρb r x) (hρ0 r x) ((abs_nonneg _).trans h1)

theorem a8p_sigBar_entry_bound (hGm : ∀ a, Measurable fun p : ℝ × Torus d => G a p.1 p.2)
    (hρm : Measurable fun p : ℝ × Torus d => ρ p.1 p.2) {B Λ : ℝ} (hGb : ∀ a r x, ‖G a r x‖ ≤ B)
    (hρ0 : ∀ r x, 0 ≤ ρ r x) (hρb : ∀ r x, ρ r x ≤ Λ) (a b : Fin q) (r : ℝ) :
    |a8pSigBar ts G ρ c r a b| ≤ |c| * (B * B * Λ) := by
  unfold a8pSigBar
  simp only [Matrix.of_apply]
  split_ifs with h
  · rw [abs_mul]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    refine (abs_integral_le_integral_abs).trans ?_
    have hbd : ∀ x, |inner ℝ (G a r x) (G b r x) * ρ r x| ≤ B * B * Λ := by
      intro x
      rw [abs_mul, abs_of_nonneg (hρ0 r x)]
      have h1 : |inner ℝ (G a r x) (G b r x)| ≤ B * B :=
        (abs_real_inner_le_norm _ _).trans (mul_le_mul (hGb a r x) (hGb b r x) (norm_nonneg _)
          ((norm_nonneg _).trans (hGb a r x)))
      exact mul_le_mul h1 (hρb r x) (hρ0 r x) ((abs_nonneg _).trans h1)
    calc ∫ x, |inner ℝ (G a r x) (G b r x) * ρ r x| ≤ ∫ _x : Torus d, B * B * Λ :=
          integral_mono_of_nonneg (Eventually.of_forall fun x => abs_nonneg _) (integrable_const _)
            (Eventually.of_forall hbd)
      _ = B * B * Λ := by simp
  · simp only [abs_zero]
    have hB : 0 ≤ B := (norm_nonneg _).trans (hGb a r (0 : Torus d))
    have hΛ : 0 ≤ Λ := (hρ0 r (0 : Torus d)).trans (hρb r (0 : Torus d))
    positivity


theorem a8p_sigBar_entry_meas (hGm : ∀ a, Measurable fun p : ℝ × Torus d => G a p.1 p.2)
    (hρm : Measurable fun p : ℝ × Torus d => ρ p.1 p.2) (a b : Fin q) :
    Measurable fun r => a8pSigBar ts G ρ c r a b := by
  have hI : Measurable fun r : ℝ => ∫ x, inner ℝ (G a r x) (G b r x) * ρ r x := by
    have hsm : StronglyMeasurable fun p : ℝ × Torus d => inner ℝ (G a p.1 p.2) (G b p.1 p.2) * ρ p.1 p.2 :=
      (a8p_sigBar_integrand_meas hGm hρm a b).stronglyMeasurable
    exact (hsm.integral_prod_right' (ν := (volume : Measure (Torus d)))).measurable
  unfold a8pSigBar
  simp only [Matrix.of_apply]
  refine Measurable.ite ?_ (measurable_const.mul hI) measurable_const
  exact (measurableSet_le measurable_const measurable_id).inter (measurableSet_lt measurable_id measurable_const)

theorem a8p_sigBar_meas (hGm : ∀ a, Measurable fun p : ℝ × Torus d => G a p.1 p.2)
    (hρm : Measurable fun p : ℝ × Torus d => ρ p.1 p.2) : Measurable (a8pSigBar ts G ρ c) :=
  measurable_pi_iff.2 fun a => measurable_pi_iff.2 fun b => a8p_sigBar_entry_meas hGm hρm a b

theorem a8p_sigBar_psd (hGm : ∀ a, Measurable fun p : ℝ × Torus d => G a p.1 p.2)
    (hρm : Measurable fun p : ℝ × Torus d => ρ p.1 p.2) {B Λ : ℝ} (hGb : ∀ a r x, ‖G a r x‖ ≤ B)
    (hρ0 : ∀ r x, 0 ≤ ρ r x) (hρb : ∀ r x, ρ r x ≤ Λ) (hc : 0 ≤ c) (r : ℝ) :
    (a8pSigBar ts G ρ c r).PosSemidef := by
  by_cases hr : 0 ≤ r
  swap
  · have : a8pSigBar ts G ρ c r = 0 := by
      ext a b
      simp [a8pSigBar, hr]
    rw [this]
    exact Matrix.PosSemidef.zero
  set g : Fin q → Torus d → Euc d := fun a x => if r < ts a then G a r x else 0 with hg
  have hent : ∀ a b, a8pSigBar ts G ρ c r a b = c * ∫ x, inner ℝ (g a x) (g b x) * ρ r x := by
    intro a b
    unfold a8pSigBar
    simp only [Matrix.of_apply, hg]
    by_cases h1 : r < ts a
    · by_cases h2 : r < ts b
      · simp only [h1, h2, if_true, if_pos (show 0 ≤ r ∧ r < min (ts a) (ts b) from ⟨hr, lt_min h1 h2⟩)]
      · have : ¬ (0 ≤ r ∧ r < min (ts a) (ts b)) := fun h => h2 (lt_of_lt_of_le h.2 (min_le_right _ _))
        simp [h2, this]
    · have : ¬ (0 ≤ r ∧ r < min (ts a) (ts b)) := fun h => h1 (lt_of_lt_of_le h.2 (min_le_left _ _))
      simp [h1, this]
  have hgm : ∀ a, Measurable (g a) := by
    intro a
    by_cases h : r < ts a
    · simp only [hg, if_pos h]; exact (hGm a).comp measurable_prodMk_left
    · simp only [hg, if_neg h]; exact measurable_const
  have hgb : ∀ a x, ‖g a x‖ ≤ B := by
    intro a x
    by_cases h : r < ts a
    · simp only [hg, if_pos h]; exact hGb a r x
    · simp only [hg, if_neg h, norm_zero]
      exact (norm_nonneg _).trans (hGb a r (0 : Torus d))
  have hint : ∀ a b, Integrable (fun x => inner ℝ (g a x) (g b x) * ρ r x) := by
    intro a b
    refine Integrable.of_bound (C := B * B * Λ) (((hgm a).inner (hgm b)).mul
      (hρm.comp measurable_prodMk_left)).aestronglyMeasurable (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hρ0 r x)]
    have h1 : |inner ℝ (g a x) (g b x)| ≤ B * B :=
      (abs_real_inner_le_norm _ _).trans (mul_le_mul (hgb a x) (hgb b x) (norm_nonneg _)
        ((norm_nonneg _).trans (hgb a x)))
    exact mul_le_mul h1 (hρb r x) (hρ0 r x) ((abs_nonneg _).trans h1)
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
  · refine Matrix.IsHermitian.ext fun a b => ?_
    have hsym : ∀ y, inner ℝ (g b y) (g a y) = inner ℝ (g a y) (g b y) := fun y => real_inner_comm _ _
    simp only [star_trivial, hent, hsym]
  · simp only [star_trivial, dotProduct, Matrix.mulVec, hent]
    have e1 : ∀ a b, x a * (c * ∫ y, inner ℝ (g a y) (g b y) * ρ r y) * x b =
        c * ∫ y, (x a * x b) * (inner ℝ (g a y) (g b y) * ρ r y) := by
      intro a b
      rw [integral_const_mul]; ring
    have e2 : ∑ a, x a * ∑ b, c * (∫ y, inner ℝ (g a y) (g b y) * ρ r y) * x b =
        c * ∫ y, ∑ a, ∑ b, (x a * x b) * (inner ℝ (g a y) (g b y) * ρ r y) := by
      rw [integral_finsetSum _ (fun a _ => integrable_finsetSum _ fun b _ => (hint a b).const_mul _)]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [integral_finsetSum _ (fun b _ => (hint a b).const_mul _), Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [integral_const_mul]; ring
    rw [e2]
    refine mul_nonneg hc (integral_nonneg fun y => ?_)
    have : ∑ a, ∑ b, (x a * x b) * (inner ℝ (g a y) (g b y) * ρ r y) =
        ‖∑ a, x a • g a y‖ ^ 2 * ρ r y := by
      rw [← real_inner_self_eq_norm_sq, sum_inner, Finset.sum_mul]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [inner_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [real_inner_smul_left, real_inner_smul_right]; ring
    rw [this]
    exact mul_nonneg (sq_nonneg _) (hρ0 r y)

theorem a8p_sigBar_isDet (hGm : ∀ a, Measurable fun p : ℝ × Torus d => G a p.1 p.2)
    (hρm : Measurable fun p : ℝ × Torus d => ρ p.1 p.2) {B Λ : ℝ} (hGb : ∀ a r x, ‖G a r x‖ ≤ B)
    (hρ0 : ∀ r x, 0 ≤ ρ r x) (hρb : ∀ r x, ρ r x ≤ Λ) (hc : 0 ≤ c) (T : ℝ) :
    IsDetCovMatrix T (a8pSigBar ts G ρ c) := by
  refine ⟨a8p_sigBar_meas hGm hρm, fun σ _ => a8p_sigBar_psd hGm hρm hGb hρ0 hρb hc σ, ?_⟩
  have hm : Measurable fun σ => s1Norm (a8pSigBar ts G ρ c σ) :=
    measurable_traceNormMatrix (a8pSigBar ts G ρ c) (fun i j => a8p_sigBar_entry_meas hGm hρm i j)
  refine Integrable.mono' (g := fun _ => ∑ _a : Fin q, ∑ _b : Fin q, |c| * (B * B * Λ))
    (integrable_const _) hm.aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall fun σ _ => ?_)
  rw [Real.norm_of_nonneg (traceNormMatrix_nonneg _)]
  exact (a8p_s1Norm_le_sum _).trans (Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ =>
    a8p_sigBar_entry_bound hGm hρm hGb hρ0 hρb a b σ)

end SigBar

end HRS.Main.A8P
