import Mathlib

/-!
# Packet K2 (aux 1): real-variable ingredients of the one-sided Lipschitz bound

* monotonicity of `u ↦ π cot (π u)` on each interval `(m, m+1)` in the form used for pairs;
* a global Lipschitz constant for a smooth 1-periodic function;
* the symmetrisation of double sums `∑_i ∑_j δ_i f_ij` with `f_ji = - f_ij`;
* the crude bound `∑_i ∑_j δ_i e_ij ≤ 2 N L ∑ δ_i²` for `|e_ij| ≤ L (|δ_i| + |δ_j|)`.
-/

open Real

noncomputable section

namespace HRS.MC.CepK2

/-- `c u = π cot (π u)` (with Lean's `x / 0 = 0` junk value at the integers). -/
def cepk2_c (u : ℝ) : ℝ := π * (Real.cos (π * u) / Real.sin (π * u))

lemma cepk2_c_neg (u : ℝ) : cepk2_c (-u) = - cepk2_c u := by
  unfold cepk2_c
  rw [mul_neg, Real.cos_neg, Real.sin_neg, div_neg]
  ring

lemma cepk2_c_zero : cepk2_c 0 = 0 := by simp [cepk2_c]

/-- `sin (π t) * t ≥ 0` for `|t| < 1`. -/
lemma cepk2_sin_mul_nonneg {t : ℝ} (h1 : -1 < t) (h2 : t < 1) : 0 ≤ Real.sin (π * t) * t := by
  rcases le_total 0 t with ht | ht
  · have : 0 ≤ Real.sin (π * t) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by positivity) (by nlinarith [Real.pi_pos])
    positivity
  · have : 0 ≤ Real.sin (π * (-t)) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])
    rw [mul_neg, Real.sin_neg] at this
    nlinarith

lemma cepk2_c_pair_pos {u u' : ℝ} (hu0 : 0 < u) (hu1 : u < 1) (hu0' : 0 < u') (hu1' : u' < 1) :
    (u - u') * (cepk2_c u - cepk2_c u') ≤ 0 := by
  have hs : 0 < Real.sin (π * u) :=
    Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith [Real.pi_pos])
  have hs' : 0 < Real.sin (π * u') :=
    Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith [Real.pi_pos])
  have key : cepk2_c u - cepk2_c u' =
      π * Real.sin (π * (u' - u)) / (Real.sin (π * u) * Real.sin (π * u')) := by
    unfold cepk2_c
    rw [mul_sub, Real.sin_sub]
    field_simp
  rw [key]
  have h := cepk2_sin_mul_nonneg (t := u' - u) (by linarith) (by linarith)
  have : (u - u') * (π * Real.sin (π * (u' - u)) / (Real.sin (π * u) * Real.sin (π * u'))) =
      -(π * (Real.sin (π * (u' - u)) * (u' - u)) / (Real.sin (π * u) * Real.sin (π * u'))) := by
    field_simp
    ring
  rw [this]
  have : 0 ≤ π * (Real.sin (π * (u' - u)) * (u' - u)) / (Real.sin (π * u) * Real.sin (π * u')) := by
    positivity
  linarith

/-- Pair monotonicity: if `u, u'` lie in the same unit interval `(0,1)` or `(-1,0)`, then
`(u - u') (c u - c u') ≤ 0`. -/
lemma cepk2_c_pair {u u' : ℝ}
    (h : (0 < u ∧ u < 1 ∧ 0 < u' ∧ u' < 1) ∨ (-1 < u ∧ u < 0 ∧ -1 < u' ∧ u' < 0)) :
    (u - u') * (cepk2_c u - cepk2_c u') ≤ 0 := by
  rcases h with ⟨a, b, c, d⟩ | ⟨a, b, c, d⟩
  · exact cepk2_c_pair_pos a b c d
  · have := cepk2_c_pair_pos (u := -u) (u' := -u') (by linarith) (by linarith) (by linarith)
      (by linarith)
    rw [cepk2_c_neg, cepk2_c_neg] at this
    nlinarith

/-- A smooth 1-periodic function is globally Lipschitz. -/
lemma cepk2_lip_of_periodic {ρ : ℝ → ℝ} (hρ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ)
    (hper : ∀ u, ρ (u + 1) = ρ u) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ u v, |ρ u - ρ v| ≤ L * |u - v| := by
  have hd : Differentiable ℝ ρ := hρ.differentiable (by simp)
  have hc : Continuous (deriv ρ) := hρ.continuous_deriv (by simp)
  have hperd : Function.Periodic (deriv ρ) 1 := by
    intro x
    have : (fun z => ρ (z + 1)) = ρ := funext hper
    have h2 := deriv_comp_add_const (f := ρ) (a := (1 : ℝ)) (x := x)
    rw [← h2]
    rw [this]
  have hcomp := hperd.compact_of_continuous one_ne_zero hc
  obtain ⟨C, hC⟩ := hcomp.isBounded.exists_norm_le
  have hC' : ∀ x, ‖deriv ρ x‖ ≤ C := fun x => hC _ ⟨x, rfl⟩
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC' 0)
  refine ⟨C, hC0, fun u v => ?_⟩
  have hl : LipschitzWith (Real.toNNReal C) ρ :=
    lipschitzWith_of_nnnorm_deriv_le hd (fun x => by
      rw [← NNReal.coe_le_coe]
      simpa [Real.coe_toNNReal _ hC0] using hC' x)
  have := hl.dist_le_mul u v
  simpa [Real.dist_eq, Real.coe_toNNReal _ hC0] using this

/-- Symmetrisation: if `f j i = - f i j` and `(δ i - δ j) f i j ≤ 0`, then `∑_i ∑_j δ i f i j ≤ 0`. -/
lemma cepk2_sum_antisym {N : ℕ} (δ : Fin N → ℝ) (f : Fin N → Fin N → ℝ)
    (hanti : ∀ i j, f j i = - f i j) (hle : ∀ i j, (δ i - δ j) * f i j ≤ 0) :
    ∑ i, ∑ j, δ i * f i j ≤ 0 := by
  have h1 : ∑ i, ∑ j, δ i * f i j = ∑ i, ∑ j, δ j * f j i := Finset.sum_comm
  have h2 : ∑ i, ∑ j, δ j * f j i = ∑ i, ∑ j, -(δ j * f i j) := by
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hanti]; ring
  have h3 : 2 * ∑ i, ∑ j, δ i * f i j = ∑ i, ∑ j, (δ i - δ j) * f i j := by
    have : ∑ i, ∑ j, (δ i - δ j) * f i j =
        ∑ i, ∑ j, δ i * f i j + ∑ i, ∑ j, -(δ j * f i j) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [this, ← h2, ← h1]; ring
  have h4 : ∑ i, ∑ j, (δ i - δ j) * f i j ≤ 0 :=
    Finset.sum_nonpos fun i _ => Finset.sum_nonpos fun j _ => hle i j
  linarith

/-- The Lipschitz-type part: `∑_i ∑_j δ_i e_ij ≤ 2 N L ∑ δ_i²` if `|e_ij| ≤ L (|δ_i| + |δ_j|)`. -/
lemma cepk2_sum_lip {N : ℕ} (δ : Fin N → ℝ) (e : Fin N → Fin N → ℝ) {L : ℝ} (hL : 0 ≤ L)
    (he : ∀ i j, |e i j| ≤ L * (|δ i| + |δ j|)) :
    ∑ i, ∑ j, δ i * e i j ≤ 2 * N * L * ∑ i, δ i ^ 2 := by
  have hterm : ∀ i j, δ i * e i j ≤ L * ((3 / 2) * δ i ^ 2 + (1 / 2) * δ j ^ 2) := by
    intro i j
    have h1 : δ i * e i j ≤ |δ i| * |e i j| := by
      rw [← abs_mul]; exact le_abs_self _
    have h2 : |δ i| * |e i j| ≤ |δ i| * (L * (|δ i| + |δ j|)) :=
      mul_le_mul_of_nonneg_left (he i j) (abs_nonneg _)
    have h3 : |δ i| * |δ j| ≤ (δ i ^ 2 + δ j ^ 2) / 2 := by
      nlinarith [sq_abs (δ i), sq_abs (δ j), sq_nonneg (|δ i| - |δ j|)]
    have h4 : |δ i| * |δ i| = δ i ^ 2 := by rw [← sq, sq_abs]
    nlinarith
  calc ∑ i, ∑ j, δ i * e i j ≤ ∑ i, ∑ j : Fin N, L * ((3 / 2) * δ i ^ 2 + (1 / 2) * δ j ^ 2) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hterm i j
    _ = 2 * N * L * ∑ i, δ i ^ 2 := by
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, nsmul_eq_mul]
        ring

end HRS.MC.CepK2
