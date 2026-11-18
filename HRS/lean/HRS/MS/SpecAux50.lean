import Mathlib

/-!
# S8R: summability facts for the spectral data (S8.7, coupling block C3)

Namespace `HRS.MS.Spec`, helper prefix `s8p_`.  For `om l ≥ c (l+1)^{1/d}` (the `growth` field of `IsSpectralData`):

* `s8p_summable_exp_growth`: `∑ exp(-κ om_l) < ∞` for `κ > 0`;
* `s8p_summable_mul_exp_growth`: `∑ om_l exp(-κ om_l) < ∞` for `κ > 0`;
* `s8p_tsum_prod_exp`: the double sum `∑_{l,j} exp(-κ(om_l+om_j)) = (∑_l exp(-κ om_l))²` in `ℝ≥0∞`.
-/

noncomputable section

open Filter Topology
open scoped ENNReal

namespace HRS.MS.Spec

/-- `x e^{-κ x} ≤ (2/κ) e^{-κ x/2}` for `x ≥ 0`, `κ > 0`. -/
theorem s8p_mul_exp_le {κ x : ℝ} (hκ : 0 < κ) (hx : 0 ≤ x) :
    x * Real.exp (-κ * x) ≤ (2 / κ) * Real.exp (-κ * x / 2) := by
  have h1 : κ * x / 2 ≤ Real.exp (κ * x / 2) := by
    have := Real.add_one_le_exp (κ * x / 2)
    linarith
  have h2 : Real.exp (-κ * x) = Real.exp (-κ * x / 2) * Real.exp (-κ * x / 2) := by
    rw [← Real.exp_add]; congr 1; ring
  have h3 : Real.exp (κ * x / 2) * Real.exp (-κ * x / 2) = 1 := by
    rw [← Real.exp_add]
    have : κ * x / 2 + -κ * x / 2 = 0 := by ring
    rw [this]; simp
  have hpos : 0 < Real.exp (-κ * x / 2) := Real.exp_pos _
  calc x * Real.exp (-κ * x) = (2 / κ) * (κ * x / 2) * Real.exp (-κ * x / 2) *
        Real.exp (-κ * x / 2) := by rw [h2]; field_simp
    _ ≤ (2 / κ) * Real.exp (κ * x / 2) * Real.exp (-κ * x / 2) * Real.exp (-κ * x / 2) := by
        gcongr
    _ = (2 / κ) * Real.exp (-κ * x / 2) := by
        rw [mul_assoc (2 / κ), h3]; ring

theorem s8p_summable_exp_growth {d : ℕ} (hd : 1 ≤ d) {c : ℝ} (hc : 0 < c) {om : ℕ → ℝ}
    (hg : ∀ l : ℕ, c * ((l : ℝ) + 1) ^ (1 / (d : ℝ)) ≤ om l) {κ : ℝ} (hκ : 0 < κ) :
    Summable fun l => Real.exp (-κ * om l) := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  set k : ℕ := 2 * d with hk
  have hbase : Summable fun l : ℕ => ((l : ℝ) + 1) ^ (-(2 : ℝ)) := by
    have := (Real.summable_nat_rpow (p := -(2 : ℝ))).2 (by norm_num)
    exact (summable_nat_add_iff 1).2 this |>.congr fun l => by push_cast; rfl
  refine Summable.of_nonneg_of_le (fun l => (Real.exp_pos _).le) (fun l => ?_)
    (hbase.mul_left (Nat.factorial k / (κ * c) ^ k))
  set y : ℝ := ((l : ℝ) + 1) ^ (1 / (d : ℝ)) with hy
  have hl1 : (0 : ℝ) < (l : ℝ) + 1 := by positivity
  have hy0 : 0 < y := Real.rpow_pos_of_pos hl1 _
  have hyk : y ^ k = ((l : ℝ) + 1) ^ (2 : ℝ) := by
    rw [hy, ← Real.rpow_natCast, ← Real.rpow_mul hl1.le]
    congr 1
    rw [hk]; push_cast
    field_simp
  have hx : κ * c * y ≤ κ * om l := by nlinarith [hg l]
  have hx0 : 0 < κ * c * y := by positivity
  have h1 : Real.exp (-κ * om l) ≤ Real.exp (-(κ * c * y)) := Real.exp_le_exp.2 (by linarith)
  have h2 : (κ * c * y) ^ k / (Nat.factorial k) ≤ Real.exp (κ * c * y) :=
    Real.pow_div_factorial_le_exp _ hx0.le k
  have hfac : (0 : ℝ) < Nat.factorial k := by exact_mod_cast Nat.factorial_pos k
  have h3 : Real.exp (-(κ * c * y)) ≤ Nat.factorial k / (κ * c * y) ^ k := by
    rw [Real.exp_neg, inv_eq_one_div, div_le_div_iff₀ (Real.exp_pos _) (by positivity)]
    rw [div_le_iff₀ hfac] at h2
    nlinarith
  refine h1.trans (h3.trans (le_of_eq ?_))
  rw [mul_pow, hyk, Real.rpow_neg hl1.le, Real.rpow_two]
  field_simp

theorem s8p_summable_mul_exp_growth {d : ℕ} (hd : 1 ≤ d) {c : ℝ} (hc : 0 < c) {om : ℕ → ℝ}
    (hg : ∀ l : ℕ, c * ((l : ℝ) + 1) ^ (1 / (d : ℝ)) ≤ om l) (hom : ∀ l, 0 ≤ om l) {κ : ℝ}
    (hκ : 0 < κ) : Summable fun l => om l * Real.exp (-κ * om l) := by
  have hs := (s8p_summable_exp_growth hd hc hg (half_pos hκ)).mul_left (2 / κ)
  refine Summable.of_nonneg_of_le (fun l => mul_nonneg (hom l) (Real.exp_pos _).le)
    (fun l => ?_) hs
  have := s8p_mul_exp_le hκ (hom l)
  have e : -κ * om l / 2 = -(κ / 2) * om l := by ring
  rw [e] at this
  exact this

theorem s8p_tsum_prod_exp {om : ℕ → ℝ} {κ : ℝ} :
    ∑' p : ℕ × ℕ, ENNReal.ofReal (Real.exp (-κ * (om p.1 + om p.2))) =
      (∑' l, ENNReal.ofReal (Real.exp (-κ * om l))) ^ 2 := by
  rw [ENNReal.tsum_prod (f := fun l j => ENNReal.ofReal (Real.exp (-κ * (om l + om j)))), sq,
    ← ENNReal.tsum_mul_right]
  refine tsum_congr fun l => ?_
  rw [← ENNReal.tsum_mul_left]
  refine tsum_congr fun j => ?_
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
  congr 2
  ring

theorem s8p_tsum_exp_lt_top {d : ℕ} (hd : 1 ≤ d) {c : ℝ} (hc : 0 < c) {om : ℕ → ℝ}
    (hg : ∀ l : ℕ, c * ((l : ℝ) + 1) ^ (1 / (d : ℝ)) ≤ om l) {κ : ℝ} (hκ : 0 < κ) :
    ∑' l, ENNReal.ofReal (Real.exp (-κ * om l)) < ⊤ := by
  have hs := s8p_summable_exp_growth hd hc hg hκ
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun l => (Real.exp_pos _).le) hs]
  exact ENNReal.ofReal_lt_top

end HRS.MS.Spec
