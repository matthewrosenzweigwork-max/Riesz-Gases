import HRS.Whole.Thermal
import HRS.MS.LogBnd

/-!
# C-STE, part 1: the spherical bound `HasSphericalBound` for the logarithmic thermal density

From `logThermal_bounds_proof` (`ρ ≤ C (1+|x|²)^{β/2} e^{-βa|x|²/2}`) and the elementary bound
`(1+t)^{β/2+d} e^{-βat/2} ≤ K` for `t ≥ 0`.  Also records the pointwise bound
`ρ ≤ A (1+|x|²)^{-d}` for all `x` (used by the stereographic pushforward bound).
No statement is adjusted.
-/

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace HRS.MS.Thm

open HRS.Whole

variable {d : ℕ}

/-- `y^p ≤ (p/c)^p e^{-p} e^{c y}` for `y ≥ 0`, `p ≥ 0`, `c > 0`. -/
lemma ste_rpow_le_exp {p c y : ℝ} (hp : 0 ≤ p) (hc : 0 < c) (hy : 0 ≤ y) :
    y ^ p ≤ (p / c) ^ p * Real.exp (-p) * Real.exp (c * y) := by
  by_cases hp0 : p = 0
  · subst hp0; simpa using Real.one_le_exp (mul_nonneg hc.le hy)
  have hp' : 0 < p := lt_of_le_of_ne hp (Ne.symm hp0)
  have hw : 0 ≤ c * y / p := by positivity
  have h1 : c * y / p ≤ Real.exp (c * y / p - 1) := by
    have := Real.add_one_le_exp (c * y / p - 1)
    linarith
  have h2 : (c * y / p) ^ p ≤ (Real.exp (c * y / p - 1)) ^ p :=
    Real.rpow_le_rpow hw h1 hp
  rw [← Real.exp_mul] at h2
  have h3 : (c * y / p) ^ p = (c / p) ^ p * y ^ p := by
    rw [show c * y / p = (c / p) * y by ring]
    exact Real.mul_rpow (by positivity) hy
  have h4 : Real.exp ((c * y / p - 1) * p) = Real.exp (c * y) * Real.exp (-p) := by
    rw [← Real.exp_add]; congr 1; field_simp; ring
  rw [h3, h4] at h2
  have hcp : 0 < (c / p) ^ p := Real.rpow_pos_of_pos (by positivity) _
  have h5 : (p / c) ^ p * (c / p) ^ p = 1 := by
    rw [← Real.mul_rpow (by positivity) (by positivity)]
    rw [show p / c * (c / p) = 1 by field_simp]; simp
  calc y ^ p = (p / c) ^ p * ((c / p) ^ p * y ^ p) := by rw [← mul_assoc, h5, one_mul]
    _ ≤ (p / c) ^ p * (Real.exp (c * y) * Real.exp (-p)) := by gcongr
    _ = _ := by ring

/-- The weight `(1+t)^{p} e^{-c t}` is bounded on `t ≥ 0`. -/
lemma ste_weight_bdd {p c : ℝ} (hp : 0 ≤ p) (hc : 0 < c) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t : ℝ, 0 ≤ t → (1 + t) ^ p * Real.exp (-c * t) ≤ K := by
  refine ⟨(p / c) ^ p * Real.exp (-p) * Real.exp c, by positivity, fun t ht => ?_⟩
  have h := ste_rpow_le_exp hp hc (show 0 ≤ 1 + t by linarith)
  calc (1 + t) ^ p * Real.exp (-c * t)
      ≤ ((p / c) ^ p * Real.exp (-p) * Real.exp (c * (1 + t))) * Real.exp (-c * t) := by gcongr
    _ = _ := by
      rw [mul_assoc, mul_assoc, mul_assoc]; congr 1; congr 1
      rw [← Real.exp_add]; congr 1; ring

/-- Pointwise spherical bound `ρ ≤ A (1+|x|²)^{-d}` for the logarithmic thermal density. -/
lemma ste_pointwise_bound (hd : 2 ≤ d) {a β : ℝ} (ha : 0 < a) (hβ : 0 < β) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ x : Euc d,
      thermalDensity d 0 a β x ≤ A * (1 + ‖x‖ ^ 2) ^ (-(d : ℝ)) := by
  obtain ⟨c, hc, C, hC⟩ := logThermal_bounds_proof hd a β ha hβ
  obtain ⟨K, hK0, hK⟩ := ste_weight_bdd (p := β / 2 + d) (c := β * a / 2) (by positivity)
    (by positivity)
  refine ⟨max C 0 * K, by positivity, fun x => ?_⟩
  have ht : (0 : ℝ) ≤ ‖x‖ ^ 2 := sq_nonneg _
  have hpos : (0 : ℝ) < 1 + ‖x‖ ^ 2 := by linarith
  have hx := (hC x).2
  have hw := hK (‖x‖ ^ 2) ht
  have hsplit : (1 + ‖x‖ ^ 2) ^ (β / 2 + d) = (1 + ‖x‖ ^ 2) ^ (β / 2) * (1 + ‖x‖ ^ 2) ^ (d : ℝ) :=
    Real.rpow_add hpos _ _
  have hinv : (1 + ‖x‖ ^ 2) ^ (-(d : ℝ)) * (1 + ‖x‖ ^ 2) ^ (d : ℝ) = 1 := by
    rw [← Real.rpow_add hpos]; simp
  have hneg : 0 < (1 + ‖x‖ ^ 2) ^ (-(d : ℝ)) := Real.rpow_pos_of_pos hpos _
  have hE : Real.exp (-β * a * ‖x‖ ^ 2 / 2) = Real.exp (-(β * a / 2) * ‖x‖ ^ 2) := by
    congr 1; ring
  have hE0 := Real.exp_pos (-(β * a / 2) * ‖x‖ ^ 2)
  have hmain : (1 + ‖x‖ ^ 2) ^ (β / 2) * Real.exp (-β * a * ‖x‖ ^ 2 / 2) ≤
      K * (1 + ‖x‖ ^ 2) ^ (-(d : ℝ)) := by
    rw [hE]
    rw [hsplit] at hw
    have := mul_le_mul_of_nonneg_right hw hneg.le
    calc (1 + ‖x‖ ^ 2) ^ (β / 2) * Real.exp (-(β * a / 2) * ‖x‖ ^ 2)
        = ((1 + ‖x‖ ^ 2) ^ (β / 2) * (1 + ‖x‖ ^ 2) ^ (d : ℝ) *
            Real.exp (-(β * a / 2) * ‖x‖ ^ 2)) * (1 + ‖x‖ ^ 2) ^ (-(d : ℝ)) := by
          have : (1 + ‖x‖ ^ 2) ^ (β / 2) * (1 + ‖x‖ ^ 2) ^ (d : ℝ) *
            Real.exp (-(β * a / 2) * ‖x‖ ^ 2) * (1 + ‖x‖ ^ 2) ^ (-(d : ℝ)) =
            (1 + ‖x‖ ^ 2) ^ (β / 2) * Real.exp (-(β * a / 2) * ‖x‖ ^ 2) *
              ((1 + ‖x‖ ^ 2) ^ (-(d : ℝ)) * (1 + ‖x‖ ^ 2) ^ (d : ℝ)) := by ring
          rw [this, hinv, mul_one]
      _ ≤ _ := this
  calc thermalDensity d 0 a β x
      ≤ C * (1 + ‖x‖ ^ 2) ^ (β / 2) * Real.exp (-β * a * ‖x‖ ^ 2 / 2) := hx
    _ ≤ max C 0 * ((1 + ‖x‖ ^ 2) ^ (β / 2) * Real.exp (-β * a * ‖x‖ ^ 2 / 2)) := by
        rw [mul_assoc]
        have hnn : 0 ≤ (1 + ‖x‖ ^ 2) ^ (β / 2) * Real.exp (-β * a * ‖x‖ ^ 2 / 2) := by positivity
        exact mul_le_mul_of_nonneg_right (le_max_left _ _) hnn
    _ ≤ max C 0 * (K * (1 + ‖x‖ ^ 2) ^ (-(d : ℝ))) := by
        gcongr
    _ = _ := by ring

/-- Conjunct (2) of `logThermal_stereographic`. -/
lemma ste_hasSphericalBound (hd : 2 ≤ d) {a β : ℝ} (ha : 0 < a) (hβ : 0 < β) :
    ∃ A : ℝ, HasSphericalBound A (thermalDensity d 0 a β) := by
  obtain ⟨A, -, hA⟩ := ste_pointwise_bound hd ha hβ
  exact ⟨A, Filter.Eventually.of_forall hA⟩

end HRS.MS.Thm

end
