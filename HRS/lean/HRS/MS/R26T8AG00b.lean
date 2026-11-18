import HRS.MS.R26T8AG00a

/-!
# S8.2 observed-time layer, packet T8A.G00 (helper b): elementary pair bound

For `s, c > 0` and `M ≥ 0`, the function `t ↦ (1 + t^(-M))^2 exp(-c t^(-s))` is bounded on `(0, ∞)`:
the exponential beats every fixed power of `t^(-s)`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators ContDiff
namespace HRS.MS.R26T8A

theorem r26t8a_g00b_pair (s M c : ℝ) (hs : 0 < s) (hM : 0 ≤ M) (hc : 0 < c) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t : ℝ, 0 < t → (1 + t ^ (-M)) ^ 2 * Real.exp (-c * t ^ (-s)) ≤ K := by
  set k : ℕ := ⌈2 * M / s⌉₊ with hk
  have hk2 : 2 * (M / s) ≤ (k : ℝ) := by
    have := Nat.le_ceil (2 * M / s)
    rw [← hk] at this
    have e : 2 * M / s = 2 * (M / s) := by ring
    linarith
  have key : ∀ u : ℝ, 0 < u → u ^ k * Real.exp (-(c * u)) ≤ (k.factorial : ℝ) / c ^ k := by
    intro u hu
    have h := Real.pow_div_factorial_le_exp (x := c * u) (by positivity) k
    have hpos : 0 < (c * u) ^ k / (k.factorial : ℝ) := by positivity
    rw [Real.exp_neg]
    have hinv : (Real.exp (c * u))⁻¹ ≤ ((c * u) ^ k / (k.factorial : ℝ))⁻¹ := inv_anti₀ hpos h
    have hu0 : 0 ≤ u ^ k := by positivity
    calc u ^ k * (Real.exp (c * u))⁻¹ ≤ u ^ k * ((c * u) ^ k / (k.factorial : ℝ))⁻¹ :=
          mul_le_mul_of_nonneg_left hinv hu0
      _ = (k.factorial : ℝ) / c ^ k := by
          have hc0 : c ≠ 0 := hc.ne'
          have hu0' : u ≠ 0 := hu.ne'
          field_simp
          ring
  refine ⟨4 + 4 * ((k.factorial : ℝ) / c ^ k), by positivity, fun t ht => ?_⟩
  rcases le_total 1 t with h1 | h1
  · -- `t ≥ 1`: the first factor is at most `2`, the exponential at most `1`
    have hx0 : 0 ≤ t ^ (-M) := Real.rpow_nonneg ht.le _
    have hx1 : t ^ (-M) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos h1 (by linarith)
    have hE : Real.exp (-c * t ^ (-s)) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have := Real.rpow_nonneg ht.le (-s)
      nlinarith
    have hF : (1 + t ^ (-M)) ^ 2 ≤ 4 := by nlinarith
    have hE0 : 0 ≤ Real.exp (-c * t ^ (-s)) := (Real.exp_pos _).le
    have hpos : 0 ≤ 4 * ((k.factorial : ℝ) / c ^ k) := by positivity
    calc (1 + t ^ (-M)) ^ 2 * Real.exp (-c * t ^ (-s)) ≤ 4 * 1 :=
          mul_le_mul hF hE hE0 (by norm_num)
      _ ≤ 4 + 4 * ((k.factorial : ℝ) / c ^ k) := by linarith
  · -- `0 < t ≤ 1`: write `u = t^(-s) ≥ 1`, so `t^(-M) = u^(M/s) ≤ u^k`
    set u : ℝ := t ^ (-s) with hu
    have hu1 : 1 ≤ u := Real.one_le_rpow_of_pos_of_le_one_of_nonpos ht h1 (by linarith)
    have hu0 : 0 < u := by linarith
    have htM : t ^ (-M) = u ^ (M / s) := by
      rw [hu, ← Real.rpow_mul ht.le]
      congr 1
      field_simp
    have hq0 : 0 ≤ M / s := div_nonneg hM hs.le
    have hup : 1 ≤ u ^ (M / s) := Real.one_le_rpow hu1 hq0
    have hmono : u ^ (M / s) ≤ u ^ (k : ℝ) := by
      apply Real.rpow_le_rpow_of_exponent_le hu1
      linarith
    have hkrpow : u ^ (k : ℝ) = u ^ k := Real.rpow_natCast u k
    have hF : (1 + t ^ (-M)) ^ 2 ≤ 4 * u ^ k := by
      rw [htM]
      have h2 : (1 + u ^ (M / s)) ≤ 2 * u ^ (M / s) := by linarith
      have h3 : (1 + u ^ (M / s)) ^ 2 ≤ (2 * u ^ (M / s)) ^ 2 :=
        pow_le_pow_left₀ (by linarith) h2 2
      have h4 : (u ^ (M / s)) ^ 2 ≤ u ^ k := by
        have hsq : (u ^ (M / s)) ^ 2 = u ^ (2 * (M / s)) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hu0.le]
          congr 1
          push_cast
          ring
        rw [hsq, ← hkrpow]
        exact Real.rpow_le_rpow_of_exponent_le hu1 hk2
      nlinarith
    have hE := key u hu0
    have hexp : Real.exp (-c * t ^ (-s)) = Real.exp (-(c * u)) := by
      rw [← hu]; ring_nf
    have hE0 : 0 ≤ Real.exp (-c * t ^ (-s)) := (Real.exp_pos _).le
    have hpos : 0 ≤ 4 * ((k.factorial : ℝ) / c ^ k) := by positivity
    calc (1 + t ^ (-M)) ^ 2 * Real.exp (-c * t ^ (-s)) ≤ (4 * u ^ k) * Real.exp (-c * t ^ (-s)) :=
          mul_le_mul_of_nonneg_right hF hE0
      _ = 4 * (u ^ k * Real.exp (-(c * u))) := by rw [hexp]; ring
      _ ≤ 4 * ((k.factorial : ℝ) / c ^ k) := mul_le_mul_of_nonneg_left hE (by norm_num)
      _ ≤ 4 + 4 * ((k.factorial : ℝ) / c ^ k) := by linarith

end HRS.MS.R26T8A

end
