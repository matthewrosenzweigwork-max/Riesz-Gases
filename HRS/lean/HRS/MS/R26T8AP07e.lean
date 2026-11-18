import HRS.MS.R26T8AP07d

/-!
# S8.2 local Newton layer, packet T8A.P07 (part e): the summed envelope
For `r in (0,2]` let `u n = (1/2)^n`, `l n = 1 + |log u n|` and
`beta n = u_n^(d-sigma) r^(2-d-q) l_n^b (l_n + |log r| if d=2,q=0 else 1)` when `u_n <= r/4`, and
`u_n^(2-sigma-q) l_n^b (l_n if d=2,q=0 else 1)` otherwise (the bounds of P03 and of the comparable/small annuli).
`r26t8a_p07_envelope`: `beta` is summable with sum `<= C (1 + r^(2-sigma-q) (1+|log r|)^(b+1))` (`sigma < d`).
-/

set_option autoImplicit false
noncomputable section
open Filter Topology

namespace HRS.MS.R26T8A

/-- the part of the envelope with `u_n <= r/4` -/
theorem r26t8a_p07_envI (d : ℕ) (hd : 2 ≤ d) (σ : ℝ) (hσ : σ < d) (q b : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 0 < r → r ≤ 4 →
      Summable (fun n : ℕ => if ((1 : ℝ) / 2) ^ n ≤ r / 4 then
          ((((1 : ℝ) / 2) ^ n) ^ ((d : ℝ) - σ) * r ^ (2 - (d : ℝ) - q)) * (1 + |Real.log (((1 : ℝ) / 2) ^ n)|) ^ b *
            (if d = 2 ∧ q = 0 then 1 + |Real.log (((1 : ℝ) / 2) ^ n)| + |Real.log r| else 1) else 0) ∧
      ∑' n : ℕ, (if ((1 : ℝ) / 2) ^ n ≤ r / 4 then
          ((((1 : ℝ) / 2) ^ n) ^ ((d : ℝ) - σ) * r ^ (2 - (d : ℝ) - q)) * (1 + |Real.log (((1 : ℝ) / 2) ^ n)|) ^ b *
            (if d = 2 ∧ q = 0 then 1 + |Real.log (((1 : ℝ) / 2) ^ n)| + |Real.log r| else 1) else 0) ≤
        C * (r ^ (2 - σ - q) * (1 + |Real.log r|) ^ (b + 1)) := by
  have hdσ : 0 < (d : ℝ) - σ := by linarith
  obtain ⟨CI, hCI0, hCI⟩ := r26t8a_p07_SI ((d : ℝ) - σ) hdσ b
  obtain ⟨CI1, hCI10, hCI1⟩ := r26t8a_p07_SI ((d : ℝ) - σ) hdσ (b + 1)
  refine ⟨CI1 + CI, by positivity, fun r hr hr2 => ?_⟩
  obtain ⟨sm0, le0⟩ := hCI r hr hr2
  obtain ⟨sm1, le1⟩ := hCI1 r hr hr2
  have hlog : 0 ≤ |Real.log r| := abs_nonneg _
  have hL1 : (1 + |Real.log r|) ^ b ≤ (1 + |Real.log r|) ^ (b + 1) :=
    pow_le_pow_right₀ (by linarith) (Nat.le_succ b)
  by_cases hs : d = 2 ∧ q = 0
  · obtain ⟨hd2, hq0⟩ := hs
    have hd2' : (d : ℝ) = 2 := by exact_mod_cast hd2
    have he : (2 - (d : ℝ) - (q : ℝ)) = 0 := by rw [hd2', hq0]; simp
    have hpt : ∀ n : ℕ, (if ((1 : ℝ) / 2) ^ n ≤ r / 4 then
          ((((1 : ℝ) / 2) ^ n) ^ ((d : ℝ) - σ) * r ^ (2 - (d : ℝ) - q)) * (1 + |Real.log (((1 : ℝ) / 2) ^ n)|) ^ b *
            (if d = 2 ∧ q = 0 then 1 + |Real.log (((1 : ℝ) / 2) ^ n)| + |Real.log r| else 1) else 0) =
        (if ((1 : ℝ) / 2) ^ n ≤ r / 4 then (((1 : ℝ) / 2) ^ n) ^ ((d : ℝ) - σ) *
          (1 + |Real.log (((1 : ℝ) / 2) ^ n)|) ^ (b + 1) else 0) +
        |Real.log r| * (if ((1 : ℝ) / 2) ^ n ≤ r / 4 then (((1 : ℝ) / 2) ^ n) ^ ((d : ℝ) - σ) *
          (1 + |Real.log (((1 : ℝ) / 2) ^ n)|) ^ b else 0) := fun n => by
      by_cases h : ((1 : ℝ) / 2) ^ n ≤ r / 4
      · simp only [if_pos h, if_pos (And.intro hd2 hq0), he, Real.rpow_zero, mul_one]; ring
      · simp only [if_neg h]; ring
    simp only [hpt]
    refine ⟨sm1.add (sm0.mul_left _), ?_⟩
    rw [Summable.tsum_add sm1 (sm0.mul_left _), tsum_mul_left]
    have hexp : r ^ ((d : ℝ) - σ) = r ^ (2 - σ - (q : ℝ)) := by
      congr 1; rw [hd2', hq0]; simp
    rw [hexp] at le0 le1
    have h2 : |Real.log r| * (CI * r ^ (2 - σ - (q : ℝ)) * (1 + |Real.log r|) ^ b) ≤
        CI * (r ^ (2 - σ - (q : ℝ)) * (1 + |Real.log r|) ^ (b + 1)) := by
      have : |Real.log r| * (1 + |Real.log r|) ^ b ≤ (1 + |Real.log r|) ^ (b + 1) := by
        rw [pow_succ]; nlinarith [pow_nonneg (by linarith : (0 : ℝ) ≤ 1 + |Real.log r|) b]
      have hr1 : 0 ≤ CI * r ^ (2 - σ - (q : ℝ)) := mul_nonneg hCI0 (Real.rpow_nonneg hr.le _)
      nlinarith [mul_le_mul_of_nonneg_left this hr1]
    nlinarith [mul_nonneg hCI10 (mul_nonneg (Real.rpow_nonneg hr.le (2 - σ - (q : ℝ))) (by positivity : (0 : ℝ) ≤ (1 + |Real.log r|) ^ (b + 1)))]
  · have hpt : ∀ n : ℕ, (if ((1 : ℝ) / 2) ^ n ≤ r / 4 then
          ((((1 : ℝ) / 2) ^ n) ^ ((d : ℝ) - σ) * r ^ (2 - (d : ℝ) - q)) * (1 + |Real.log (((1 : ℝ) / 2) ^ n)|) ^ b *
            (if d = 2 ∧ q = 0 then 1 + |Real.log (((1 : ℝ) / 2) ^ n)| + |Real.log r| else 1) else 0) =
        r ^ (2 - (d : ℝ) - q) * (if ((1 : ℝ) / 2) ^ n ≤ r / 4 then (((1 : ℝ) / 2) ^ n) ^ ((d : ℝ) - σ) *
          (1 + |Real.log (((1 : ℝ) / 2) ^ n)|) ^ b else 0) := fun n => by
      by_cases h : ((1 : ℝ) / 2) ^ n ≤ r / 4
      · simp only [if_pos h, if_neg hs]; ring
      · simp only [if_neg h]; ring
    simp only [hpt]
    refine ⟨sm0.mul_left _, ?_⟩
    rw [tsum_mul_left]
    have hexp : r ^ (2 - (d : ℝ) - (q : ℝ)) * r ^ ((d : ℝ) - σ) = r ^ (2 - σ - (q : ℝ)) := by
      rw [← Real.rpow_add hr]; congr 1; ring
    have hr0 : 0 ≤ r ^ (2 - (d : ℝ) - (q : ℝ)) := Real.rpow_nonneg hr.le _
    calc r ^ (2 - (d : ℝ) - (q : ℝ)) * ∑' n : ℕ, (if ((1 : ℝ) / 2) ^ n ≤ r / 4 then (((1 : ℝ) / 2) ^ n) ^ ((d : ℝ) - σ) *
          (1 + |Real.log (((1 : ℝ) / 2) ^ n)|) ^ b else 0)
        ≤ r ^ (2 - (d : ℝ) - (q : ℝ)) * (CI * r ^ ((d : ℝ) - σ) * (1 + |Real.log r|) ^ b) :=
          mul_le_mul_of_nonneg_left le0 hr0
      _ = CI * (r ^ (2 - (d : ℝ) - (q : ℝ)) * r ^ ((d : ℝ) - σ)) * (1 + |Real.log r|) ^ b := by ring
      _ = CI * r ^ (2 - σ - (q : ℝ)) * (1 + |Real.log r|) ^ b := by rw [hexp]
      _ ≤ (CI1 + CI) * (r ^ (2 - σ - (q : ℝ)) * (1 + |Real.log r|) ^ (b + 1)) := by
          have hr1 : 0 ≤ r ^ (2 - σ - (q : ℝ)) := Real.rpow_nonneg hr.le _
          have : CI * r ^ (2 - σ - (q : ℝ)) * (1 + |Real.log r|) ^ b ≤
              CI * (r ^ (2 - σ - (q : ℝ)) * (1 + |Real.log r|) ^ (b + 1)) := by
            nlinarith [mul_le_mul_of_nonneg_left hL1 (mul_nonneg hCI0 hr1)]
          nlinarith [mul_nonneg hCI10 (mul_nonneg hr1 (by positivity : (0 : ℝ) ≤ (1 + |Real.log r|) ^ (b + 1)))]

end HRS.MS.R26T8A
