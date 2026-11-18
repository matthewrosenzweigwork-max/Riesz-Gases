import HRS.MS.R26T8AP07e

/-!
# S8.2 local Newton layer, packet T8A.P07 (part f): the summed envelope, part with `u_n > r/4`, and the full envelope
-/

set_option autoImplicit false
noncomputable section
open Filter Topology

namespace HRS.MS.R26T8A

theorem r26t8a_p07_envII (d : ℕ) (hd : 2 ≤ d) (σ : ℝ) (hσ : σ < d) (q b : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 0 < r → r ≤ 4 →
      Summable (fun n : ℕ => if r / 4 < ((1 : ℝ) / 2) ^ n then
          (((1 : ℝ) / 2) ^ n) ^ (2 - σ - q) * (1 + |Real.log (((1 : ℝ) / 2) ^ n)|) ^ b *
            (if d = 2 ∧ q = 0 then 1 + |Real.log (((1 : ℝ) / 2) ^ n)| else 1) else 0) ∧
      ∑' n : ℕ, (if r / 4 < ((1 : ℝ) / 2) ^ n then
          (((1 : ℝ) / 2) ^ n) ^ (2 - σ - q) * (1 + |Real.log (((1 : ℝ) / 2) ^ n)|) ^ b *
            (if d = 2 ∧ q = 0 then 1 + |Real.log (((1 : ℝ) / 2) ^ n)| else 1) else 0) ≤
        C * (1 + r ^ (2 - σ - q) * (1 + |Real.log r|) ^ (b + 1)) := by
  by_cases hs : d = 2 ∧ q = 0
  · obtain ⟨hd2, hq0⟩ := hs
    have hd2' : (d : ℝ) = 2 := by exact_mod_cast hd2
    have ha : 0 < 2 - σ - (q : ℝ) := by rw [hq0]; simp; linarith [hσ, hd2']
    obtain ⟨C, hC0, hC⟩ := r26t8a_p07_SII_pos (2 - σ - (q : ℝ)) ha (b + 1)
    refine ⟨C, hC0, fun r hr hr2 => ⟨?_, ?_⟩⟩
    · have := r26t8a_p07_head_summable (fun n : ℕ => (((1 : ℝ) / 2) ^ n) ^ (2 - σ - (q : ℝ)) *
        (1 + |Real.log (((1 : ℝ) / 2) ^ n)|) ^ b * (1 + |Real.log (((1 : ℝ) / 2) ^ n)|)) (r / 4) (by positivity)
      simpa [if_pos (And.intro hd2 hq0)] using this
    · have e : ∀ n : ℕ, (if r / 4 < ((1 : ℝ) / 2) ^ n then
          (((1 : ℝ) / 2) ^ n) ^ (2 - σ - (q : ℝ)) * (1 + |Real.log (((1 : ℝ) / 2) ^ n)|) ^ b *
            (if d = 2 ∧ q = 0 then 1 + |Real.log (((1 : ℝ) / 2) ^ n)| else 1) else 0) =
          (if r / 4 < ((1 : ℝ) / 2) ^ n then (((1 : ℝ) / 2) ^ n) ^ (2 - σ - (q : ℝ)) *
            (1 + |Real.log (((1 : ℝ) / 2) ^ n)|) ^ (b + 1) else 0) := fun n => by
        by_cases h : r / 4 < ((1 : ℝ) / 2) ^ n
        · simp only [if_pos h, if_pos (And.intro hd2 hq0)]; ring
        · simp only [if_neg h]
      simp only [e]
      refine (hC r hr hr2).trans ?_
      have : 0 ≤ r ^ (2 - σ - (q : ℝ)) * (1 + |Real.log r|) ^ (b + 1) :=
        mul_nonneg (Real.rpow_nonneg hr.le _) (by positivity)
      nlinarith [mul_nonneg hC0 this]
  · have e : ∀ r : ℝ, ∀ n : ℕ, (if r / 4 < ((1 : ℝ) / 2) ^ n then
          (((1 : ℝ) / 2) ^ n) ^ (2 - σ - (q : ℝ)) * (1 + |Real.log (((1 : ℝ) / 2) ^ n)|) ^ b *
            (if d = 2 ∧ q = 0 then 1 + |Real.log (((1 : ℝ) / 2) ^ n)| else 1) else 0) =
          (if r / 4 < ((1 : ℝ) / 2) ^ n then (((1 : ℝ) / 2) ^ n) ^ (2 - σ - (q : ℝ)) *
            (1 + |Real.log (((1 : ℝ) / 2) ^ n)|) ^ b else 0) := fun r n => by
      by_cases h : r / 4 < ((1 : ℝ) / 2) ^ n
      · simp only [if_pos h, if_neg hs]; ring
      · simp only [if_neg h]
    have hsm : ∀ r : ℝ, 0 < r → Summable (fun n : ℕ => if r / 4 < ((1 : ℝ) / 2) ^ n then
          (((1 : ℝ) / 2) ^ n) ^ (2 - σ - (q : ℝ)) * (1 + |Real.log (((1 : ℝ) / 2) ^ n)|) ^ b *
            (if d = 2 ∧ q = 0 then 1 + |Real.log (((1 : ℝ) / 2) ^ n)| else 1) else 0) := fun r hr => by
      have := r26t8a_p07_head_summable (fun n : ℕ => (((1 : ℝ) / 2) ^ n) ^ (2 - σ - (q : ℝ)) *
        (1 + |Real.log (((1 : ℝ) / 2) ^ n)|) ^ b) (r / 4) (by positivity)
      simpa only [e r] using this
    by_cases hneg : 2 - σ - (q : ℝ) < 0
    · obtain ⟨C, hC0, hC⟩ := r26t8a_p07_SII_neg (2 - σ - (q : ℝ)) hneg b
      refine ⟨C, hC0, fun r hr hr2 => ⟨hsm r hr, ?_⟩⟩
      simp only [e r]
      refine (hC r hr hr2).trans ?_
      have hL1 : (1 + |Real.log r|) ^ b ≤ (1 + |Real.log r|) ^ (b + 1) :=
        pow_le_pow_right₀ (by linarith [abs_nonneg (Real.log r)]) (Nat.le_succ b)
      have hr1 : 0 ≤ r ^ (2 - σ - (q : ℝ)) := Real.rpow_nonneg hr.le _
      nlinarith [mul_le_mul_of_nonneg_left hL1 (mul_nonneg hC0 hr1), mul_nonneg hC0 hr1]
    · by_cases hzero : 2 - σ - (q : ℝ) = 0
      · obtain ⟨C, hC0, hC⟩ := r26t8a_p07_SII_zero b
        refine ⟨C, hC0, fun r hr hr2 => ⟨hsm r hr, ?_⟩⟩
        simp only [e r]
        simp only [hzero]
        refine (hC r hr hr2).trans ?_
        have : 0 ≤ r ^ (0 : ℝ) * (1 + |Real.log r|) ^ (b + 1) := by positivity
        rw [Real.rpow_zero] at this ⊢
        nlinarith [mul_nonneg hC0 (by positivity : (0 : ℝ) ≤ (1 + |Real.log r|) ^ (b + 1))]
      · have hpos : 0 < 2 - σ - (q : ℝ) := lt_of_le_of_ne (not_lt.1 hneg) (Ne.symm hzero)
        obtain ⟨C, hC0, hC⟩ := r26t8a_p07_SII_pos (2 - σ - (q : ℝ)) hpos b
        refine ⟨C, hC0, fun r hr hr2 => ⟨hsm r hr, ?_⟩⟩
        simp only [e r]
        refine (hC r hr hr2).trans ?_
        have : 0 ≤ r ^ (2 - σ - (q : ℝ)) * (1 + |Real.log r|) ^ (b + 1) :=
          mul_nonneg (Real.rpow_nonneg hr.le _) (by positivity)
        nlinarith [mul_nonneg hC0 this]

end HRS.MS.R26T8A
