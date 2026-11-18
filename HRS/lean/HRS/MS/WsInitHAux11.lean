import HRS.MS.WsInitHAux10

/-!
# S21H packet H, part 11: the box hypothesis of `s21h_init_w1` from the decay of the orbit family

`s21h_box_of_product`: product decay `w_k ≤ B (1+n)^{-5/2} V_α` (`(n,α) = σ k`), `∑ V^{2/5} < ∞`, gives `K, τ₀` with
`∀ Q ≥ 1, ∃ I, |I| ≤ K Q² ∧ ∑_{k ∉ I} w_k ≤ τ₀² Q^{-3/2}` (box `I = σ⁻¹({n ≤ Q} × A_Q)`).

`s21h_box_osc`: for the Hermite index set (`V_α = λ_α^{-2γ}`, `λ_α = 2|α| + d + 1`) and `5d/4 < γ`: if
`‖φ_k‖_{C_b^J} ≤ A (1+n)^{-5/4} λ_α^{-γ}` then the box hypothesis holds.  (For the cosine orbit family:
`cbNorm J f_{n,α} ≲ (1+n²)^{3/8} n^{-2} K b_α ≲ (1+n)^{-5/4} λ_α^{(I-m)/2}`, `γ = (m - I)/2`, `m - I > 5d/2` for `m = 24d+240`.)
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal Real

namespace HRS.MS.S21

open HRS.Whole

theorem s21h_box_of_product {ι : Type*} (σ : ℕ ≃ ℕ × ι) (w : ℕ → ℝ) (hw0 : ∀ k, 0 ≤ w k) {V : ι → ℝ}
    (hV0 : ∀ i, 0 ≤ V i) (hV : Summable V) {B : ℝ} (hB0 : 0 ≤ B)
    (hw : ∀ k, w k ≤ B * (((1 : ℝ) + ((σ k).1 : ℝ)) ^ (-(5 : ℝ) / 2) * V (σ k).2))
    (hsum : Summable fun i => V i ^ ((2 : ℝ) / 5)) :
    ∃ K τ₀ : ℝ, 0 ≤ K ∧ 0 ≤ τ₀ ∧ ∀ Q : ℕ, 1 ≤ Q → ∃ I : Finset ℕ, (I.card : ℝ) ≤ K * (Q : ℝ) ^ 2 ∧
      ∑' k : ℕ, (if k ∈ I then 0 else w k) ≤ τ₀ ^ 2 / (Q : ℝ) ^ ((3 : ℝ) / 2) := by
  classical
  set M : ℝ := ∑' i, V i ^ ((2 : ℝ) / 5) with hM
  have hM0 : 0 ≤ M := tsum_nonneg fun i => Real.rpow_nonneg (hV0 i) _
  set U : ℕ → ℝ := fun n => ((1 : ℝ) + n) ^ (-(5 : ℝ) / 2) with hU
  have hU0 : ∀ n, 0 ≤ U n := fun n => Real.rpow_nonneg (by positivity) _
  have hUs : Summable U := by
    have h : Summable fun n : ℕ => ((n : ℝ) + 1) ^ (-(5 : ℝ) / 2) := by
      have := (Real.summable_nat_rpow (p := -(5 : ℝ) / 2)).2 (by norm_num)
      exact (summable_nat_add_iff 1).2 this |>.congr fun n => by push_cast; rfl
    exact h.congr fun n => by simp [hU, add_comm]
  set SU : ℝ := ∑' n, U n with hSU
  set SV : ℝ := ∑' i, V i with hSV
  have hSU0 : 0 ≤ SU := tsum_nonneg hU0
  have hSV0 : 0 ≤ SV := tsum_nonneg hV0
  refine ⟨2 * M, Real.sqrt (B * (2 / 3 * SV + SU * M)), by positivity, Real.sqrt_nonneg _, fun Q hQ => ?_⟩
  obtain ⟨A, hAc, hAt⟩ := s21h_levelset hV0 hsum le_rfl Q hQ
  have hQ0 : (0 : ℝ) < Q := by exact_mod_cast hQ
  set N : Finset ℕ := Finset.range (Q + 1) with hN
  set I : Finset ℕ := (N ×ˢ A).image σ.symm with hI
  have hmem : ∀ k, k ∈ I ↔ σ k ∈ N ×ˢ A := fun k => by
    rw [hI, Finset.mem_image]
    constructor
    · rintro ⟨q, hq, rfl⟩; simpa using hq
    · intro h; exact ⟨σ k, h, by simp⟩
  refine ⟨I, ?_, ?_⟩
  · have hc : I.card ≤ (N ×ˢ A).card := Finset.card_image_le
    rw [Finset.card_product, hN, Finset.card_range] at hc
    have hc' : (I.card : ℝ) ≤ ((Q + 1 : ℕ) : ℝ) * (A.card : ℝ) := by exact_mod_cast hc
    calc (I.card : ℝ) ≤ ((Q + 1 : ℕ) : ℝ) * (A.card : ℝ) := hc'
      _ ≤ (2 * (Q : ℝ)) * (M * Q) := by
          have hQ1 : ((Q + 1 : ℕ) : ℝ) ≤ 2 * Q := by
            push_cast; have : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
            linarith
          exact mul_le_mul hQ1 hAc (Nat.cast_nonneg _) (by positivity)
      _ = 2 * M * (Q : ℝ) ^ 2 := by ring
  · -- the tail
    set tU : ℕ → ℝ := fun n => if n ≤ Q then 0 else U n with htU
    set tV : ι → ℝ := fun i => if i ∈ A then 0 else V i with htV
    have htU0 : ∀ n, 0 ≤ tU n := fun n => by simp only [htU]; split_ifs <;> simp [hU0 n]
    have htV0 : ∀ i, 0 ≤ tV i := fun i => by simp only [htV]; split_ifs <;> simp [hV0 i]
    have htUs : Summable tU := Summable.of_nonneg_of_le htU0 (fun n => by
      simp only [htU]; split_ifs <;> simp [hU0 n]) hUs
    have htVs : Summable tV := Summable.of_nonneg_of_le htV0 (fun i => by
      simp only [htV]; split_ifs <;> simp [hV0 i]) hV
    set g : ℕ × ι → ℝ := fun q => B * (tU q.1 * V q.2 + U q.1 * tV q.2) with hg
    have hg0 : ∀ q, 0 ≤ g q := fun q => by
      simp only [hg]
      have := htU0 q.1; have := hV0 q.2; have := hU0 q.1; have := htV0 q.2
      positivity
    have hgs : Summable g := by
      have h1 : Summable fun q : ℕ × ι => tU q.1 * V q.2 :=
        summable_mul_of_summable_norm (f := tU) (g := V)
          (by simpa [Real.norm_eq_abs, abs_of_nonneg, htU0] using htUs)
          (by simpa [Real.norm_eq_abs, abs_of_nonneg, hV0] using hV)
      have h2 : Summable fun q : ℕ × ι => U q.1 * tV q.2 :=
        summable_mul_of_summable_norm (f := U) (g := tV)
          (by simpa [Real.norm_eq_abs, abs_of_nonneg, hU0] using hUs)
          (by simpa [Real.norm_eq_abs, abs_of_nonneg, htV0] using htVs)
      exact (h1.add h2).mul_left B
    have hle : ∀ k, (if k ∈ I then 0 else w k) ≤ g (σ k) := by
      intro k
      by_cases hk : k ∈ I
      · simp only [hk, if_true]; exact hg0 _
      · simp only [hk, if_false]
        have hnot : ¬ ((σ k).1 ∈ N ∧ (σ k).2 ∈ A) := by
          intro h; exact hk ((hmem k).2 (Finset.mem_product.2 h))
        refine (hw k).trans ?_
        simp only [hg]
        have hUV : 0 ≤ U (σ k).1 * V (σ k).2 := mul_nonneg (hU0 _) (hV0 _)
        by_cases hn : (σ k).1 ∈ N
        · have hA' : (σ k).2 ∉ A := fun h => hnot ⟨hn, h⟩
          have : tV (σ k).2 = V (σ k).2 := by simp [htV, hA']
          rw [this]
          have h2 : 0 ≤ tU (σ k).1 * V (σ k).2 := mul_nonneg (htU0 _) (hV0 _)
          exact mul_le_mul_of_nonneg_left (by simp only [hU]; linarith) hB0
        · have hn' : ¬ (σ k).1 ≤ Q := by
            intro h; exact hn (by simp [hN, Nat.lt_succ_iff, h])
          have : tU (σ k).1 = U (σ k).1 := by simp [htU, hn']
          rw [this]
          have h2 : 0 ≤ U (σ k).1 * tV (σ k).2 := mul_nonneg (hU0 _) (htV0 _)
          have h3 : 0 ≤ tU (σ k).1 * V (σ k).2 := mul_nonneg (htU0 _) (hV0 _)
          refine mul_le_mul_of_nonneg_left ?_ hB0
          have e : U (σ k).1 = ((1 : ℝ) + ((σ k).1 : ℝ)) ^ (-(5 : ℝ) / 2) := rfl
          rw [← e]
          linarith
    have hls : Summable fun k : ℕ => (if k ∈ I then 0 else w k) :=
      Summable.of_nonneg_of_le (fun k => by split_ifs <;> simp [hw0 k]) hle ((σ.summable_iff.2 hgs))
    refine (hls.tsum_le_tsum hle (σ.summable_iff.2 hgs)).trans ?_
    rw [show (∑' k, g (σ k)) = ∑' q, g q from σ.tsum_eq g]
    have e1 : ∑' q : ℕ × ι, tU q.1 * V q.2 = (∑' n, tU n) * ∑' i, V i :=
      (tsum_mul_tsum_of_summable_norm (f := tU) (g := V)
          (by simpa [Real.norm_eq_abs, abs_of_nonneg, htU0] using htUs)
          (by simpa [Real.norm_eq_abs, abs_of_nonneg, hV0] using hV)).symm
    have e2 : ∑' q : ℕ × ι, U q.1 * tV q.2 = (∑' n, U n) * ∑' i, tV i :=
      (tsum_mul_tsum_of_summable_norm (f := U) (g := tV)
          (by simpa [Real.norm_eq_abs, abs_of_nonneg, hU0] using hUs)
          (by simpa [Real.norm_eq_abs, abs_of_nonneg, htV0] using htVs)).symm
    have h1s : Summable fun q : ℕ × ι => tU q.1 * V q.2 :=
      summable_mul_of_summable_norm (f := tU) (g := V)
        (by simpa [Real.norm_eq_abs, abs_of_nonneg, htU0] using htUs)
        (by simpa [Real.norm_eq_abs, abs_of_nonneg, hV0] using hV)
    have h2s : Summable fun q : ℕ × ι => U q.1 * tV q.2 :=
      summable_mul_of_summable_norm (f := U) (g := tV)
        (by simpa [Real.norm_eq_abs, abs_of_nonneg, hU0] using hUs)
        (by simpa [Real.norm_eq_abs, abs_of_nonneg, htV0] using htVs)
    have hgsum : ∑' q, g q = B * ((∑' n, tU n) * SV + SU * ∑' i, tV i) := by
      simp only [hg]
      rw [tsum_mul_left, h1s.tsum_add h2s, e1, e2]
    rw [hgsum]
    -- the tail sums
    have hs5 : Summable fun n : ℕ => (if n ≤ Q then (0 : ℝ) else ((n : ℝ)) ^ (-(5 : ℝ) / 2)) :=
      Summable.of_nonneg_of_le (fun n => by split_ifs <;> simp [Real.rpow_nonneg])
        (fun n => by split_ifs <;> simp [Real.rpow_nonneg])
        ((Real.summable_nat_rpow (p := -(5 : ℝ) / 2)).2 (by norm_num))
    have hTU : ∑' n, tU n ≤ 2 / 3 * (Q : ℝ) ^ (-(3 : ℝ) / 2) := by
      refine le_trans (htUs.tsum_le_tsum (g := fun n : ℕ => if n ≤ Q then (0 : ℝ) else ((n : ℝ)) ^ (-(5 : ℝ) / 2))
        (fun n => ?_) hs5) (s21h_tail_nat Q hQ)
      simp only [htU]
      by_cases hn : n ≤ Q
      · simp [hn]
      · simp only [hn, if_false, hU]
        have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
        exact Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith) (by norm_num)
    have hTV : ∑' i, tV i ≤ M * (Q : ℝ) ^ (-(3 : ℝ) / 2) := hAt
    have hp : (Q : ℝ) ^ (-(3 : ℝ) / 2) = 1 / (Q : ℝ) ^ ((3 : ℝ) / 2) := by
      rw [show -(3 : ℝ) / 2 = -((3 : ℝ) / 2) by ring, Real.rpow_neg hQ0.le, one_div]
    have hpos : 0 ≤ B * (2 / 3 * SV + SU * M) := by positivity
    calc B * ((∑' n, tU n) * SV + SU * ∑' i, tV i)
        ≤ B * ((2 / 3 * (Q : ℝ) ^ (-(3 : ℝ) / 2)) * SV + SU * (M * (Q : ℝ) ^ (-(3 : ℝ) / 2))) := by
          gcongr
      _ = B * (2 / 3 * SV + SU * M) / (Q : ℝ) ^ ((3 : ℝ) / 2) := by rw [hp]; ring
      _ = Real.sqrt (B * (2 / 3 * SV + SU * M)) ^ 2 / (Q : ℝ) ^ ((3 : ℝ) / 2) := by
          rw [Real.sq_sqrt hpos]

end HRS.MS.S21
