import HRS.MS.WsInitHAux9

/-!
# S21H packet H, part 10: box decompositions from product decay

`s21h_levelset`: for `V ≥ 0` on a countable index set with `∑ V^{2/5} ≤ M`, for every `Q ≥ 1` there is a finite set `A` with `|A| ≤ M Q` and
`∑_{i ∉ A} V_i ≤ M Q^{-3/2}` (level set `{V ≥ Q^{-5/2}}`, Markov).
`s21h_tail_nat`: `∑_{n > Q} n^{-5/2} ≤ (2/3) Q^{-3/2}` (integral test).
`s21h_box_of_product`: for an enumeration `σ : ℕ ≃ ℕ × ι` and weights `w_k ≤ B (1+n)^{-5/2} V_α` (`(n,α) = σ k`) with `∑ V^{2/5} < ∞`
there are `K, τ₀` with the box hypothesis of `s21h_init_w1`: `∀ Q ≥ 1, ∃ I, |I| ≤ K Q²` and `∑_{k ∉ I} w_k ≤ τ₀² Q^{-3/2}`.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal Real

namespace HRS.MS.S21

open Classical in
theorem s21h_levelset {ι : Type*} {V : ι → ℝ} (hV0 : ∀ i, 0 ≤ V i) {M : ℝ}
    (hsum : Summable fun i => V i ^ ((2 : ℝ) / 5)) (hM : ∑' i, V i ^ ((2 : ℝ) / 5) ≤ M) (Q : ℕ) (hQ : 1 ≤ Q) :
    ∃ A : Finset ι, (A.card : ℝ) ≤ M * Q ∧
      ∑' i, (if i ∈ A then 0 else V i) ≤ M * (Q : ℝ) ^ (-(3 : ℝ) / 2) := by
  classical
  have hQ0 : (0 : ℝ) < Q := by exact_mod_cast hQ
  set t : ℝ := (Q : ℝ) ^ (-(5 : ℝ) / 2) with ht
  have ht0 : 0 < t := Real.rpow_pos_of_pos hQ0 _
  have htθ : t ^ ((2 : ℝ) / 5) = (Q : ℝ)⁻¹ := by
    rw [ht, ← Real.rpow_mul hQ0.le]
    rw [show -(5 : ℝ) / 2 * (2 / 5) = -1 by ring, Real.rpow_neg_one]
  have ht35 : t ^ ((3 : ℝ) / 5) = (Q : ℝ) ^ (-(3 : ℝ) / 2) := by
    rw [ht, ← Real.rpow_mul hQ0.le]
    congr 1; ring
  have hθ0 : 0 < t ^ ((2 : ℝ) / 5) := Real.rpow_pos_of_pos ht0 _
  have hfin : {i | t ≤ V i}.Finite := by
    have hlim := hsum.tendsto_cofinite_zero
    have hev : ∀ᶠ i in Filter.cofinite, V i ^ ((2 : ℝ) / 5) < t ^ ((2 : ℝ) / 5) :=
      hlim.eventually (gt_mem_nhds hθ0)
    rw [Filter.eventually_cofinite] at hev
    refine hev.subset fun i hi => ?_
    simp only [mem_setOf_eq] at hi ⊢
    exact not_lt.2 (Real.rpow_le_rpow ht0.le hi (by norm_num))
  set A : Finset ι := hfin.toFinset with hA
  have hmemA : ∀ i, i ∈ A ↔ t ≤ V i := fun i => by simp [hA]
  have hpos : ∀ i, 0 ≤ V i ^ ((2 : ℝ) / 5) := fun i => Real.rpow_nonneg (hV0 i) _
  refine ⟨A, ?_, ?_⟩
  · have h1 : A.card • t ^ ((2 : ℝ) / 5) ≤ ∑ i ∈ A, V i ^ ((2 : ℝ) / 5) := by
      rw [← Finset.sum_const]
      exact Finset.sum_le_sum fun i hi => Real.rpow_le_rpow ht0.le ((hmemA i).1 hi) (by norm_num)
    have h2 : ∑ i ∈ A, V i ^ ((2 : ℝ) / 5) ≤ M := (hsum.sum_le_tsum A fun i _ => hpos i).trans hM
    rw [nsmul_eq_mul, htθ] at h1
    have : (A.card : ℝ) * (Q : ℝ)⁻¹ ≤ M := h1.trans h2
    rw [← le_div_iff₀ (inv_pos.2 hQ0)] at this
    simpa [div_inv_eq_mul] using this
  · have hle : ∀ i, (if i ∈ A then 0 else V i) ≤ V i ^ ((2 : ℝ) / 5) * (Q : ℝ) ^ (-(3 : ℝ) / 2) := by
      intro i
      by_cases hi : i ∈ A
      · simp only [hi, ite_true]; exact mul_nonneg (hpos i) (Real.rpow_nonneg hQ0.le _)
      · simp only [hi, ite_false]
        have hlt : V i < t := not_le.1 fun h => hi ((hmemA i).2 h)
        rw [← ht35]
        calc V i = V i ^ ((2 : ℝ) / 5) * V i ^ ((3 : ℝ) / 5) := by
              rw [← Real.rpow_add' (hV0 i) (by norm_num)]; norm_num
          _ ≤ V i ^ ((2 : ℝ) / 5) * t ^ ((3 : ℝ) / 5) :=
              mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (hV0 i) hlt.le (by norm_num)) (hpos i)
    have hs2 : Summable fun i => V i ^ ((2 : ℝ) / 5) * (Q : ℝ) ^ (-(3 : ℝ) / 2) := hsum.mul_right _
    have hs1 : Summable fun i => (if i ∈ A then 0 else V i) :=
      Summable.of_nonneg_of_le (fun i => by split_ifs <;> simp [hV0 i]) hle hs2
    refine (hs1.tsum_le_tsum hle hs2).trans ?_
    rw [tsum_mul_right]
    exact mul_le_mul_of_nonneg_right hM (Real.rpow_nonneg hQ0.le _)

theorem s21h_tail_nat (Q : ℕ) (hQ : 1 ≤ Q) :
    ∑' n : ℕ, (if n ≤ Q then (0 : ℝ) else ((n : ℝ)) ^ (-(5 : ℝ) / 2)) ≤ 2 / 3 * (Q : ℝ) ^ (-(3 : ℝ) / 2) := by
  classical
  have hQ0 : (0 : ℝ) < Q := by exact_mod_cast hQ
  set f : ℝ → ℝ := fun x => x ^ (-(5 : ℝ) / 2) with hf
  have hanti : AntitoneOn f (Ici (Q : ℝ)) := fun x hx y hy hxy =>
    Real.rpow_le_rpow_of_nonpos (hQ0.trans_le hx) hxy (by norm_num)
  have hint : IntegrableOn f (Ioi (Q : ℝ)) := integrableOn_Ioi_rpow_of_lt (by norm_num) hQ0
  have hnn : ∀ t ∈ Ioi (Q : ℝ), 0 ≤ f t := fun t ht => Real.rpow_nonneg (hQ0.trans ht).le _
  have h1 := AntitoneOn.tsum_comp_add_le_integral Q hanti hint hnn
  have h2 : ∫ x in Ioi (Q : ℝ), f x = 2 / 3 * (Q : ℝ) ^ (-(3 : ℝ) / 2) := by
    rw [hf]
    simp only
    rw [integral_Ioi_rpow_of_lt (by norm_num) hQ0]
    rw [show -(5 : ℝ) / 2 + 1 = -(3 : ℝ) / 2 by norm_num]
    ring
  rw [h2] at h1
  have hsum : Summable fun n : ℕ => f ((n + Q + 1 : ℕ) : ℝ) := by
    have := (AntitoneOn.summable_of_integrableOn_Ioi (f := f) (N := Q) hanti hint hnn)
    exact (summable_nat_add_iff (Q + 1)).2 this |>.congr fun n => by
      show f (((n + (Q + 1) : ℕ) : ℝ)) = f ((n + Q + 1 : ℕ) : ℝ)
      congr 1
  refine le_trans (le_of_eq ?_) h1
  -- reindex `n = k + Q + 1`
  have hsum' : Summable fun n : ℕ => (if n ≤ Q then (0 : ℝ) else ((n : ℝ)) ^ (-(5 : ℝ) / 2)) := by
    refine (summable_nat_add_iff (Q + 1)).1 ?_
    refine hsum.congr fun k => ?_
    have : ¬ (k + (Q + 1) ≤ Q) := by omega
    simp only [this, ite_false, hf]
    congr 2 <;> first | done | (push_cast; ring)
  rw [← hsum'.sum_add_tsum_nat_add (Q + 1)]
  have h0 : ∑ i ∈ Finset.range (Q + 1), (if i ≤ Q then (0 : ℝ) else ((i : ℝ)) ^ (-(5 : ℝ) / 2)) = 0 := by
    refine Finset.sum_eq_zero fun i hi => ?_
    have : i ≤ Q := by simpa [Nat.lt_succ_iff] using hi
    simp [this]
  rw [h0, zero_add]
  refine tsum_congr fun k => ?_
  have : ¬ (k + (Q + 1) ≤ Q) := by omega
  simp only [this, ite_false, hf]
  congr 2 <;> first | done | (push_cast; ring)

end HRS.MS.S21
