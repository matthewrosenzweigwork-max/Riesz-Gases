import HRS.MS.S111X2Aux39

/-!
# S11.1 X2, packet H02 (part 2): the discrete Sobolev bound for the grid interpolation
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

open MeasureTheory Filter Topology Set
open scoped BigOperators

namespace HRS.MS.S111X2

open HRS HRS.Whole HRS.MS.R2Interp HRS.Sec7

variable {d : ℕ} {m T : ℝ}

theorem s111x2_e_inner (α β : MultiIndex d) :
    inner ℝ (s102_e (m := m) α) (s102_e (m := m) β) = if α = β then (1 : ℝ) else 0 := by
  classical
  unfold s102_e
  have := lp.inner_single_left (𝕜 := ℝ) (G := fun _ : MultiIndex d => ℝ) α (1 : ℝ)
    (lp.single 2 β (1 : ℝ))
  erw [this]
  simp [lp.single_apply, Pi.single_apply, eq_comm]

theorem s111x2_norm_sq_comb (A : Finset (MultiIndex d)) (a : MultiIndex d → ℝ) :
    ‖∑ α ∈ A, a α • s102_e (m := m) α‖ ^ 2 = ∑ α ∈ A, a α ^ 2 := by
  classical
  rw [← real_inner_self_eq_norm_sq, sum_inner]
  refine Finset.sum_congr rfl fun α hα => ?_
  rw [inner_sum]
  simp only [inner_smul_left, inner_smul_right, s111x2_e_inner, RCLike.conj_to_real]
  simp [mul_ite, Finset.sum_ite_eq, sq, hα]

theorem s111x2_at_sum {ι : Type*} (s : Finset ι) (c : ι → ℝ) (f : ι → OscPath d m T) (t : Set.Icc (0 : ℝ) T) :
    OscPath.at' (∑ i ∈ s, c i • f i) t = ∑ i ∈ s, c i • OscPath.at' (f i) t := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]; rfl

theorem s111x2_path_norm_sq (hT : 0 < T) (L : ℕ) (A : Finset (MultiIndex d)) (v : ℕ × MultiIndex d → ℝ) (r : ℝ)
    (hr : ∀ i ≤ 2 ^ L, ∑ α ∈ A, v (i, α) ^ 2 ≤ r) :
    ‖∑ p ∈ (Finset.range (2 ^ L + 1)) ×ˢ A, v p • s102_bpath (m := m) T L p‖ ^ 2 ≤ r := by
  classical
  have hr0 : 0 ≤ r := (Finset.sum_nonneg fun α _ => sq_nonneg _).trans (hr 0 (Nat.zero_le _))
  set w := ∑ p ∈ (Finset.range (2 ^ L + 1)) ×ˢ A, v p • s102_bpath (m := m) T L p with hw
  have hn : ‖w‖ ≤ Real.sqrt r := by
    refine (ContinuousMap.norm_le (show C(Set.Icc (0 : ℝ) T, OscDual d m) from w)
      (Real.sqrt_nonneg _)).2 fun t => ?_
    have hs0 : 0 ≤ (t : ℝ) * 2 ^ L / T := by
      have := t.2.1; positivity
    have hsN : (t : ℝ) * 2 ^ L / T ≤ ((2 ^ L : ℕ) : ℝ) := by
      rw [div_le_iff₀ hT]; push_cast
      have := t.2.2
      nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) L]
    have hsum := q17_hat_sum (2 ^ L) _ hs0 hsN
    have hev : OscPath.at' w t =
        ∑ i ∈ Finset.range (2 ^ L + 1), q17_hat ((t : ℝ) * 2 ^ L / T) i •
        ∑ α ∈ A, v (i, α) • s102_e (m := m) α := by
      rw [hw, s111x2_at_sum, Finset.sum_product]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun α _ => ?_
      show v (i, α) • (q17_hat ((t : ℝ) * 2 ^ L / T) i • s102_e (m := m) α) = _
      rw [smul_comm]
    change ‖OscPath.at' w t‖ ≤ _
    rw [hev]
    refine (norm_sum_le _ _).trans ?_
    calc ∑ i ∈ Finset.range (2 ^ L + 1), ‖q17_hat ((t : ℝ) * 2 ^ L / T) i •
          ∑ α ∈ A, v (i, α) • s102_e (m := m) α‖
        ≤ ∑ i ∈ Finset.range (2 ^ L + 1), q17_hat ((t : ℝ) * 2 ^ L / T) i * Real.sqrt r := by
          refine Finset.sum_le_sum fun i hi => ?_
          rw [norm_smul, Real.norm_of_nonneg (q17_hat_nonneg _ _)]
          refine mul_le_mul_of_nonneg_left ?_ (q17_hat_nonneg _ _)
          have := hr i (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi))
          have h2 := s111x2_norm_sq_comb (m := m) A (fun α => v (i, α))
          rw [← Real.sqrt_sq (norm_nonneg _), h2]
          exact Real.sqrt_le_sqrt this
      _ = Real.sqrt r := by rw [← Finset.sum_mul, hsum, one_mul]
  calc ‖w‖ ^ 2 ≤ (Real.sqrt r) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hn 2
    _ = r := Real.sq_sqrt hr0

theorem s111x2_sobolev {ι : Type*} (A : Finset ι) (N : ℕ) (v : ℕ → ι → ℝ) {i : ℕ} (hi : i ≤ N) :
    ∑ α ∈ A, v i α ^ 2 ≤ 2 * ∑ α ∈ A, v 0 α ^ 2 +
      2 * N * ∑ j ∈ Finset.range N, ∑ α ∈ A, (v (j + 1) α - v j α) ^ 2 := by
  have hpt : ∀ α, v i α ^ 2 ≤ 2 * v 0 α ^ 2 + 2 * N * ∑ j ∈ Finset.range N, (v (j + 1) α - v j α) ^ 2 := by
    intro α
    have h1 : v i α = v 0 α + ∑ j ∈ Finset.range i, (v (j + 1) α - v j α) := by
      rw [Finset.sum_range_sub (fun j => v j α) i]; ring
    have h2 := sq_sum_le_card_mul_sum_sq (s := Finset.range i) (f := fun j => v (j + 1) α - v j α)
    simp only [Finset.card_range] at h2
    have h3 : ∑ j ∈ Finset.range i, (v (j + 1) α - v j α) ^ 2 ≤ ∑ j ∈ Finset.range N, (v (j + 1) α - v j α) ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hi) (fun j _ _ => sq_nonneg _)
    have hiN : (i : ℝ) ≤ N := by exact_mod_cast hi
    have hS : 0 ≤ ∑ j ∈ Finset.range N, (v (j + 1) α - v j α) ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
    have h4 : (i : ℝ) * ∑ j ∈ Finset.range i, (v (j + 1) α - v j α) ^ 2 ≤
        N * ∑ j ∈ Finset.range N, (v (j + 1) α - v j α) ^ 2 := by
      have hS' : 0 ≤ ∑ j ∈ Finset.range i, (v (j + 1) α - v j α) ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
      nlinarith
    rw [h1]
    nlinarith [sq_nonneg (v 0 α - ∑ j ∈ Finset.range i, (v (j + 1) α - v j α))]
  calc ∑ α ∈ A, v i α ^ 2
      ≤ ∑ α ∈ A, (2 * v 0 α ^ 2 + 2 * N * ∑ j ∈ Finset.range N, (v (j + 1) α - v j α) ^ 2) :=
        Finset.sum_le_sum fun α _ => hpt α
    _ = 2 * ∑ α ∈ A, v 0 α ^ 2 + 2 * N * ∑ j ∈ Finset.range N, ∑ α ∈ A, (v (j + 1) α - v j α) ^ 2 := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_comm]

/-- **Quadratic bound** for a positive semidefinite kernel on the grid-and-Hermite index set. -/
theorem s111x2_quad_bound (hT : 0 < T) (L : ℕ) (A : Finset (MultiIndex d))
    (M : OscPath d m T [×2]→L[ℝ] ℝ) (hM : ‖M‖ ≤ 1) (K : ℕ × MultiIndex d → ℕ × MultiIndex d → ℝ)
    (hsymm : ∀ p ∈ (Finset.range (2 ^ L + 1)) ×ˢ A, ∀ q ∈ (Finset.range (2 ^ L + 1)) ×ˢ A, K p q = K q p)
    (hpsd : ∀ c : ℕ × MultiIndex d → ℝ, 0 ≤ ∑ p ∈ (Finset.range (2 ^ L + 1)) ×ˢ A,
      ∑ q ∈ (Finset.range (2 ^ L + 1)) ×ˢ A, c p * c q * K p q) :
    |∑ p ∈ (Finset.range (2 ^ L + 1)) ×ˢ A, ∑ q ∈ (Finset.range (2 ^ L + 1)) ×ˢ A,
        K p q * M ![s102_bpath (m := m) T L p, s102_bpath (m := m) T L q]| ≤
      2 * ∑ α ∈ A, K (0, α) (0, α) + 2 * (2 ^ L : ℕ) * ∑ j ∈ Finset.range (2 ^ L), ∑ α ∈ A,
        (K (j + 1, α) (j + 1, α) - 2 * K (j, α) (j + 1, α) + K (j, α) (j, α)) := by
  classical
  obtain ⟨m', v, hv, hb⟩ := s111x2_quad_decomp M hM _ (fun p => s102_bpath (m := m) T L p) K hsymm hpsd
  refine hb.trans ?_
  have hN : (0 : ℕ) < 2 ^ L := by positivity
  have hin : ∀ α ∈ A, ∀ i ≤ 2 ^ L, (i, α) ∈ (Finset.range (2 ^ L + 1)) ×ˢ A := fun α hα i hi =>
    Finset.mem_product.2 ⟨Finset.mem_range.2 (Nat.lt_succ_of_le hi), hα⟩
  have hk : ∀ k : Fin m', ‖∑ p ∈ (Finset.range (2 ^ L + 1)) ×ˢ A, v k p • s102_bpath (m := m) T L p‖ ^ 2 ≤
      2 * ∑ α ∈ A, v k (0, α) ^ 2 + 2 * (2 ^ L : ℕ) * ∑ j ∈ Finset.range (2 ^ L), ∑ α ∈ A,
        (v k (j + 1, α) - v k (j, α)) ^ 2 := by
    intro k
    refine s111x2_path_norm_sq hT L A (v k) _ fun i hi => ?_
    have := s111x2_sobolev A (2 ^ L) (fun i α => v k (i, α)) hi
    simpa using this
  refine (Finset.sum_le_sum fun k _ => hk k).trans (le_of_eq ?_)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  congr 1
  · congr 1
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun α hα => ?_
    rw [hv _ (hin α hα 0 (Nat.zero_le _)) _ (hin α hα 0 (Nat.zero_le _))]
    simp [sq]
  · congr 1
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun α hα => ?_
    have hj1 : j + 1 ≤ 2 ^ L := Finset.mem_range.1 hj
    have hj0 : j ≤ 2 ^ L := by omega
    rw [hv _ (hin α hα (j + 1) hj1) _ (hin α hα (j + 1) hj1), hv _ (hin α hα j hj0) _ (hin α hα (j + 1) hj1),
      hv _ (hin α hα j hj0) _ (hin α hα j hj0)]
    simp only [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => by ring

end HRS.MS.S111X2
