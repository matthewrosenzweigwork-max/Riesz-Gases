import HRS.MS.TransOpAux4

/-!
# S611 packet P1e: the energy estimate for axis translations

`s611_energy_bound`: for `A_α' = a_α A_{α-e_i} - b_α A_{α+e_i}`, `∑_α A_α(t)² = P` (all `t`) and `∑ λ^m A(0)² < ∞`,
`∑_{|α|≤N} λ_α^m A_α(t)² ≤ exp(2 m 3^m |t|) ∑_α λ_α^m A_α(0)²`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.TransOp

open HRS.Whole
open HRS (Euc)

variable {d : ℕ}

theorem s611_energy_bound (m : ℕ) (hm : 1 ≤ m) (i : Fin d) (A : MultiIndex d → ℝ → ℝ) (P : ℝ)
    (hA : ∀ α t, HasDerivAt (A α)
      (s611_a i α * A (s611_dec α i) t - s611_b i α * A (s611_inc α i) t) t)
    (hP : ∀ t, HasSum (fun α => A α t ^ 2) P)
    (hS : Summable (fun α => s611_w d m α * A α 0 ^ 2)) (N : ℕ) (t : ℝ) :
    ∑ α ∈ s611_D d N, s611_w d m α * A α t ^ 2 ≤
      Real.exp (2 * m * 3 ^ m * |t|) * ∑' α, s611_w d m α * A α 0 ^ 2 := by
  set W : ℝ := (2 * (N : ℝ) + d + 1) ^ m with hWdef
  set K : ℝ := 2 * m * 3 ^ m with hK
  have hK0 : 0 ≤ K := by positivity
  have hW : ∀ α : MultiIndex d, α.degree = N → s611_w d m α = W := by
    intro α hα
    unfold s611_w
    show (2 * (α.degree : ℝ) + d + 1) ^ m = _
    rw [hα]
  have hW0 : 0 ≤ W := pow_nonneg (by positivity) m
  set Q : ℝ → ℝ := fun t => ∑ α ∈ s611_D d N, s611_w d m α * A α t ^ 2 with hQ
  set E : ℝ → ℝ := fun t => W * P + ∑ α ∈ s611_D d N, (s611_w d m α - W) * A α t ^ 2 with hE
  set E' : ℝ → ℝ := fun t => ∑ α ∈ s611_D d N, (s611_w d m α - W) *
    (2 * A α t * (s611_a i α * A (s611_dec α i) t - s611_b i α * A (s611_inc α i) t)) with hE'
  have hdE : ∀ t, HasDerivAt E (E' t) t := by
    intro t
    have h1 : ∀ α ∈ s611_D d N, HasDerivAt (fun t => (s611_w d m α - W) * A α t ^ 2)
        ((s611_w d m α - W) * (2 * A α t * (s611_a i α * A (s611_dec α i) t -
          s611_b i α * A (s611_inc α i) t))) t := by
      intro α _
      have := ((hA α t).pow 2).const_mul (s611_w d m α - W)
      refine this.congr_deriv ?_
      simp
    have := HasDerivAt.fun_sum h1
    have h2 := this.const_add (W * P)
    exact h2
  have hQE : ∀ t, Q t ≤ E t := by
    intro t
    have hle : ∑ α ∈ s611_D d N, A α t ^ 2 ≤ P :=
      sum_le_hasSum _ (fun α _ => sq_nonneg _) (hP t)
    have : E t = Q t + W * (P - ∑ α ∈ s611_D d N, A α t ^ 2) := by
      simp only [hE, hQ]
      rw [Finset.sum_congr rfl (fun α _ => sub_mul (s611_w d m α) W (A α t ^ 2)),
        Finset.sum_sub_distrib, ← Finset.mul_sum]
      ring
    rw [this]
    have := mul_nonneg hW0 (sub_nonneg.2 hle)
    linarith
  have hQ0 : ∀ t, 0 ≤ Q t := fun t =>
    Finset.sum_nonneg fun α _ => mul_nonneg (pow_nonneg (oscEv_pos α).le m) (sq_nonneg _)
  have hbE : ∀ t, |E' t| ≤ K * E t := by
    intro t
    have hid := s611_deriv_sum_eq N i (s611_w d m) W hW (fun α => A α t)
    have hb := s611_sum_bound m hm N i (fun α => A α t)
    have : E' t = 2 * ∑ β ∈ (s611_D d N).filter (fun β => 1 ≤ β i),
        s611_a i β * A β t * A (s611_dec β i) t *
          (s611_w d m β - s611_w d m (s611_dec β i)) := hid
    rw [this, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have h3 : |∑ β ∈ (s611_D d N).filter (fun β => 1 ≤ β i),
        s611_a i β * A β t * A (s611_dec β i) t *
          (s611_w d m β - s611_w d m (s611_dec β i))| ≤
        ((m : ℝ) * 3 ^ m / 2) * (2 * Q t) := hb
    calc 2 * |∑ β ∈ (s611_D d N).filter (fun β => 1 ≤ β i),
        s611_a i β * A β t * A (s611_dec β i) t *
          (s611_w d m β - s611_w d m (s611_dec β i))|
        ≤ 2 * (((m : ℝ) * 3 ^ m / 2) * (2 * Q t)) := by gcongr
      _ = K * Q t := by rw [hK]; ring
      _ ≤ K * E t := by gcongr; exact hQE t
  have hgr := s611_gronwall E E' K hK0 hdE hbE t
  -- bound at time 0
  have hE0 : E 0 ≤ ∑' α, s611_w d m α * A α 0 ^ 2 := by
    have hsum1 : Summable (fun α => A α 0 ^ 2) := (hP 0).summable
    set s := s611_D d N with hs
    have hP0 : P = ∑' α, A α 0 ^ 2 := (hP 0).tsum_eq.symm
    have e1 : ∑ α ∈ s, A α 0 ^ 2 + ∑' α : ↥((s : Set (MultiIndex d))ᶜ), A α 0 ^ 2 = P := by
      rw [hP0]; exact hsum1.sum_add_tsum_compl
    have e2 : ∑ α ∈ s, s611_w d m α * A α 0 ^ 2 +
        ∑' α : ↥((s : Set (MultiIndex d))ᶜ), s611_w d m α * A α 0 ^ 2 =
        ∑' α, s611_w d m α * A α 0 ^ 2 := hS.sum_add_tsum_compl
    have htail : W * ∑' α : ↥((s : Set (MultiIndex d))ᶜ), A α 0 ^ 2 ≤
        ∑' α : ↥((s : Set (MultiIndex d))ᶜ), s611_w d m α * A α 0 ^ 2 := by
      rw [← tsum_mul_left]
      refine Summable.tsum_le_tsum (fun α => ?_) ((hsum1.subtype _).mul_left W) (hS.subtype _)
      have hα : ¬ (α.1.degree ≤ N) := by
        have := α.2
        simp only [Set.mem_compl_iff, Finset.mem_coe, hs, s611_mem_D] at this
        exact this
      have hl : (2 * (N : ℝ) + d + 1) ≤ oscEigenvalue d α.1 := by
        show _ ≤ 2 * (α.1.degree : ℝ) + d + 1
        have : (N : ℝ) ≤ (α.1.degree : ℝ) := by exact_mod_cast (by omega : N ≤ α.1.degree)
        linarith
      have : W ≤ s611_w d m α.1 := pow_le_pow_left₀ (by positivity) hl m
      exact mul_le_mul_of_nonneg_right this (sq_nonneg _)
    have : E 0 = ∑ α ∈ s, s611_w d m α * A α 0 ^ 2 +
        W * ∑' α : ↥((s : Set (MultiIndex d))ᶜ), A α 0 ^ 2 := by
      simp only [hE]
      rw [Finset.sum_congr rfl (fun α _ => sub_mul (s611_w d m α) W (A α 0 ^ 2)),
        Finset.sum_sub_distrib, ← Finset.mul_sum, ← e1]
      ring
    rw [this, ← e2]
    linarith
  calc ∑ α ∈ s611_D d N, s611_w d m α * A α t ^ 2 = Q t := rfl
    _ ≤ E t := hQE t
    _ ≤ Real.exp (K * |t|) * E 0 := hgr
    _ ≤ Real.exp (K * |t|) * ∑' α, s611_w d m α * A α 0 ^ 2 := by
        gcongr

end HRS.MS.TransOp

end
