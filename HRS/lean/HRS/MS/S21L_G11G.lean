import HRS.MS.S21L_G11E

/-!
# S21L G11G -- the `L²(P;B)` limit of the vector Wick sections (R26-T3.G11, eighth step)

For symmetric `V_ij ∈ B` with `∑_{i,j<n} ‖V_ij‖² ≤ M` and jointly Gaussian coordinates `z` (`S94GSeq`, bound `Λ`), the vector sections
`S_n = ∑_{i,j<n} (z_i z_j - E z_i z_j) • V_ij` form a Cauchy sequence in `L²(P;B)` (`s21l_vec_isometry` applied to the block
differences), so they converge to some `Q0 ∈ L²(P;B)` with `E ‖Q0‖² ≤ 2 Λ² M` (`s21l_sections_limit`).  Prefix `s21l_`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.longLine false
set_option linter.deprecated false
noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.R26T3

open HRS.MS.R2Chaos HRS.Whole

theorem s21l_sum_range_ite {M : Type*} [AddCommMonoid M] (f : ℕ → ℕ → M) (m n : ℕ) (hmn : m ≤ n) :
    ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, (if i < m ∧ j < m then f i j else 0) =
      ∑ i ∈ Finset.range m, ∑ j ∈ Finset.range m, f i j := by
  have h1 : ∀ i, i < m → ∑ j ∈ Finset.range n, (if i < m ∧ j < m then f i j else 0) =
      ∑ j ∈ Finset.range m, f i j := by
    intro i hi
    rw [← Finset.sum_subset (Finset.range_mono hmn) (fun j _ hj => by
      simp only [Finset.mem_range, not_lt] at hj; simp [not_lt.2 hj])]
    refine Finset.sum_congr rfl fun j hj => ?_
    simp only [Finset.mem_range] at hj
    simp [hi, hj]
  rw [← Finset.sum_subset (Finset.range_mono hmn) (fun i _ hi => by
    simp only [Finset.mem_range, not_lt] at hi
    refine Finset.sum_eq_zero fun j _ => by simp [not_lt.2 hi])]
  refine Finset.sum_congr rfl fun i hi => h1 i (Finset.mem_range.1 hi)

section Lim

variable {B : Type*} [NormedAddCommGroup B] [InnerProductSpace ℝ B] [CompleteSpace B]
  [MeasurableSpace B] [BorelSpace B] [SecondCountableTopology B]
variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

theorem s21l_Lp_norm_sq (f : Lp B 2 P) : ‖f‖ ^ 2 = ∫ ω, ‖f ω‖ ^ 2 ∂P := by
  rw [← real_inner_self_eq_norm_sq, MeasureTheory.L2.inner_def]
  exact integral_congr_ae (ae_of_all _ fun ω => real_inner_self_eq_norm_sq _)

theorem s21l_sections_limit {z : ℕ → Ω → ℝ} {Λ : ℝ} (hz : S94GSeq P z Λ) (hΛ0 : 0 ≤ Λ) {V : ℕ → ℕ → B}
    (hVs : ∀ i j, V i j = V j i) {M : ℝ}
    (hM : ∀ n, ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, ‖V i j‖ ^ 2 ≤ M) :
    ∃ Q0 : Ω → B, AEStronglyMeasurable Q0 P ∧ MemLp Q0 2 P ∧
      Tendsto (fun n => ∫ ω, ‖(∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
        (z i ω * z j ω - ∫ ζ, z i ζ * z j ζ ∂P) • V i j) - Q0 ω‖ ^ 2 ∂P) atTop (𝓝 0) ∧
      ∫ ω, ‖Q0 ω‖ ^ 2 ∂P ≤ 2 * Λ ^ 2 * M := by
  set S : ℕ → Ω → B := fun n ω => ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
    (z i ω * z j ω - ∫ ζ, z i ζ * z j ζ ∂P) • V i j with hS
  set τ : ℕ → ℝ := fun n => ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, ‖V i j‖ ^ 2 with hτ
  have hSL : ∀ n, MemLp (S n) 2 P := fun n => (s21l_vec_isometry hz hΛ0 hVs n).1
  have hSb : ∀ n, ∫ ω, ‖S n ω‖ ^ 2 ∂P ≤ 2 * Λ ^ 2 * τ n := fun n => (s21l_vec_isometry hz hΛ0 hVs n).2
  have hτmono : Monotone τ := by
    refine monotone_nat_of_le_succ fun m => ?_
    simp only [hτ]
    refine (Finset.sum_le_sum fun i _ => Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.range_subset_range.2 (Nat.le_succ m)) fun j _ _ => sq_nonneg _).trans ?_
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 (Nat.le_succ m))
      fun i _ _ => Finset.sum_nonneg fun j _ => sq_nonneg _
  have hτc : Tendsto τ atTop (𝓝 (⨆ n, τ n)) := tendsto_atTop_ciSup hτmono ⟨M, by rintro _ ⟨n, rfl⟩; exact hM n⟩
  -- block differences
  have hdiff : ∀ m n, m ≤ n → ∫ ω, ‖S n ω - S m ω‖ ^ 2 ∂P ≤ 2 * Λ ^ 2 * (τ n - τ m) := by
    intro m n hmn
    set C : ℕ → ℕ → B := fun i j => if i < m ∧ j < m then 0 else V i j with hC
    have hCs : ∀ i j, C i j = C j i := fun i j => by
      simp only [hC, hVs i j, and_comm]
    have hpt : ∀ ω, S n ω - S m ω = ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
        (z i ω * z j ω - ∫ ζ, z i ζ * z j ζ ∂P) • C i j := by
      intro ω
      have h1 := s21l_sum_range_ite (fun i j => (z i ω * z j ω - ∫ ζ, z i ζ * z j ζ ∂P) • V i j) m n hmn
      simp only [hS]
      rw [← h1, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      by_cases h : i < m ∧ j < m <;> simp [hC, h]
    have := (s21l_vec_isometry hz hΛ0 hCs n).2
    simp_rw [← hpt] at this
    refine this.trans ?_
    have hCn : ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, ‖C i j‖ ^ 2 = τ n - τ m := by
      have h2 := s21l_sum_range_ite (fun i j => ‖V i j‖ ^ 2) m n hmn
      have e : ∀ i j, ‖C i j‖ ^ 2 = ‖V i j‖ ^ 2 - (if i < m ∧ j < m then ‖V i j‖ ^ 2 else 0) := fun i j => by
        by_cases h : i < m ∧ j < m <;> simp [hC, h]
      simp_rw [e, Finset.sum_sub_distrib]
      simp only [hτ]
      rw [h2]
    rw [hCn]
  -- Cauchy in `L²(P;B)`
  set s : ℕ → Lp B 2 P := fun n => (hSL n).toLp (S n) with hs
  have hd : ∀ m n, m ≤ n → dist (s n) (s m) ^ 2 ≤ 2 * Λ ^ 2 * (τ n - τ m) := by
    intro m n hmn
    rw [dist_eq_norm, s21l_Lp_norm_sq]
    refine le_trans (le_of_eq (integral_congr_ae ?_)) (hdiff m n hmn)
    filter_upwards [Lp.coeFn_sub (s n) (s m), (hSL n).coeFn_toLp, (hSL m).coeFn_toLp] with ω h1 h2 h3
    rw [h1, Pi.sub_apply]
    simp only [hs, h2, h3]
  have hcau : CauchySeq s := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.1 hτc.cauchySeq (ε ^ 2 / (2 * Λ ^ 2 + 1)) (by positivity)
    refine ⟨N, fun m hm n hn => ?_⟩
    have key : ∀ m n, N ≤ m → m ≤ n → dist (s n) (s m) < ε := by
      intro m n hm hmn
      have h1 := hd m n hmn
      have h2 := hN n (hm.trans hmn) m hm
      rw [Real.dist_eq] at h2
      have h3 : τ n - τ m < ε ^ 2 / (2 * Λ ^ 2 + 1) := (le_abs_self _).trans_lt h2
      have h5 : 0 ≤ τ n - τ m := sub_nonneg.2 (hτmono hmn)
      have h4 : 2 * Λ ^ 2 * (τ n - τ m) < ε ^ 2 := by
        calc 2 * Λ ^ 2 * (τ n - τ m) ≤ (2 * Λ ^ 2 + 1) * (τ n - τ m) := by nlinarith
          _ < (2 * Λ ^ 2 + 1) * (ε ^ 2 / (2 * Λ ^ 2 + 1)) := by gcongr
          _ = ε ^ 2 := by field_simp
      have : dist (s n) (s m) ^ 2 < ε ^ 2 := h1.trans_lt h4
      exact lt_of_pow_lt_pow_left₀ 2 hε.le this
    rcases le_total m n with h | h
    · rw [dist_comm]; exact key m n hm h
    · exact key n m hn h
  obtain ⟨q, hq⟩ := cauchySeq_tendsto_of_complete hcau
  refine ⟨q, (Lp.aestronglyMeasurable q), Lp.memLp q, ?_, ?_⟩
  · have h1 : ∀ n, ∫ ω, ‖S n ω - q ω‖ ^ 2 ∂P = dist (s n) q ^ 2 := by
      intro n
      rw [dist_eq_norm, s21l_Lp_norm_sq]
      refine (integral_congr_ae ?_).symm
      filter_upwards [Lp.coeFn_sub (s n) q, (hSL n).coeFn_toLp] with ω h1 h2
      rw [h1, Pi.sub_apply]
      simp only [hs, h2]
    refine Tendsto.congr (fun n => (h1 n).symm) ?_
    have := ((tendsto_iff_dist_tendsto_zero.1 hq).pow 2)
    simpa using this
  · have h1 : ∀ n, ‖s n‖ ^ 2 ≤ 2 * Λ ^ 2 * M := fun n => by
      rw [s21l_Lp_norm_sq]
      refine le_trans (le_of_eq (integral_congr_ae ?_)) ((hSb n).trans ?_)
      · filter_upwards [(hSL n).coeFn_toLp] with ω h2
        simp only [hs, h2]
      · exact mul_le_mul_of_nonneg_left (hM n) (by positivity)
    have h2 : Tendsto (fun n => ‖s n‖ ^ 2) atTop (𝓝 (‖q‖ ^ 2)) := ((continuous_norm.tendsto q).comp hq).pow 2
    have := le_of_tendsto' h2 h1
    rwa [s21l_Lp_norm_sq] at this

end Lim

end HRS.MS.R26T3
