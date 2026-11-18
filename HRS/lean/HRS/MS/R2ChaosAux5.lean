import HRS.MS.R2ChaosAux4

/-!
# HRS.MS.R2ChaosAux5 -- Wick sections of correlated Gaussian coordinates: Bessel, Cauchy, `L²`-Lipschitz bound

Packet S94, namespace `HRS.MS.R2Chaos`, helper prefix `s94_`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false
set_option linter.style.haveILetI false
set_option linter.deprecated false

open MeasureTheory ProbabilityTheory Function Set Filter
open scoped ENNReal NNReal Topology

noncomputable section

namespace HRS.MS.R2Chaos

open HRS.Whole

variable {d : ℕ}

/-! ### Bessel inequality for the coefficients `A_ij` -/

section Bessel

variable (μ : Measure (Euc d)) [IsProbabilityMeasure μ]

theorem s94_projMean_continuous {a : Euc d → ℝ} (ha : IsR2Test a) : Continuous (Whole.projMean μ a) :=
  (s94_test_continuous ha).sub continuous_const

theorem s94_projMean_bounded {a : Euc d → ℝ} (ha : IsR2Test a) :
    ∃ C : ℝ, ∀ x, |Whole.projMean μ a x| ≤ C := by
  obtain ⟨Ca, hCa⟩ := s94_test_bounded ha
  refine ⟨Ca + |Whole.pair μ a|, fun x => ?_⟩
  unfold Whole.projMean
  exact (abs_sub _ _).trans (by linarith [hCa x])

/-- A measurable function of two variables lying in `L²(μ ⊗ μ)` times bounded functions is integrable. -/
theorem s94_integrable_k_mul {k : Euc d → Euc d → ℝ} (hk2 : MemLp (fun q : Euc d × Euc d => k q.1 q.2) 2 (μ.prod μ))
    {g : Euc d × Euc d → ℝ} (hg : Measurable g) {C : ℝ} (hC : ∀ q, |g q| ≤ C) :
    Integrable (fun q : Euc d × Euc d => k q.1 q.2 * g q) (μ.prod μ) := by
  haveI : IsProbabilityMeasure (μ.prod μ) := inferInstance
  have h1 : Integrable (fun q : Euc d × Euc d => k q.1 q.2) (μ.prod μ) := hk2.integrable (by norm_num)
  exact h1.mul_bdd hg.aestronglyMeasurable (ae_of_all _ fun q => by simpa using hC q)

/-- The tensor `e_i ⊗ e_j` of the projected test functions. -/
def s94E2 (a : ℕ → Euc d → ℝ) (p : ℕ × ℕ) (q : Euc d × Euc d) : ℝ :=
  Whole.projMean μ (a p.1) q.1 * Whole.projMean μ (a p.2) q.2

variable {μ}

theorem s94E2_measurable {a : ℕ → Euc d → ℝ} (ha : ∀ i, IsR2Test (a i)) (p : ℕ × ℕ) :
    Measurable (s94E2 μ a p) :=
  (((s94_projMean_continuous μ (ha p.1)).measurable.comp measurable_fst).mul
    ((s94_projMean_continuous μ (ha p.2)).measurable.comp measurable_snd))

theorem s94E2_bounded {a : ℕ → Euc d → ℝ} (ha : ∀ i, IsR2Test (a i)) (p : ℕ × ℕ) :
    ∃ C : ℝ, ∀ q, |s94E2 μ a p q| ≤ C := by
  obtain ⟨C1, h1⟩ := s94_projMean_bounded μ (ha p.1)
  obtain ⟨C2, h2⟩ := s94_projMean_bounded μ (ha p.2)
  refine ⟨C1 * C2, fun q => ?_⟩
  unfold s94E2
  rw [abs_mul]
  exact mul_le_mul (h1 _) (h2 _) (abs_nonneg _) ((abs_nonneg _).trans (h1 q.1))

theorem s94_coeff_eq_prod {a : ℕ → Euc d → ℝ} (ha : ∀ i, IsR2Test (a i)) {k : Euc d → Euc d → ℝ}
    (hk : Measurable fun q : Euc d × Euc d => k q.1 q.2)
    (hk2 : MemLp (fun q : Euc d × Euc d => k q.1 q.2) 2 (μ.prod μ)) (i j : ℕ) :
    r2WickCoeff μ a k i j = ∫ q, k q.1 q.2 * s94E2 μ a (i, j) q ∂(μ.prod μ) := by
  obtain ⟨C, hC⟩ := s94E2_bounded (μ := μ) ha (i, j)
  have hint := s94_integrable_k_mul μ hk2 (s94E2_measurable ha (i, j)) hC
  rw [integral_prod _ hint]
  unfold r2WickCoeff s94E2
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  refine integral_congr_ae (ae_of_all _ fun y => ?_)
  simp only
  ring

theorem s94_E2_inner {a : ℕ → Euc d → ℝ} (ha : ∀ i, IsR2Test (a i))
    (hon : ∀ i j, ∫ x, Whole.projMean μ (a i) x * Whole.projMean μ (a j) x ∂μ = if i = j then 1 else 0)
    (p p' : ℕ × ℕ) :
    ∫ q, s94E2 μ a p q * s94E2 μ a p' q ∂(μ.prod μ) = if p = p' then 1 else 0 := by
  have e : ∀ q : Euc d × Euc d, s94E2 μ a p q * s94E2 μ a p' q =
      (Whole.projMean μ (a p.1) q.1 * Whole.projMean μ (a p'.1) q.1) *
        (Whole.projMean μ (a p.2) q.2 * Whole.projMean μ (a p'.2) q.2) := fun q => by
    unfold s94E2; ring
  simp_rw [e]
  rw [integral_prod_mul (μ := μ) (ν := μ) (fun x => Whole.projMean μ (a p.1) x * Whole.projMean μ (a p'.1) x)
    (fun y => Whole.projMean μ (a p.2) y * Whole.projMean μ (a p'.2) y), hon, hon]
  by_cases h1 : p.1 = p'.1 <;> by_cases h2 : p.2 = p'.2 <;> simp [Prod.ext_iff, h1, h2]

/-- Bessel inequality for the coefficients of a kernel in `L²(μ ⊗ μ)`. -/
theorem s94_bessel {a : ℕ → Euc d → ℝ} (ha : ∀ i, IsR2Test (a i))
    (hon : ∀ i j, ∫ x, Whole.projMean μ (a i) x * Whole.projMean μ (a j) x ∂μ = if i = j then 1 else 0)
    {k : Euc d → Euc d → ℝ} (hk : Measurable fun q : Euc d × Euc d => k q.1 q.2)
    (hk2 : MemLp (fun q : Euc d × Euc d => k q.1 q.2) 2 (μ.prod μ)) (F : Finset (ℕ × ℕ)) :
    ∑ p ∈ F, (r2WickCoeff μ a k p.1 p.2) ^ 2 ≤ ∫ q, (k q.1 q.2) ^ 2 ∂(μ.prod μ) := by
  set A : ℕ × ℕ → ℝ := fun p => r2WickCoeff μ a k p.1 p.2 with hA
  set g : Euc d × Euc d → ℝ := fun q => ∑ p ∈ F, A p * s94E2 μ a p q with hg
  have hAprod : ∀ p, A p = ∫ q, k q.1 q.2 * s94E2 μ a p q ∂(μ.prod μ) := fun p =>
    s94_coeff_eq_prod ha hk hk2 p.1 p.2
  have hE2m := s94E2_measurable (μ := μ) ha
  have hkE : ∀ p, Integrable (fun q => k q.1 q.2 * s94E2 μ a p q) (μ.prod μ) := fun p =>
    (s94_integrable_k_mul μ hk2 (hE2m p) (s94E2_bounded (μ := μ) ha p).choose_spec)
  have hgm : Measurable g := Finset.measurable_sum _ fun p _ => (hE2m p).const_mul _
  have hgb : ∃ C, ∀ q, |g q| ≤ C := by
    refine ⟨∑ p ∈ F, |A p| * (s94E2_bounded (μ := μ) ha p).choose, fun q => ?_⟩
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun p _ => ?_)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left ((s94E2_bounded (μ := μ) ha p).choose_spec q) (abs_nonneg _)
  obtain ⟨Cg, hCg⟩ := hgb
  have hkg : Integrable (fun q => k q.1 q.2 * g q) (μ.prod μ) := s94_integrable_k_mul μ hk2 hgm hCg
  have hk2i : Integrable (fun q : Euc d × Euc d => (k q.1 q.2) ^ 2) (μ.prod μ) := hk2.integrable_sq
  have hg2 : Integrable (fun q => g q ^ 2) (μ.prod μ) := by
    refine Integrable.of_bound (hgm.pow_const 2).aestronglyMeasurable (Cg ^ 2) (ae_of_all _ fun q => ?_)
    rw [Real.norm_eq_abs, abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (hCg q) 2
  have h1 : ∫ q, k q.1 q.2 * g q ∂(μ.prod μ) = ∑ p ∈ F, A p ^ 2 := by
    have : ∀ q, k q.1 q.2 * g q = ∑ p ∈ F, A p * (k q.1 q.2 * s94E2 μ a p q) := fun q => by
      simp only [hg, Finset.mul_sum]
      exact Finset.sum_congr rfl fun p _ => by ring
    simp_rw [this]
    rw [integral_finset_sum _ fun p _ => (hkE p).const_mul (A p)]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [integral_const_mul, ← hAprod p]
    ring
  have hE2E2 : ∀ p p', Integrable (fun q => s94E2 μ a p q * s94E2 μ a p' q) (μ.prod μ) := fun p p' => by
    obtain ⟨C1, h1⟩ := s94E2_bounded (μ := μ) ha p
    obtain ⟨C2, h2⟩ := s94E2_bounded (μ := μ) ha p'
    refine Integrable.of_bound ((hE2m p).mul (hE2m p')).aestronglyMeasurable (C1 * C2) (ae_of_all _ fun q => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (h1 q) (h2 q) (abs_nonneg _) ((abs_nonneg _).trans (h1 q))
  have h2 : ∫ q, g q ^ 2 ∂(μ.prod μ) = ∑ p ∈ F, A p ^ 2 := by
    have : ∀ q, g q ^ 2 = ∑ p ∈ F, ∑ p' ∈ F, (A p * A p') * (s94E2 μ a p q * s94E2 μ a p' q) := fun q => by
      simp only [hg, sq, Finset.sum_mul_sum]
      exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun p' _ => by ring
    simp_rw [this]
    rw [integral_finset_sum _ fun p _ => integrable_finset_sum _ fun p' _ => (hE2E2 p p').const_mul _]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [integral_finset_sum _ fun p' _ => (hE2E2 p p').const_mul _]
    simp_rw [integral_const_mul, s94_E2_inner ha hon]
    rw [Finset.sum_eq_single p (fun p' _ hp' => by simp [Ne.symm hp']) (fun h => absurd hp h)]
    simp [sq]
  have h3 : 0 ≤ ∫ q, (k q.1 q.2 - g q) ^ 2 ∂(μ.prod μ) := integral_nonneg fun q => sq_nonneg _
  have e : ∀ q : Euc d × Euc d, (k q.1 q.2 - g q) ^ 2 = (k q.1 q.2) ^ 2 - 2 * (k q.1 q.2 * g q) + g q ^ 2 :=
    fun q => by ring
  simp_rw [e] at h3
  have i2 : Integrable (fun q : Euc d × Euc d => 2 * (k q.1 q.2 * g q)) (μ.prod μ) := hkg.const_mul 2
  have i12 : Integrable (fun q : Euc d × Euc d => (k q.1 q.2) ^ 2 - 2 * (k q.1 q.2 * g q)) (μ.prod μ) :=
    hk2i.sub i2
  rw [integral_add i12 hg2, integral_sub hk2i i2, integral_const_mul, h1, h2] at h3
  linarith

end Bessel

/-! ### Finite sums over `Fin n` squares and index restriction -/

theorem s94_sum_fin_range {n : ℕ} (f : ℕ → ℝ) : ∑ i : Fin n, f i = ∑ i ∈ Finset.range n, f i :=
  Fin.sum_univ_eq_sum_range f n

theorem s94_sum_range_ind {f : ℕ → ℕ → ℝ} {m n : ℕ} (hmn : m ≤ n) :
    ∑ i ∈ Finset.range m, ∑ j ∈ Finset.range m, f i j =
      ∑ i : Fin n, ∑ j : Fin n, if (i : ℕ) < m ∧ (j : ℕ) < m then f i j else 0 := by
  have h1 : ∀ g : ℕ → ℝ, ∑ i ∈ Finset.range m, g i = ∑ i ∈ Finset.range n, if i < m then g i else 0 := by
    intro g
    rw [← Finset.sum_filter]
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext i
    simp only [Finset.mem_range, Finset.mem_filter]
    constructor
    · intro h; exact ⟨lt_of_lt_of_le h hmn, h⟩
    · intro h; exact h.2
  rw [h1]
  simp_rw [h1]
  rw [s94_sum_fin_range (n := n) (fun i => ∑ j : Fin n, if i < m ∧ (j : ℕ) < m then f i j else 0)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [s94_sum_fin_range (n := n) (fun j => if i < m ∧ j < m then f i j else 0)]
  by_cases hi : i < m
  · simp only [hi, true_and, if_true]
  · simp [hi]

/-! ### Sections of a quadratic Wick sum -/

section Sections

variable {Ω' : Type*} [MeasurableSpace Ω']

/-- The finite section `∑_{i,j<n} A_ij (z_i z_j - E z_i z_j)`. -/
def s94Sec (P' : Measure Ω') (z : ℕ → Ω' → ℝ) (A : ℕ → ℕ → ℝ) (n : ℕ) (ζ : Ω') : ℝ :=
  ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, A i j * (z i ζ * z j ζ - ∫ ζ', z i ζ' * z j ζ' ∂P')

/-- Partial sums of the squared coefficients. -/
def s94T (A : ℕ → ℕ → ℝ) (n : ℕ) : ℝ := ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, A i j ^ 2

/-- A sequence of coordinates with jointly Gaussian finite sections and covariance bound `Λ`. -/
def S94GSeq (P' : Measure Ω') (z : ℕ → Ω' → ℝ) (Λ : ℝ) : Prop :=
  ∀ n : ℕ, S94GFam P' (fun i : Fin n => z i) ∧
    ∀ α : Fin n → ℝ, s94q P' (fun i : Fin n => z i) α ≤ Λ * ∑ i, α i ^ 2

variable {P' : Measure Ω'} [IsProbabilityMeasure P'] {z : ℕ → Ω' → ℝ} {Λ : ℝ}

theorem s94_sec_diff_le (hz : S94GSeq P' z Λ) (hΛ0 : 0 ≤ Λ) {A : ℕ → ℕ → ℝ} (hA : ∀ i j, A i j = A j i)
    {m n : ℕ} (hmn : m ≤ n) :
    ∫ ζ, (s94Sec P' z A n ζ - s94Sec P' z A m ζ) ^ 2 ∂P' ≤ 2 * Λ ^ 2 * (s94T A n - s94T A m) := by
  set B : Fin n → Fin n → ℝ := fun i j => if (i : ℕ) < m ∧ (j : ℕ) < m then 0 else A i j with hB
  have hBs : ∀ i j, B i j = B j i := fun i j => by
    simp only [hB, hA i j, and_comm]
  have hpt : ∀ ζ, s94Sec P' z A n ζ - s94Sec P' z A m ζ =
      ∑ i : Fin n, ∑ j : Fin n, B i j * (z i ζ * z j ζ - ∫ ζ', z i ζ' * z j ζ' ∂P') := by
    intro ζ
    unfold s94Sec
    set g : ℕ → ℕ → ℝ := fun i j => A i j * (z i ζ * z j ζ - ∫ ζ', z i ζ' * z j ζ' ∂P') with hg
    have hfull : ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, g i j = ∑ i : Fin n, ∑ j : Fin n, g i j := by
      rw [← s94_sum_fin_range (n := n) (fun i => ∑ j ∈ Finset.range n, g i j)]
      exact Finset.sum_congr rfl fun i _ => (s94_sum_fin_range (n := n) (g i)).symm
    rw [s94_sum_range_ind (f := g) hmn, hfull, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases h : (i : ℕ) < m ∧ (j : ℕ) < m
    · simp [hB, h, hg]
    · simp [hB, h, hg]
  have hT : ∑ i : Fin n, ∑ j : Fin n, B i j ^ 2 = s94T A n - s94T A m := by
    have e : ∀ i j : Fin n, B i j ^ 2 =
        A i j ^ 2 - (if (i : ℕ) < m ∧ (j : ℕ) < m then A i j ^ 2 else 0) := fun i j => by
      by_cases h : (i : ℕ) < m ∧ (j : ℕ) < m
      · simp [hB, h]
      · simp [hB, h]
    simp_rw [e, Finset.sum_sub_distrib]
    unfold s94T
    rw [s94_sum_range_ind (f := fun i j => A i j ^ 2) hmn]
    have hfull : ∑ i : Fin n, ∑ j : Fin n, A i j ^ 2 =
        ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, A i j ^ 2 := by
      rw [s94_sum_fin_range (n := n) (fun i => ∑ j : Fin n, A i j ^ 2)]
      exact Finset.sum_congr rfl fun i _ => s94_sum_fin_range (n := n) (fun j => A i j ^ 2)
    rw [hfull]
  have hint : ∫ ζ, (s94Sec P' z A n ζ - s94Sec P' z A m ζ) ^ 2 ∂P' =
      ∫ ζ, (∑ i : Fin n, ∑ j : Fin n, B i j * (z i ζ * z j ζ - ∫ ζ', z i ζ' * z j ζ' ∂P')) ^ 2 ∂P' := by
    refine integral_congr_ae (ae_of_all _ fun ζ => ?_)
    simp only [hpt ζ]
  rw [hint]
  have := (hz n).1.quad_var hΛ0 (hz n).2 B hBs
  rw [hT] at this
  exact this

/-- Completeness of `L²`: a Cauchy sequence in the mean-square sense has a limit. -/
theorem s94_exists_L2_limit {S : ℕ → Ω' → ℝ} (hmem : ∀ n, MemLp (S n) 2 P')
    (hcau : ∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N, ∫ ζ, (S n ζ - S m ζ) ^ 2 ∂P' ≤ ε) :
    ∃ Q : Ω' → ℝ, MemLp Q 2 P' ∧ Tendsto (fun n => ∫ ζ, (S n ζ - Q ζ) ^ 2 ∂P') atTop (𝓝 0) := by
  set q : ℕ → Lp ℝ 2 P' := fun n => (hmem n).toLp (S n) with hq
  have hdist : ∀ m n, dist (q n) (q m) ^ 2 = ∫ ζ, (S n ζ - S m ζ) ^ 2 ∂P' := by
    intro m n
    rw [dist_eq_norm, HRS.Lp2_norm_sq]
    refine integral_congr_ae ?_
    have h1 := Lp.coeFn_sub (q n) (q m)
    have h2 := (hmem n).coeFn_toLp
    have h3 := (hmem m).coeFn_toLp
    filter_upwards [h1, h2, h3] with ω h1 h2 h3
    simp only [hq] at h1 h2 h3 ⊢
    rw [h1]; simp only [Pi.sub_apply]; rw [h2, h3]
  have hcauchy : CauchySeq q := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := hcau (ε ^ 2 / 2) (by positivity)
    refine ⟨N, fun m hm n hn => ?_⟩
    have hb : dist (q m) (q n) ^ 2 < ε ^ 2 := by
      rw [dist_comm, hdist m n]
      have := hN m hm n hn
      have hε2 : 0 < ε ^ 2 := by positivity
      linarith
    exact lt_of_pow_lt_pow_left₀ 2 hε.le hb
  obtain ⟨qlim, hqlim⟩ := cauchySeq_tendsto_of_complete hcauchy
  refine ⟨qlim, Lp.memLp qlim, ?_⟩
  have hd : Tendsto (fun n => dist (q n) qlim ^ 2) atTop (𝓝 0) := by
    have := (tendsto_iff_dist_tendsto_zero.1 hqlim).pow 2
    simpa using this
  have hE : ∀ n, dist (q n) qlim ^ 2 = ∫ ζ, (S n ζ - qlim ζ) ^ 2 ∂P' := by
    intro n
    rw [dist_eq_norm, HRS.Lp2_norm_sq]
    refine integral_congr_ae ?_
    have h1 := Lp.coeFn_sub (q n) qlim
    have h2 := (hmem n).coeFn_toLp
    filter_upwards [h1, h2] with ω h1 h2
    simp only [hq] at h1 h2 ⊢
    rw [h1]; simp only [Pi.sub_apply]; rw [h2]
  simpa [hE] using hd

theorem s94T_mono (A : ℕ → ℕ → ℝ) : Monotone (s94T A) := by
  intro m n hmn
  unfold s94T
  refine (Finset.sum_le_sum fun i _ => ?_).trans (Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.range_subset_range.2 hmn) fun i _ _ => Finset.sum_nonneg fun j _ => sq_nonneg _)
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 hmn) fun j _ _ => sq_nonneg _

theorem S94GFam.memLp_zz {n : ℕ} {z' : Fin n → Ω' → ℝ} (hz : S94GFam P' z') (i j : Fin n) :
    MemLp (fun ζ => z' i ζ * z' j ζ) 2 P' := by
  refine (memLp_two_iff_integrable_sq (f := fun ζ => z' i ζ * z' j ζ)
    ((hz.meas i).mul (hz.meas j)).aestronglyMeasurable).2 ?_
  have := hz.integrable_sq_mul_sq (Pi.single i 1) (Pi.single j 1)
  refine this.congr (ae_of_all _ fun ζ => ?_)
  simp [s94lin, Pi.single_apply, mul_pow]

theorem s94_sec_memLp (hz : S94GSeq P' z Λ) (A : ℕ → ℕ → ℝ) (n : ℕ) : MemLp (s94Sec P' z A n) 2 P' := by
  unfold s94Sec
  refine memLp_finset_sum _ fun i hi => memLp_finset_sum _ fun j hj => ?_
  have hzz : MemLp (fun ζ => z i ζ * z j ζ) 2 P' := by
    have hi' : i < max (i + 1) (j + 1) := lt_max_of_lt_left (Nat.lt_succ_self i)
    have hj' : j < max (i + 1) (j + 1) := lt_max_of_lt_right (Nat.lt_succ_self j)
    exact (hz (max (i + 1) (j + 1))).1.memLp_zz ⟨i, hi'⟩ ⟨j, hj'⟩
  exact (hzz.sub (memLp_const (∫ ζ', z i ζ' * z j ζ' ∂P'))).const_mul (A i j)

theorem s94_sec_limit (hz : S94GSeq P' z Λ) (hΛ0 : 0 ≤ Λ) {A : ℕ → ℕ → ℝ} (hA : ∀ i j, A i j = A j i)
    {M : ℝ} (hM : ∀ n, s94T A n ≤ M) :
    ∃ Q : Ω' → ℝ, MemLp Q 2 P' ∧ Tendsto (fun n => ∫ ζ, (s94Sec P' z A n ζ - Q ζ) ^ 2 ∂P') atTop (𝓝 0) ∧
      ∫ ζ, Q ζ ^ 2 ∂P' ≤ 2 * Λ ^ 2 * M := by
  have hTc : Tendsto (s94T A) atTop (𝓝 (⨆ n, s94T A n)) :=
    tendsto_atTop_ciSup (s94T_mono A) ⟨M, by rintro _ ⟨n, rfl⟩; exact hM n⟩
  have hcau : ∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N, ∫ ζ, (s94Sec P' z A n ζ - s94Sec P' z A m ζ) ^ 2 ∂P' ≤ ε := by
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.1 hTc.cauchySeq (ε / (2 * Λ ^ 2 + 1)) (by positivity)
    refine ⟨N, fun m hm n hn => ?_⟩
    have key : ∀ m n, N ≤ m → m ≤ n →
        ∫ ζ, (s94Sec P' z A n ζ - s94Sec P' z A m ζ) ^ 2 ∂P' ≤ ε := by
      intro m n hm hmn
      have h1 := s94_sec_diff_le hz hΛ0 hA hmn
      have h2 := hN n (hm.trans hmn) m hm
      rw [Real.dist_eq] at h2
      have h3 : s94T A n - s94T A m < ε / (2 * Λ ^ 2 + 1) := (le_abs_self _).trans_lt h2
      have h4 : 2 * Λ ^ 2 * (s94T A n - s94T A m) ≤ ε := by
        have h5 : 0 ≤ s94T A n - s94T A m := sub_nonneg.2 (s94T_mono A hmn)
        calc 2 * Λ ^ 2 * (s94T A n - s94T A m) ≤ (2 * Λ ^ 2 + 1) * (s94T A n - s94T A m) := by nlinarith
          _ ≤ (2 * Λ ^ 2 + 1) * (ε / (2 * Λ ^ 2 + 1)) := by gcongr
          _ = ε := by field_simp
      exact h1.trans h4
    rcases le_total m n with h | h
    · exact key m n hm h
    · have := key n m hn h
      refine le_of_eq_of_le (integral_congr_ae (ae_of_all _ fun ζ => ?_)) this
      simp only
      ring
  obtain ⟨Q, hQ, hlim⟩ := s94_exists_L2_limit (fun n => s94_sec_memLp hz A n) hcau
  refine ⟨Q, hQ, hlim, ?_⟩
  have hbd : ∀ n, ∫ ζ, (s94Sec P' z A n ζ) ^ 2 ∂P' ≤ 2 * Λ ^ 2 * M := by
    intro n
    have h1 := s94_sec_diff_le hz hΛ0 hA (Nat.zero_le n)
    have e0 : s94Sec P' z A 0 = fun _ => 0 := by
      funext ζ; simp [s94Sec]
    have eT : s94T A 0 = 0 := by simp [s94T]
    rw [e0, eT] at h1
    simp only [sub_zero] at h1
    refine h1.trans ?_
    have := hM n
    have h2 : 0 ≤ 2 * Λ ^ 2 := by positivity
    nlinarith
  -- `∫ Q² ≤ (1+δ)∫ S_n² + (1+1/δ)∫(S_n-Q)²`
  have hc0 : 0 ≤ 2 * Λ ^ 2 * M := by
    have := hM 0
    have h0 : s94T A 0 = 0 := by simp [s94T]
    rw [h0] at this
    positivity
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hfin : ∀ n, Integrable (fun ζ => s94Sec P' z A n ζ ^ 2) P' := fun n =>
    (s94_sec_memLp hz A n).integrable_sq
  have hQi : Integrable (fun ζ => Q ζ ^ 2) P' := hQ.integrable_sq
  have hdi : ∀ n, Integrable (fun ζ => (s94Sec P' z A n ζ - Q ζ) ^ 2) P' := fun n =>
    ((s94_sec_memLp hz A n).sub hQ).integrable_sq
  set c : ℝ := 2 * Λ ^ 2 * M with hc
  set δ : ℝ := ε / (c + 1) with hδdef
  have hδ : 0 < δ := by positivity
  have hpt : ∀ n, ∫ ζ, Q ζ ^ 2 ∂P' ≤
      (1 + δ) * c + (1 + 1 / δ) * ∫ ζ, (s94Sec P' z A n ζ - Q ζ) ^ 2 ∂P' := by
    intro n
    have hpw : ∀ ζ, Q ζ ^ 2 ≤ (1 + δ) * s94Sec P' z A n ζ ^ 2 +
        (1 + 1 / δ) * (s94Sec P' z A n ζ - Q ζ) ^ 2 := fun ζ => by
      set x := s94Sec P' z A n ζ
      set y := Q ζ
      have h2 : 0 ≤ (δ * x + (x - y)) ^ 2 / δ := by positivity
      have h3 : (δ * x + (x - y)) ^ 2 / δ = δ * x ^ 2 + 2 * x * (x - y) + (x - y) ^ 2 / δ := by
        field_simp
        ring
      have h4 : (1 + 1 / δ) * (x - y) ^ 2 = (x - y) ^ 2 + (x - y) ^ 2 / δ := by ring
      have h5 : y ^ 2 = x ^ 2 - 2 * x * (x - y) + (x - y) ^ 2 := by ring
      nlinarith
    calc ∫ ζ, Q ζ ^ 2 ∂P' ≤ ∫ ζ, ((1 + δ) * s94Sec P' z A n ζ ^ 2 +
          (1 + 1 / δ) * (s94Sec P' z A n ζ - Q ζ) ^ 2) ∂P' :=
        integral_mono hQi (((hfin n).const_mul _).add ((hdi n).const_mul _)) hpw
      _ = (1 + δ) * ∫ ζ, s94Sec P' z A n ζ ^ 2 ∂P' + (1 + 1 / δ) * ∫ ζ, (s94Sec P' z A n ζ - Q ζ) ^ 2 ∂P' := by
        rw [integral_add ((hfin n).const_mul _) ((hdi n).const_mul _), integral_const_mul, integral_const_mul]
      _ ≤ _ := by
        have := hbd n
        have h1δ : 0 ≤ 1 + δ := by linarith
        nlinarith
  have hlim' : Tendsto (fun n => (1 + δ) * c + (1 + 1 / δ) * ∫ ζ, (s94Sec P' z A n ζ - Q ζ) ^ 2 ∂P')
      atTop (𝓝 ((1 + δ) * c + (1 + 1 / δ) * 0)) := tendsto_const_nhds.add (hlim.const_mul _)
  have hle := ge_of_tendsto' hlim' hpt
  rw [mul_zero, add_zero] at hle
  have : δ * c ≤ ε := by
    rw [hδdef, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith
  linarith

end Sections

end HRS.MS.R2Chaos
