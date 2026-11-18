import HRS.MS.R2ChaosAux5

/-!
# HRS.MS.R2ChaosAux6 -- the Wick chaos `I_2(k)` of a kernel `k ∈ L²(μ ⊗ μ)` for a correlated Gaussian family

Packet S94, namespace `HRS.MS.R2Chaos`, helper prefix `s94_`.

`s94WickL2`: mean-square convergence of the sections to `Q` (Bochner form).  Existence for every orthonormal family
`(a_i)` (`s94_wick_exists`), the bound `E Q² ≤ 2Λ² ‖k‖²_{L²(μ⊗μ)}` and the Lipschitz estimate in the kernel.
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

section Coeff

variable {μ : Measure (Euc d)} [IsProbabilityMeasure μ]

theorem s94_coeff_symm {a : ℕ → Euc d → ℝ} (ha : ∀ i, IsR2Test (a i)) {k : Euc d → Euc d → ℝ}
    (hk : Measurable fun q : Euc d × Euc d => k q.1 q.2) (hksym : ∀ x y, k x y = k y x)
    (hk2 : MemLp (fun q : Euc d × Euc d => k q.1 q.2) 2 (μ.prod μ)) (i j : ℕ) :
    r2WickCoeff μ a k i j = r2WickCoeff μ a k j i := by
  rw [s94_coeff_eq_prod ha hk hk2, s94_coeff_eq_prod ha hk hk2]
  rw [← integral_prod_swap (μ := μ) (ν := μ) (fun q : Euc d × Euc d => k q.1 q.2 * s94E2 μ a (i, j) q)]
  refine integral_congr_ae (ae_of_all _ fun q => ?_)
  simp only [Prod.fst_swap, Prod.snd_swap, s94E2]
  rw [hksym q.2 q.1]
  ring

theorem s94_coeff_sub {a : ℕ → Euc d → ℝ} (ha : ∀ i, IsR2Test (a i)) {k k' : Euc d → Euc d → ℝ}
    (hk : Measurable fun q : Euc d × Euc d => k q.1 q.2)
    (hk2 : MemLp (fun q : Euc d × Euc d => k q.1 q.2) 2 (μ.prod μ))
    (hk' : Measurable fun q : Euc d × Euc d => k' q.1 q.2)
    (hk2' : MemLp (fun q : Euc d × Euc d => k' q.1 q.2) 2 (μ.prod μ)) (i j : ℕ) :
    r2WickCoeff μ a (fun x y => k x y - k' x y) i j = r2WickCoeff μ a k i j - r2WickCoeff μ a k' i j := by
  have hd : Measurable fun q : Euc d × Euc d => (fun x y => k x y - k' x y) q.1 q.2 := hk.sub hk'
  have hd2 : MemLp (fun q : Euc d × Euc d => (fun x y => k x y - k' x y) q.1 q.2) 2 (μ.prod μ) := hk2.sub hk2'
  rw [s94_coeff_eq_prod ha hd hd2, s94_coeff_eq_prod ha hk hk2, s94_coeff_eq_prod ha hk' hk2']
  obtain ⟨C, hC⟩ := s94E2_bounded (μ := μ) ha (i, j)
  have h1 := s94_integrable_k_mul μ hk2 (s94E2_measurable ha (i, j)) hC
  have h2 := s94_integrable_k_mul μ hk2' (s94E2_measurable ha (i, j)) hC
  rw [← integral_sub h1 h2]
  refine integral_congr_ae (ae_of_all _ fun q => ?_)
  simp only
  ring

end Coeff

/-! ### Wick chaos of a kernel -/

section Wick

variable {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']

/-- Generic: an `L²` limit of random variables with second moments `≤ c` has second moment `≤ c`. -/
theorem s94_L2_bound_of_tendsto {S : ℕ → Ω' → ℝ} {R : Ω' → ℝ} (hS : ∀ n, MemLp (S n) 2 P')
    (hR : MemLp R 2 P') (hlim : Tendsto (fun n => ∫ ζ, (S n ζ - R ζ) ^ 2 ∂P') atTop (𝓝 0)) {c : ℝ}
    (hc0 : 0 ≤ c) (hbd : ∀ n, ∫ ζ, S n ζ ^ 2 ∂P' ≤ c) : ∫ ζ, R ζ ^ 2 ∂P' ≤ c := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hfin : ∀ n, Integrable (fun ζ => S n ζ ^ 2) P' := fun n => (hS n).integrable_sq
  have hQi : Integrable (fun ζ => R ζ ^ 2) P' := hR.integrable_sq
  have hdi : ∀ n, Integrable (fun ζ => (S n ζ - R ζ) ^ 2) P' := fun n => ((hS n).sub hR).integrable_sq
  set δ : ℝ := ε / (c + 1) with hδdef
  have hδ : 0 < δ := by positivity
  have hpt : ∀ n, ∫ ζ, R ζ ^ 2 ∂P' ≤ (1 + δ) * c + (1 + 1 / δ) * ∫ ζ, (S n ζ - R ζ) ^ 2 ∂P' := by
    intro n
    have hpw : ∀ ζ, R ζ ^ 2 ≤ (1 + δ) * S n ζ ^ 2 + (1 + 1 / δ) * (S n ζ - R ζ) ^ 2 := fun ζ => by
      set x := S n ζ
      set y := R ζ
      have h2 : 0 ≤ (δ * x + (x - y)) ^ 2 / δ := by positivity
      have h3 : (δ * x + (x - y)) ^ 2 / δ = δ * x ^ 2 + 2 * x * (x - y) + (x - y) ^ 2 / δ := by
        field_simp
        ring
      have h4 : (1 + 1 / δ) * (x - y) ^ 2 = (x - y) ^ 2 + (x - y) ^ 2 / δ := by ring
      have h5 : y ^ 2 = x ^ 2 - 2 * x * (x - y) + (x - y) ^ 2 := by ring
      nlinarith
    calc ∫ ζ, R ζ ^ 2 ∂P' ≤ ∫ ζ, ((1 + δ) * S n ζ ^ 2 + (1 + 1 / δ) * (S n ζ - R ζ) ^ 2) ∂P' :=
        integral_mono hQi (((hfin n).const_mul _).add ((hdi n).const_mul _)) hpw
      _ = (1 + δ) * ∫ ζ, S n ζ ^ 2 ∂P' + (1 + 1 / δ) * ∫ ζ, (S n ζ - R ζ) ^ 2 ∂P' := by
        rw [integral_add ((hfin n).const_mul _) ((hdi n).const_mul _), integral_const_mul, integral_const_mul]
      _ ≤ _ := by
        have := hbd n
        have h1δ : 0 ≤ 1 + δ := by linarith
        nlinarith
  have hlim' : Tendsto (fun n => (1 + δ) * c + (1 + 1 / δ) * ∫ ζ, (S n ζ - R ζ) ^ 2 ∂P')
      atTop (𝓝 ((1 + δ) * c + (1 + 1 / δ) * 0)) := tendsto_const_nhds.add (hlim.const_mul _)
  have hle := ge_of_tendsto' hlim' hpt
  rw [mul_zero, add_zero] at hle
  have : δ * c ≤ ε := by
    rw [hδdef, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith
  linarith

/-- Mean-square convergence of the Wick sections of the kernel `k` to `Q`. -/
def s94WickL2 (P' : Measure Ω') (μ : Measure (Euc d)) (a : ℕ → Euc d → ℝ) (z : ℕ → Ω' → ℝ)
    (k : Euc d → Euc d → ℝ) (Q : Ω' → ℝ) : Prop :=
  MemLp Q 2 P' ∧ Tendsto (fun n => ∫ ζ, (s94Sec P' z (fun i j => r2WickCoeff μ a k i j) n ζ - Q ζ) ^ 2 ∂P')
    atTop (𝓝 0)

variable {μ : Measure (Euc d)} [IsProbabilityMeasure μ] {z : ℕ → Ω' → ℝ} {Λ : ℝ}

theorem s94WickL2.isWick {a : ℕ → Euc d → ℝ} {k : Euc d → Euc d → ℝ} {Q : Ω' → ℝ}
    (hz : S94GSeq P' z Λ) (h : s94WickL2 P' μ a z k Q) : IsR2WickChaos P' μ a z k Q :=
  HRS.tendstoL2_of_memLp h.1 (fun n => s94_sec_memLp hz _ n) h.2

/-- Existence of the Wick chaos of a symmetric kernel in `L²(μ ⊗ μ)`, with the isometry bound. -/
theorem s94_wick_exists (hz : S94GSeq P' z Λ) (hΛ0 : 0 ≤ Λ) {a : ℕ → Euc d → ℝ} (ha : ∀ i, IsR2Test (a i))
    (hon : ∀ i j, ∫ x, Whole.projMean μ (a i) x * Whole.projMean μ (a j) x ∂μ = if i = j then 1 else 0)
    {k : Euc d → Euc d → ℝ} (hk : Measurable fun q : Euc d × Euc d => k q.1 q.2)
    (hksym : ∀ x y, k x y = k y x) (hk2 : MemLp (fun q : Euc d × Euc d => k q.1 q.2) 2 (μ.prod μ)) :
    ∃ Q, s94WickL2 P' μ a z k Q ∧ ∫ ζ, Q ζ ^ 2 ∂P' ≤ 2 * Λ ^ 2 * ∫ q, (k q.1 q.2) ^ 2 ∂(μ.prod μ) := by
  have hsym : ∀ i j, r2WickCoeff μ a k i j = r2WickCoeff μ a k j i := s94_coeff_symm ha hk hksym hk2
  have hT : ∀ n, s94T (fun i j => r2WickCoeff μ a k i j) n ≤ ∫ q, (k q.1 q.2) ^ 2 ∂(μ.prod μ) := by
    intro n
    have := s94_bessel ha hon hk hk2 (Finset.range n ×ˢ Finset.range n)
    unfold s94T
    rw [Finset.sum_product] at this
    exact this
  obtain ⟨Q, hQ, hlim, hbd⟩ := s94_sec_limit hz hΛ0 hsym hT
  exact ⟨Q, ⟨hQ, hlim⟩, hbd⟩

theorem s94_wick_bound (hz : S94GSeq P' z Λ) (hΛ0 : 0 ≤ Λ) {a : ℕ → Euc d → ℝ} (ha : ∀ i, IsR2Test (a i))
    (hon : ∀ i j, ∫ x, Whole.projMean μ (a i) x * Whole.projMean μ (a j) x ∂μ = if i = j then 1 else 0)
    {k : Euc d → Euc d → ℝ} (hk : Measurable fun q : Euc d × Euc d => k q.1 q.2)
    (hksym : ∀ x y, k x y = k y x) (hk2 : MemLp (fun q : Euc d × Euc d => k q.1 q.2) 2 (μ.prod μ))
    {Q : Ω' → ℝ} (hQ : s94WickL2 P' μ a z k Q) :
    ∫ ζ, Q ζ ^ 2 ∂P' ≤ 2 * Λ ^ 2 * ∫ q, (k q.1 q.2) ^ 2 ∂(μ.prod μ) := by
  have hsym : ∀ i j, r2WickCoeff μ a k i j = r2WickCoeff μ a k j i := s94_coeff_symm ha hk hksym hk2
  have hT : ∀ n, s94T (fun i j => r2WickCoeff μ a k i j) n ≤ ∫ q, (k q.1 q.2) ^ 2 ∂(μ.prod μ) := by
    intro n
    have := s94_bessel ha hon hk hk2 (Finset.range n ×ˢ Finset.range n)
    unfold s94T
    rw [Finset.sum_product] at this
    exact this
  have hM0 : 0 ≤ ∫ q, (k q.1 q.2) ^ 2 ∂(μ.prod μ) := integral_nonneg fun q => sq_nonneg _
  refine s94_L2_bound_of_tendsto (fun n => s94_sec_memLp hz _ n) hQ.1 hQ.2 (by positivity) fun n => ?_
  have h1 := s94_sec_diff_le hz hΛ0 hsym (Nat.zero_le n)
  have e0 : s94Sec P' z (fun i j => r2WickCoeff μ a k i j) 0 = fun _ => 0 := by
    funext ζ; simp [s94Sec]
  have eT : s94T (fun i j => r2WickCoeff μ a k i j) 0 = 0 := by simp [s94T]
  rw [e0, eT] at h1
  simp only [sub_zero] at h1
  refine h1.trans ?_
  have := hT n
  have h2 : 0 ≤ 2 * Λ ^ 2 := by positivity
  nlinarith

theorem s94Sec_sub (A A' : ℕ → ℕ → ℝ) (n : ℕ) (ζ : Ω') :
    s94Sec P' z (fun i j => A i j - A' i j) n ζ = s94Sec P' z A n ζ - s94Sec P' z A' n ζ := by
  unfold s94Sec
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- `L²`-Lipschitz dependence of the Wick chaos on the kernel. -/
theorem s94_wick_lipschitz (hz : S94GSeq P' z Λ) (hΛ0 : 0 ≤ Λ) {a : ℕ → Euc d → ℝ} (ha : ∀ i, IsR2Test (a i))
    (hon : ∀ i j, ∫ x, Whole.projMean μ (a i) x * Whole.projMean μ (a j) x ∂μ = if i = j then 1 else 0)
    {k k' : Euc d → Euc d → ℝ} (hk : Measurable fun q : Euc d × Euc d => k q.1 q.2)
    (hksym : ∀ x y, k x y = k y x) (hk2 : MemLp (fun q : Euc d × Euc d => k q.1 q.2) 2 (μ.prod μ))
    (hk' : Measurable fun q : Euc d × Euc d => k' q.1 q.2)
    (hksym' : ∀ x y, k' x y = k' y x) (hk2' : MemLp (fun q : Euc d × Euc d => k' q.1 q.2) 2 (μ.prod μ))
    {Q Q' : Ω' → ℝ} (hQ : s94WickL2 P' μ a z k Q) (hQ' : s94WickL2 P' μ a z k' Q') :
    ∫ ζ, (Q ζ - Q' ζ) ^ 2 ∂P' ≤ 2 * Λ ^ 2 * ∫ q, (k q.1 q.2 - k' q.1 q.2) ^ 2 ∂(μ.prod μ) := by
  set κ : Euc d → Euc d → ℝ := fun x y => k x y - k' x y with hκ
  have hκm : Measurable fun q : Euc d × Euc d => κ q.1 q.2 := hk.sub hk'
  have hκ2 : MemLp (fun q : Euc d × Euc d => κ q.1 q.2) 2 (μ.prod μ) := hk2.sub hk2'
  have hκs : ∀ x y, κ x y = κ y x := fun x y => by simp only [hκ, hksym x y, hksym' x y]
  have hcoef : (fun i j => r2WickCoeff μ a κ i j) =
      fun i j => r2WickCoeff μ a k i j - r2WickCoeff μ a k' i j := by
    funext i j
    exact s94_coeff_sub ha hk hk2 hk' hk2' i j
  have hQκ : s94WickL2 P' μ a z κ (fun ζ => Q ζ - Q' ζ) := by
    refine ⟨hQ.1.sub hQ'.1, ?_⟩
    have hu : ∀ n, Integrable (fun ζ => (s94Sec P' z (fun i j => r2WickCoeff μ a k i j) n ζ - Q ζ) ^ 2) P' :=
      fun n => ((s94_sec_memLp hz _ n).sub hQ.1).integrable_sq
    have hv : ∀ n, Integrable (fun ζ => (s94Sec P' z (fun i j => r2WickCoeff μ a k' i j) n ζ - Q' ζ) ^ 2) P' :=
      fun n => ((s94_sec_memLp hz _ n).sub hQ'.1).integrable_sq
    have hsq : Tendsto (fun n => 2 * ∫ ζ, (s94Sec P' z (fun i j => r2WickCoeff μ a k i j) n ζ - Q ζ) ^ 2 ∂P' +
        2 * ∫ ζ, (s94Sec P' z (fun i j => r2WickCoeff μ a k' i j) n ζ - Q' ζ) ^ 2 ∂P') atTop (𝓝 (2 * 0 + 2 * 0)) :=
      (hQ.2.const_mul 2).add (hQ'.2.const_mul 2)
    rw [mul_zero, add_zero] at hsq
    refine squeeze_zero (fun n => integral_nonneg fun ζ => sq_nonneg _) (fun n => ?_) hsq
    rw [hcoef]
    simp_rw [s94Sec_sub]
    have hdi : Integrable (fun ζ => (s94Sec P' z (fun i j => r2WickCoeff μ a k i j) n ζ - Q ζ -
        (s94Sec P' z (fun i j => r2WickCoeff μ a k' i j) n ζ - Q' ζ)) ^ 2) P' :=
      (((s94_sec_memLp hz _ n).sub hQ.1).sub ((s94_sec_memLp hz _ n).sub hQ'.1)).integrable_sq
    calc ∫ ζ, (s94Sec P' z (fun i j => r2WickCoeff μ a k i j) n ζ - s94Sec P' z (fun i j => r2WickCoeff μ a k' i j) n ζ -
          (Q ζ - Q' ζ)) ^ 2 ∂P'
        ≤ ∫ ζ, (2 * (s94Sec P' z (fun i j => r2WickCoeff μ a k i j) n ζ - Q ζ) ^ 2 +
          2 * (s94Sec P' z (fun i j => r2WickCoeff μ a k' i j) n ζ - Q' ζ) ^ 2) ∂P' := by
          refine integral_mono (by simpa [sub_sub_sub_comm] using hdi) (((hu n).const_mul 2).add ((hv n).const_mul 2))
            fun ζ => ?_
          nlinarith [sq_nonneg (s94Sec P' z (fun i j => r2WickCoeff μ a k i j) n ζ - Q ζ +
            (s94Sec P' z (fun i j => r2WickCoeff μ a k' i j) n ζ - Q' ζ))]
      _ = _ := by
          rw [integral_add ((hu n).const_mul 2) ((hv n).const_mul 2), integral_const_mul, integral_const_mul]
  exact s94_wick_bound hz hΛ0 ha hon hκm hκs hκ2 hQκ

end Wick

end HRS.MS.R2Chaos
