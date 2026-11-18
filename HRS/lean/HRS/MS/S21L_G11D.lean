import HRS.MS.S21L_G11B
import HRS.MS.S21L_G11C

/-!
# S21L G11D -- basis independence of the scalar Wick chaos for the abstract field `η` (R26-T3.G11, fourth step)

If `Q` and `Q'` are the `L²`-limits of the Wick sections of one symmetric kernel `k ∈ L²(μ⊗μ)` computed in two orthonormal
bases `a`, `a'` of `L²_0(μ)` (coordinates `η(a_i)`, `η(a'_i)`), then `Q = Q'` a.e.  Route: the sections of `k` in `a` are the
Wick chaoses of the finite-rank kernels `G_n = ∑_{i,j<n} A_ij e_i⊗e_j` in the basis `a'` (G11C); `G_n → k_c` in `L²(μ⊗μ)`
(G11B) and the Wick chaos is `L²`-Lipschitz in the kernel (`s94_wick_lipschitz`).  Prefix `s21l_`.
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

variable {d : ℕ} {Ω : Type} [MeasurableSpace Ω] {μ : Measure (Euc d)} [IsProbabilityMeasure μ]
  {P : Measure Ω} [IsProbabilityMeasure P] {η : (Euc d → ℝ) → Ω → ℝ} {Λ : ℝ}

theorem s21l_wickL2_center {a : ℕ → Euc d → ℝ} (hat : ∀ i, IsR2Test (a i)) {z : ℕ → Ω → ℝ}
    {k : Euc d → Euc d → ℝ} (hk : Integrable (fun q : Euc d × Euc d => k q.1 q.2) (μ.prod μ)) {Q : Ω → ℝ}
    (hQ : s94WickL2 P μ a z k Q) : s94WickL2 P μ a z (r2CenterKernel μ k) Q := by
  have : (fun i j => r2WickCoeff μ a (r2CenterKernel μ k) i j) = fun i j => r2WickCoeff μ a k i j :=
    funext fun i => funext fun j => s21l_coeff_center hat hk i j
  unfold s94WickL2
  rw [this]
  exact hQ

theorem s21l_wick_unique (h : S21LEta μ P η Λ) (hΛ0 : 0 ≤ Λ) {a a' : ℕ → Euc d → ℝ}
    (hb : IsR2ZeroMeanONB μ a) (hb' : IsR2ZeroMeanONB μ a') {k : Euc d → Euc d → ℝ}
    (hkm : Measurable fun q : Euc d × Euc d => k q.1 q.2) (hsym : ∀ x y, k x y = k y x)
    (hk2 : MemLp (fun q : Euc d × Euc d => k q.1 q.2) 2 (μ.prod μ)) {Q Q' : Ω → ℝ}
    (hQ : s94WickL2 P μ a (fun i ζ => η (a i) ζ) k Q) (hQ' : s94WickL2 P μ a' (fun i ζ => η (a' i) ζ) k Q') :
    Q =ᵐ[P] Q' := by
  obtain ⟨hat, hon, hcomp⟩ := hb
  obtain ⟨hat', hon', hcomp'⟩ := hb'
  have hz' := s21l_gseq h hat' hon'
  have hk1 : Integrable (fun z : Euc d × Euc d => k z.1 z.2) (μ.prod μ) := hk2.integrable one_le_two
  have hcm : Measurable fun q : Euc d × Euc d => r2CenterKernel μ k q.1 q.2 := s94_center_measurable hkm
  have hcs : ∀ x y, r2CenterKernel μ k x y = r2CenterKernel μ k y x := s94_center_symm hsym
  have hc2 : MemLp (fun q : Euc d × Euc d => r2CenterKernel μ k q.1 q.2) 2 (μ.prod μ) := s21h2_c_memLp μ hk2
  have hQ'c := s21l_wickL2_center hat' hk1 hQ'
  have hAs : ∀ i j, r2WickCoeff μ a k i j = r2WickCoeff μ a k j i := s94_coeff_symm hat hkm hsym hk2
  -- finite sections as kernels in the basis `a'`
  set A : ℕ → ℕ → ℝ := fun i j => r2WickCoeff μ a k i j with hA
  have hFR : ∀ n : ℕ, s94WickL2 P μ a' (fun i ζ => η (a' i) ζ)
      (r2CenterKernel μ (r2FiniteRankKernel (fun α β : Fin n => A α β) (fun α : Fin n => a α)))
      (fun ζ => ∑ α : Fin n, ∑ β : Fin n, A α β * (η (a α) ζ * η (a β) ζ - ∫ ζ', η (a α) ζ' * η (a β) ζ' ∂P)) :=
    fun n => s21l_wick_finiteRank h hΛ0 hat' hon' hcomp' (fun α β : Fin n => A α β)
      (u := fun α : Fin n => a α) (fun α => hat α)
  have hsec : ∀ n ζ, s94Sec P (fun i ζ => η (a i) ζ) A n ζ =
      ∑ α : Fin n, ∑ β : Fin n, A α β * (η (a α) ζ * η (a β) ζ - ∫ ζ', η (a α) ζ' * η (a β) ζ' ∂P) := by
    intro n ζ
    unfold s94Sec
    rw [Finset.sum_range]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_range]
  have hGn : ∀ n : ℕ, ∀ q : Euc d × Euc d,
      r2CenterKernel μ (r2FiniteRankKernel (fun α β : Fin n => A α β) (fun α : Fin n => a α)) q.1 q.2 =
        ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, A i j * (Whole.projMean μ (a i) q.1 * Whole.projMean μ (a j) q.2) := by
    intro n q
    rw [s94_center_finiteRank (fun α => hat α) q.1 q.2, Finset.sum_range]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_range]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have hlip : ∀ n : ℕ, ∫ ζ, (Q' ζ - ∑ α : Fin n, ∑ β : Fin n,
      A α β * (η (a α) ζ * η (a β) ζ - ∫ ζ', η (a α) ζ' * η (a β) ζ' ∂P)) ^ 2 ∂P ≤
      2 * Λ ^ 2 * ∫ q, (r2CenterKernel μ k q.1 q.2 - ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
        A i j * (Whole.projMean μ (a i) q.1 * Whole.projMean μ (a j) q.2)) ^ 2 ∂(μ.prod μ) := by
    intro n
    have hu : ∀ α : Fin n, IsR2Test (a α) := fun α => hat α
    have hl := s94_wick_lipschitz hz' hΛ0 hat' hon' (k := r2CenterKernel μ k)
      (k' := r2CenterKernel μ (r2FiniteRankKernel (fun α β : Fin n => A α β) (fun α : Fin n => a α)))
      hcm hcs hc2 (s94_center_finiteRank_measurable hu)
      (fun x y => s94_center_finiteRank_symm hu (fun α β => hAs α β) x y)
      (s94_center_finiteRank_memLp hu) hQ'c (hFR n)
    simp_rw [hGn] at hl
    exact hl
  have hT := s21l_tc_conv ⟨hat, hon, hcomp⟩ hkm hsym hk2
  have hQL := hQ.1
  have hQL' := hQ'.1
  have hsq : ∀ n, ∫ ζ, (Q ζ - Q' ζ) ^ 2 ∂P ≤
      2 * ∫ ζ, (s94Sec P (fun i ζ => η (a i) ζ) A n ζ - Q ζ) ^ 2 ∂P +
        2 * ∫ ζ, (Q' ζ - s94Sec P (fun i ζ => η (a i) ζ) A n ζ) ^ 2 ∂P := fun n => by
    have m1 : MemLp (fun ζ => s94Sec P (fun i ζ => η (a i) ζ) A n ζ - Q ζ) 2 P :=
      (s94_sec_memLp (s21l_gseq h hat hon) A n).sub hQL
    have m2 : MemLp (fun ζ => Q' ζ - s94Sec P (fun i ζ => η (a i) ζ) A n ζ) 2 P :=
      hQL'.sub (s94_sec_memLp (s21l_gseq h hat hon) A n)
    have m3 : MemLp (fun ζ => Q ζ - Q' ζ) 2 P := hQL.sub hQL'
    have e : ∀ ζ, (Q ζ - Q' ζ) ^ 2 ≤ 2 * (s94Sec P (fun i ζ => η (a i) ζ) A n ζ - Q ζ) ^ 2 +
        2 * (Q' ζ - s94Sec P (fun i ζ => η (a i) ζ) A n ζ) ^ 2 := fun ζ => by
      nlinarith [sq_nonneg ((s94Sec P (fun i ζ => η (a i) ζ) A n ζ - Q ζ) - (Q' ζ - s94Sec P (fun i ζ => η (a i) ζ) A n ζ))]
    calc ∫ ζ, (Q ζ - Q' ζ) ^ 2 ∂P ≤ ∫ ζ, (2 * (s94Sec P (fun i ζ => η (a i) ζ) A n ζ - Q ζ) ^ 2 +
        2 * (Q' ζ - s94Sec P (fun i ζ => η (a i) ζ) A n ζ) ^ 2) ∂P :=
          integral_mono m3.integrable_sq (m1.integrable_sq.const_mul 2 |>.add (m2.integrable_sq.const_mul 2)) e
      _ = _ := by
        rw [integral_add (m1.integrable_sq.const_mul 2) (m2.integrable_sq.const_mul 2), integral_const_mul,
          integral_const_mul]
  have hlim : Tendsto (fun n => 2 * ∫ ζ, (s94Sec P (fun i ζ => η (a i) ζ) A n ζ - Q ζ) ^ 2 ∂P +
      2 * ∫ ζ, (Q' ζ - s94Sec P (fun i ζ => η (a i) ζ) A n ζ) ^ 2 ∂P) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n => ∫ ζ, (s94Sec P (fun i ζ => η (a i) ζ) A n ζ - Q ζ) ^ 2 ∂P) atTop (𝓝 0) := hQ.2
    have h2 : Tendsto (fun n => ∫ ζ, (Q' ζ - s94Sec P (fun i ζ => η (a i) ζ) A n ζ) ^ 2 ∂P) atTop (𝓝 0) := by
      have h3 : Tendsto (fun n => 2 * Λ ^ 2 * ∫ q, (r2CenterKernel μ k q.1 q.2 - ∑ i ∈ Finset.range n,
          ∑ j ∈ Finset.range n, A i j * (Whole.projMean μ (a i) q.1 * Whole.projMean μ (a j) q.2)) ^ 2 ∂(μ.prod μ)) atTop
          (𝓝 0) := by
        simpa using hT.const_mul (2 * Λ ^ 2)
      refine squeeze_zero (fun n => integral_nonneg fun ζ => sq_nonneg _) (fun n => ?_) h3
      simp only [hsec]
      exact hlip n
    simpa using (h1.const_mul 2).add (h2.const_mul 2)
  have hz : ∫ ζ, (Q ζ - Q' ζ) ^ 2 ∂P = 0 :=
    le_antisymm (ge_of_tendsto' hlim fun n => (hsq n)) (integral_nonneg fun ζ => sq_nonneg _)
  have hi : Integrable (fun ζ => (Q ζ - Q' ζ) ^ 2) P := (hQL.sub hQL').integrable_sq
  have := (integral_eq_zero_iff_of_nonneg (fun ζ => sq_nonneg _) hi).1 hz
  filter_upwards [this] with ζ hζ
  have : (Q ζ - Q' ζ) ^ 2 = 0 := hζ
  have := pow_eq_zero_iff (two_ne_zero) |>.1 this
  linarith

end HRS.MS.R26T3
