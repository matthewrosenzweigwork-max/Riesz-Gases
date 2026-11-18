import HRS.MS.R2ChaosAux13
import HRS.MS.S21G2_K11bB
import HRS.MS.S21H2_S14aD1

/-!
# S21L G11B -- tensor Parseval for the Wick coefficients (R26-T3.G11, second step)

For an orthonormal basis `e_i = P_μ a_i` of `L²_0(μ)` (`IsR2ZeroMeanONB`) and a symmetric measurable `k ∈ L²(μ⊗μ)` with
coefficients `A_ij = r2WickCoeff μ a k i j`: the coefficients of the centred kernel are the same
(`s21l_coeff_center`), `∑_{i,j<n} A_ij² → ‖k_c‖²` (`s21l_tc_total`: Parseval on a.e. slices, then on the
function `g_j = ∫ k_c(·,y)e_j(y)dμ`), and `‖k_c - ∑_{i,j<n} A_ij e_i⊗e_j‖² = ‖k_c‖² - ∑_{i,j<n} A_ij²`
(`s21l_pythag`), so the finite sections of the kernel converge to `k_c` in `L²(μ⊗μ)` (`s21l_tc_conv`).  Prefix `s21l_`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.R26T3

open HRS.MS.R2Chaos HRS.Whole

variable {d : ℕ} {μ : Measure (HRS.Euc d)} [IsProbabilityMeasure μ] {a : ℕ → HRS.Euc d → ℝ}

theorem s21l_coeff_center (hat : ∀ i, IsR2Test (a i)) {k : HRS.Euc d → HRS.Euc d → ℝ}
    (hk : Integrable (fun z : HRS.Euc d × HRS.Euc d => k z.1 z.2) (μ.prod μ)) (i j : ℕ) :
    r2WickCoeff μ a (r2CenterKernel μ k) i j = r2WickCoeff μ a k i j := by
  obtain ⟨C1, h1⟩ := s94_projMean_bounded μ (hat i)
  obtain ⟨C2, h2⟩ := s94_projMean_bounded μ (hat j)
  exact s21g2_k11b_center hk (s94_projMean_continuous μ (hat i)) (s94_projMean_continuous μ (hat j))
    h1 h2 (s94_integral_projMean (hat i)) (s94_integral_projMean (hat j))

/-- Pythagoras for the finite sections of the tensor expansion of `k` (any measurable `k ∈ L²`). -/
theorem s21l_pythag (hat : ∀ i, IsR2Test (a i))
    (hon : ∀ i j, ∫ x, Whole.projMean μ (a i) x * Whole.projMean μ (a j) x ∂μ = if i = j then 1 else 0)
    {k : HRS.Euc d → HRS.Euc d → ℝ} (hk : Measurable fun q : HRS.Euc d × HRS.Euc d => k q.1 q.2)
    (hk2 : MemLp (fun q : HRS.Euc d × HRS.Euc d => k q.1 q.2) 2 (μ.prod μ)) (n : ℕ) :
    ∫ q, (k q.1 q.2 - ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
        r2WickCoeff μ a k i j * (Whole.projMean μ (a i) q.1 * Whole.projMean μ (a j) q.2)) ^ 2 ∂(μ.prod μ) =
      ∫ q, (k q.1 q.2) ^ 2 ∂(μ.prod μ) - ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, (r2WickCoeff μ a k i j) ^ 2 := by
  set F : Finset (ℕ × ℕ) := Finset.range n ×ˢ Finset.range n with hF
  set A : ℕ × ℕ → ℝ := fun p => r2WickCoeff μ a k p.1 p.2 with hA
  set g : HRS.Euc d × HRS.Euc d → ℝ := fun q => ∑ p ∈ F, A p * s94E2 μ a p q with hg
  have hgeq : ∀ q : HRS.Euc d × HRS.Euc d, g q = ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
      r2WickCoeff μ a k i j * (Whole.projMean μ (a i) q.1 * Whole.projMean μ (a j) q.2) := fun q => by
    simp only [hg, hF, Finset.sum_product, hA, s94E2]
  have hAprod : ∀ p, A p = ∫ q, k q.1 q.2 * s94E2 μ a p q ∂(μ.prod μ) := fun p =>
    s94_coeff_eq_prod hat hk hk2 p.1 p.2
  have hE2m := s94E2_measurable (μ := μ) hat
  have hkE : ∀ p, Integrable (fun q => k q.1 q.2 * s94E2 μ a p q) (μ.prod μ) := fun p =>
    (s94_integrable_k_mul μ hk2 (hE2m p) (s94E2_bounded (μ := μ) hat p).choose_spec)
  have hgm : Measurable g := Finset.measurable_sum _ fun p _ => (hE2m p).const_mul _
  have hgb : ∃ C, ∀ q, |g q| ≤ C := by
    refine ⟨∑ p ∈ F, |A p| * (s94E2_bounded (μ := μ) hat p).choose, fun q => ?_⟩
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun p _ => ?_)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left ((s94E2_bounded (μ := μ) hat p).choose_spec q) (abs_nonneg _)
  obtain ⟨Cg, hCg⟩ := hgb
  have hkg : Integrable (fun q => k q.1 q.2 * g q) (μ.prod μ) := s94_integrable_k_mul μ hk2 hgm hCg
  have hk2i : Integrable (fun q : HRS.Euc d × HRS.Euc d => (k q.1 q.2) ^ 2) (μ.prod μ) := hk2.integrable_sq
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
    obtain ⟨C1, h1⟩ := s94E2_bounded (μ := μ) hat p
    obtain ⟨C2, h2⟩ := s94E2_bounded (μ := μ) hat p'
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
    simp_rw [integral_const_mul, s94_E2_inner hat hon]
    rw [Finset.sum_eq_single p (fun p' _ hp' => by simp [Ne.symm hp']) (fun h => absurd hp h)]
    simp [sq]
  have e : ∀ q : HRS.Euc d × HRS.Euc d, (k q.1 q.2 - g q) ^ 2 = (k q.1 q.2) ^ 2 - 2 * (k q.1 q.2 * g q) + g q ^ 2 :=
    fun q => by ring
  have i2 : Integrable (fun q : HRS.Euc d × HRS.Euc d => 2 * (k q.1 q.2 * g q)) (μ.prod μ) := hkg.const_mul 2
  have i12 : Integrable (fun q : HRS.Euc d × HRS.Euc d => (k q.1 q.2) ^ 2 - 2 * (k q.1 q.2 * g q)) (μ.prod μ) :=
    hk2i.sub i2
  have hsum : ∑ p ∈ F, A p ^ 2 = ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, (r2WickCoeff μ a k i j) ^ 2 := by
    simp only [hF, Finset.sum_product, hA]
  simp_rw [← hgeq, e]
  rw [integral_add i12 hg2, integral_sub hk2i i2, integral_const_mul, h1, h2, ← hsum]
  ring

/-- Parseval for the mean-zero marginal functions `g_j(x) = ∫ c(x,y) e_j(y) dμ(y)` and a.e. slices. -/
theorem s21l_tc_total (hb : IsR2ZeroMeanONB μ a) {k : HRS.Euc d → HRS.Euc d → ℝ}
    (hkm : Measurable fun q : HRS.Euc d × HRS.Euc d => k q.1 q.2) (hsym : ∀ x y, k x y = k y x)
    (hk2 : MemLp (fun q : HRS.Euc d × HRS.Euc d => k q.1 q.2) 2 (μ.prod μ)) :
    Tendsto (fun n => ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, (r2WickCoeff μ a k i j) ^ 2) atTop
      (𝓝 (∫ q, (r2CenterKernel μ k q.1 q.2) ^ 2 ∂(μ.prod μ))) := by
  obtain ⟨hat, hon, hcomp⟩ := hb
  set c : HRS.Euc d → HRS.Euc d → ℝ := r2CenterKernel μ k with hc
  have hcm : Measurable fun q : HRS.Euc d × HRS.Euc d => c q.1 q.2 := s94_center_measurable hkm
  have hcs : ∀ x y, c x y = c y x := s94_center_symm hsym
  have hc2 : MemLp (fun q : HRS.Euc d × HRS.Euc d => c q.1 q.2) 2 (μ.prod μ) := s21h2_c_memLp μ hk2
  have hk1 : Integrable (fun z : HRS.Euc d × HRS.Euc d => k z.1 z.2) (μ.prod μ) := hk2.integrable one_le_two
  have hcoef : ∀ i j, r2WickCoeff μ a c i j = r2WickCoeff μ a k i j := fun i j => s21l_coeff_center hat hk1 i j
  set e : ℕ → HRS.Euc d → ℝ := fun j => Whole.projMean μ (a j) with he
  have hec : ∀ j, Continuous (e j) := fun j => s94_projMean_continuous μ (hat j)
  set g : ℕ → HRS.Euc d → ℝ := fun j x => ∫ y, c x y * e j y ∂μ with hg
  set bd : HRS.Euc d → ℝ := fun x => ∫ y, c x y ^ 2 ∂μ with hbd
  have hbdi : Integrable bd μ := hc2.integrable_sq.integral_prod_left
  set S : ℝ := ∫ q, (c q.1 q.2) ^ 2 ∂(μ.prod μ) with hS
  have hSbd : ∫ x, bd x ∂μ = S := (integral_prod _ hc2.integrable_sq).symm
  have hslice := s21h2_c_slice μ hk2
  -- Parseval on a.e. slices
  have hpars : ∀ᵐ x ∂μ, Tendsto (fun n => ∑ j ∈ Finset.range n, (g j x) ^ 2) atTop (𝓝 (bd x)) := by
    filter_upwards [hslice] with x hx
    exact s94_parseval hat hon hcomp (f := fun y => c x y) hx.1 hx.2
  have hbessel : ∀ᵐ x ∂μ, ∀ n, ∑ j ∈ Finset.range n, (g j x) ^ 2 ≤ bd x := by
    filter_upwards [hpars] with x hx n
    refine Monotone.ge_of_tendsto (f := fun n => ∑ j ∈ Finset.range n, (g j x) ^ 2) ?_ hx n
    refine monotone_nat_of_le_succ fun m => ?_
    rw [Finset.sum_range_succ]
    nlinarith [sq_nonneg (g m x)]
  have hgm : ∀ j, AEStronglyMeasurable (g j) μ := fun j => by
    have : AEStronglyMeasurable (fun z : HRS.Euc d × HRS.Euc d => c z.1 z.2 * e j z.2) (μ.prod μ) :=
      hcm.aestronglyMeasurable.mul ((hec j).measurable.comp measurable_snd).aestronglyMeasurable
    exact this.integral_prod_right'
  have hg2i : ∀ j, Integrable (fun x => (g j x) ^ 2) μ := fun j => by
    refine Integrable.mono' hbdi ((hgm j).pow 2) ?_
    filter_upwards [hbessel] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have := hx (j + 1)
    rw [Finset.sum_range_succ] at this
    have h0 : 0 ≤ ∑ i ∈ Finset.range j, (g i x) ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
    linarith
  have hgL2 : ∀ j, MemLp (g j) 2 μ := fun j => (memLp_two_iff_integrable_sq (hgm j)).2 (hg2i j)
  -- the series of integrals converges to S
  have hU : Tendsto (fun n => ∑ j ∈ Finset.range n, ∫ x, (g j x) ^ 2 ∂μ) atTop (𝓝 S) := by
    have hdc : Tendsto (fun n => ∫ x, ∑ j ∈ Finset.range n, (g j x) ^ 2 ∂μ) atTop (𝓝 (∫ x, bd x ∂μ)) := by
      refine tendsto_integral_of_dominated_convergence bd (fun n => ?_) hbdi (fun n => ?_) hpars
      · exact Finset.aestronglyMeasurable_fun_sum _ fun j _ => (hgm j).pow 2
      · filter_upwards [hbessel] with x hx
        rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun i _ => sq_nonneg _)]
        exact hx n
    rw [hSbd] at hdc
    refine hdc.congr fun n => ?_
    exact integral_finset_sum _ fun j _ => hg2i j
  have hUle : ∀ n, ∑ j ∈ Finset.range n, ∫ x, (g j x) ^ 2 ∂μ ≤ S := fun n => by
    rw [← integral_finset_sum _ fun j _ => hg2i j, ← hSbd]
    refine integral_mono_ae (integrable_finset_sum _ fun j _ => hg2i j) hbdi ?_
    filter_upwards [hbessel] with x hx using hx n
  -- mean zero of g_j
  have hg0 : ∀ j, ∫ x, g j x ∂μ = 0 := fun j => by
    obtain ⟨Cj, hCj⟩ := s94_projMean_bounded μ (hat j)
    have hint : Integrable (fun z : HRS.Euc d × HRS.Euc d => c z.1 z.2 * e j z.2) (μ.prod μ) :=
      s94_integrable_k_mul μ hc2 ((hec j).measurable.comp measurable_snd) (C := Cj) (fun z => hCj z.2)
    have hint' : Integrable (Function.uncurry fun x y => c x y * e j y) (μ.prod μ) := hint
    show ∫ x, ∫ y, c x y * e j y ∂μ ∂μ = 0
    rw [integral_integral_swap hint']
    have : ∀ᵐ y ∂μ, ∫ x, c x y * e j y ∂μ = 0 := by
      filter_upwards [hslice] with y hy
      rw [integral_mul_const]
      rw [show (∫ x, c x y ∂μ) = ∫ x, c y x ∂μ from integral_congr_ae (ae_of_all _ fun x => hcs x y), hy.2, zero_mul]
    rw [integral_congr_ae this]
    simp
  -- Parseval for g_j: ∫ g_j² = lim_n ∑_{i<n} A_ij²
  have hAj : ∀ j i, ∫ x, g j x * e i x ∂μ = r2WickCoeff μ a c i j := fun j i => by
    unfold r2WickCoeff
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp only [hg, he]
    rw [← integral_mul_const]
    refine integral_congr_ae (ae_of_all _ fun y => ?_)
    ring
  have hparsj : ∀ j, Tendsto (fun n => ∑ i ∈ Finset.range n, (r2WickCoeff μ a k i j) ^ 2) atTop
      (𝓝 (∫ x, (g j x) ^ 2 ∂μ)) := fun j => by
    have := s94_parseval hat hon hcomp (hgL2 j) (hg0 j)
    refine this.congr fun n => ?_
    refine Finset.sum_congr rfl fun i _ => ?_
    have := hAj j i
    simp only [he] at this
    rw [show (∫ x, g j x * Whole.projMean μ (a i) x ∂μ) = r2WickCoeff μ a k i j by rw [← hcoef i j]; exact this]
  -- partial sums T_n of the double series
  set T : ℕ → ℝ := fun n => ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, (r2WickCoeff μ a k i j) ^ 2 with hT
  have hTbd : ∀ n, T n ≤ S := fun n => by
    have := s94_bessel hat hon hcm hc2 (Finset.range n ×ˢ Finset.range n)
    rw [Finset.sum_product] at this
    have h2 : ∀ i j, r2WickCoeff μ a k i j ^ 2 = r2WickCoeff μ a c i j ^ 2 := fun i j => by rw [hcoef]
    simp only [hT, h2]
    exact this
  have hTmono : Monotone T := by
    refine monotone_nat_of_le_succ fun m => ?_
    simp only [hT]
    have h1 : ∑ i ∈ Finset.range m, ∑ j ∈ Finset.range m, (r2WickCoeff μ a k i j) ^ 2 ≤
        ∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (m + 1), (r2WickCoeff μ a k i j) ^ 2 := by
      refine (Finset.sum_le_sum fun i _ => Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.range_subset_range.2 (Nat.le_succ m)) fun j _ _ => sq_nonneg _).trans ?_
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 (Nat.le_succ m))
        fun i _ _ => Finset.sum_nonneg fun j _ => sq_nonneg _
    exact h1
  have hTc : Tendsto T atTop (𝓝 (⨆ n, T n)) := tendsto_atTop_ciSup hTmono ⟨S, by rintro _ ⟨n, rfl⟩; exact hTbd n⟩
  have hL1 : (⨆ n, T n) ≤ S := ciSup_le hTbd
  have hL2 : S ≤ ⨆ n, T n := by
    refine le_of_tendsto' hU fun J => ?_
    have hlim : Tendsto (fun n => ∑ j ∈ Finset.range J, ∑ i ∈ Finset.range n, (r2WickCoeff μ a k i j) ^ 2) atTop
        (𝓝 (∑ j ∈ Finset.range J, ∫ x, (g j x) ^ 2 ∂μ)) :=
      tendsto_finset_sum _ fun j _ => hparsj j
    refine le_of_tendsto' hlim fun n => ?_
    -- for `n ≥ J` the sum is bounded by `T n ≤ sup`; for `n < J` use monotonicity at `max`
    have hbd' : ∑ j ∈ Finset.range J, ∑ i ∈ Finset.range n, (r2WickCoeff μ a k i j) ^ 2 ≤ T (max n J) := by
      have hsc : ∑ j ∈ Finset.range J, ∑ i ∈ Finset.range n, (r2WickCoeff μ a k i j) ^ 2 =
          ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range J, (r2WickCoeff μ a k i j) ^ 2 := Finset.sum_comm
      rw [hsc]
      simp only [hT]
      refine (Finset.sum_le_sum fun i hi => Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.range_subset_range.2 (le_max_right n J)) fun j _ _ => sq_nonneg _).trans ?_
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 (le_max_left n J))
        fun i _ _ => Finset.sum_nonneg fun j _ => sq_nonneg _
    exact hbd'.trans (le_ciSup ⟨S, by rintro _ ⟨m, rfl⟩; exact hTbd m⟩ _)
  have : (⨆ n, T n) = S := le_antisymm hL1 hL2
  rw [this] at hTc
  exact hTc

theorem s21l_tc_conv (hb : IsR2ZeroMeanONB μ a) {k : HRS.Euc d → HRS.Euc d → ℝ}
    (hkm : Measurable fun q : HRS.Euc d × HRS.Euc d => k q.1 q.2) (hsym : ∀ x y, k x y = k y x)
    (hk2 : MemLp (fun q : HRS.Euc d × HRS.Euc d => k q.1 q.2) 2 (μ.prod μ)) :
    Tendsto (fun n => ∫ q, (r2CenterKernel μ k q.1 q.2 - ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
        r2WickCoeff μ a k i j * (Whole.projMean μ (a i) q.1 * Whole.projMean μ (a j) q.2)) ^ 2 ∂(μ.prod μ)) atTop (𝓝 0) := by
  have hat := hb.1
  have hon := hb.2.1
  have hcm : Measurable fun q : HRS.Euc d × HRS.Euc d => r2CenterKernel μ k q.1 q.2 := s94_center_measurable hkm
  have hc2 := s21h2_c_memLp μ hk2
  have hk1 : Integrable (fun z : HRS.Euc d × HRS.Euc d => k z.1 z.2) (μ.prod μ) := hk2.integrable one_le_two
  have hcoef : ∀ i j, r2WickCoeff μ a (r2CenterKernel μ k) i j = r2WickCoeff μ a k i j :=
    fun i j => s21l_coeff_center hat hk1 i j
  have hp := fun n => s21l_pythag hat hon hcm hc2 n
  simp only [hcoef] at hp
  have ht := s21l_tc_total hb hkm hsym hk2
  have := (tendsto_const_nhds (x := ∫ q, (r2CenterKernel μ k q.1 q.2) ^ 2 ∂(μ.prod μ))).sub ht
  rw [sub_self] at this
  exact this.congr fun n => (hp n).symm

end HRS.MS.R26T3
