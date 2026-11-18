import HRS.MS.R2ChaosAux7

/-!
# HRS.MS.R2ChaosAux8 -- the Wick chaos of a finite-rank kernel

Packet S94, namespace `HRS.MS.R2Chaos`, helper prefix `s94_`.

For `h = ∑_{ab} c_ab u_a ⊗ u_b` with test functions `u_a`, the centered kernel is `∑ c_ab (P u_a) ⊗ (P u_b)`, its coefficients in
the basis `(P a_i)` are `∑ c_ab γ^a_i γ^b_j`, and its Wick chaos is `∑ c_ab (ξ(u_a) ξ(u_b) - E ξ(u_a) ξ(u_b))`, whatever
the orthonormal basis.
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

section Kernel

variable {μ : Measure (Euc d)} [IsProbabilityMeasure μ] {m : ℕ} {c : Fin m → Fin m → ℝ} {u : Fin m → Euc d → ℝ}

theorem s94_center_finiteRank (hu : ∀ a, IsR2Test (u a)) (x y : Euc d) :
    r2CenterKernel μ (r2FiniteRankKernel c u) x y =
      ∑ a, ∑ b, c a b * Whole.projMean μ (u a) x * Whole.projMean μ (u b) y := by
  unfold r2CenterKernel r2FiniteRankKernel
  have h1 : ∫ y', ∑ a, ∑ b, c a b * u a x * u b y' ∂μ = ∑ a, ∑ b, c a b * u a x * Whole.pair μ (u b) := by
    rw [integral_finset_sum _ fun a _ => integrable_finset_sum _ fun b _ =>
      (s94_test_integrable (hu b) μ).const_mul (c a b * u a x)]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [integral_finset_sum _ fun b _ => (s94_test_integrable (hu b) μ).const_mul (c a b * u a x)]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [integral_const_mul]; rfl
  have h2 : ∫ x', ∑ a, ∑ b, c a b * u a x' * u b y ∂μ = ∑ a, ∑ b, c a b * Whole.pair μ (u a) * u b y := by
    rw [integral_finset_sum _ fun a _ => integrable_finset_sum _ fun b _ =>
      ((s94_test_integrable (hu a) μ).const_mul (c a b)).mul_const (u b y)]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [integral_finset_sum _ fun b _ => ((s94_test_integrable (hu a) μ).const_mul (c a b)).mul_const (u b y)]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [integral_mul_const, integral_const_mul]; rfl
  have h3 : ∫ x', ∫ y', ∑ a, ∑ b, c a b * u a x' * u b y' ∂μ ∂μ =
      ∑ a, ∑ b, c a b * Whole.pair μ (u a) * Whole.pair μ (u b) := by
    have : ∀ x', ∫ y', ∑ a, ∑ b, c a b * u a x' * u b y' ∂μ = ∑ a, ∑ b, c a b * u a x' * Whole.pair μ (u b) := by
      intro x'
      rw [integral_finset_sum _ fun a _ => integrable_finset_sum _ fun b _ =>
        (s94_test_integrable (hu b) μ).const_mul (c a b * u a x')]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [integral_finset_sum _ fun b _ => (s94_test_integrable (hu b) μ).const_mul (c a b * u a x')]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [integral_const_mul]; rfl
    simp_rw [this]
    rw [integral_finset_sum _ fun a _ => integrable_finset_sum _ fun b _ =>
      ((s94_test_integrable (hu a) μ).const_mul (c a b)).mul_const (Whole.pair μ (u b))]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [integral_finset_sum _ fun b _ => ((s94_test_integrable (hu a) μ).const_mul (c a b)).mul_const (Whole.pair μ (u b))]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [integral_mul_const, integral_const_mul]; rfl
  rw [h1, h2, h3]
  unfold Whole.projMean
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  ring

theorem s94_center_finiteRank_measurable (hu : ∀ a, IsR2Test (u a)) :
    Measurable fun q : Euc d × Euc d => r2CenterKernel μ (r2FiniteRankKernel c u) q.1 q.2 := by
  have : (fun q : Euc d × Euc d => r2CenterKernel μ (r2FiniteRankKernel c u) q.1 q.2) =
      fun q => ∑ a, ∑ b, c a b * Whole.projMean μ (u a) q.1 * Whole.projMean μ (u b) q.2 := by
    funext q; exact s94_center_finiteRank hu q.1 q.2
  rw [this]
  refine Finset.measurable_sum _ fun a _ => Finset.measurable_sum _ fun b _ => ?_
  exact (((s94_projMean_continuous μ (hu a)).measurable.comp measurable_fst).const_mul (c a b)).mul
    ((s94_projMean_continuous μ (hu b)).measurable.comp measurable_snd)

theorem s94_center_finiteRank_symm (hu : ∀ a, IsR2Test (u a)) (hc : ∀ a b, c a b = c b a) (x y : Euc d) :
    r2CenterKernel μ (r2FiniteRankKernel c u) x y = r2CenterKernel μ (r2FiniteRankKernel c u) y x := by
  rw [s94_center_finiteRank hu, s94_center_finiteRank hu, Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [hc a b]; ring

theorem s94_center_finiteRank_bounded (hu : ∀ a, IsR2Test (u a)) :
    ∃ C : ℝ, ∀ x y, |r2CenterKernel μ (r2FiniteRankKernel c u) x y| ≤ C := by
  have hb : ∀ a, ∃ C : ℝ, ∀ x, |Whole.projMean μ (u a) x| ≤ C := fun a => s94_projMean_bounded μ (hu a)
  choose C hC using hb
  refine ⟨∑ a, ∑ b, |c a b| * C a * C b, fun x y => ?_⟩
  rw [s94_center_finiteRank hu]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun a _ => ?_)
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun b _ => ?_)
  rw [abs_mul, abs_mul]
  have h1 := hC a x
  have h2 := hC b y
  have h3 : 0 ≤ |Whole.projMean μ (u a) x| := abs_nonneg _
  have h4 : 0 ≤ |Whole.projMean μ (u b) y| := abs_nonneg _
  calc |c a b| * |Whole.projMean μ (u a) x| * |Whole.projMean μ (u b) y|
      ≤ |c a b| * C a * C b := by
        have h5 : 0 ≤ C a := h3.trans h1
        gcongr
    _ = _ := by ring

theorem s94_center_finiteRank_memLp (hu : ∀ a, IsR2Test (u a)) :
    MemLp (fun q : Euc d × Euc d => r2CenterKernel μ (r2FiniteRankKernel c u) q.1 q.2) 2 (μ.prod μ) := by
  obtain ⟨C, hC⟩ := s94_center_finiteRank_bounded (μ := μ) (c := c) hu
  exact MemLp.of_bound (s94_center_finiteRank_measurable hu).aestronglyMeasurable C
    (ae_of_all _ fun q => by simpa using hC q.1 q.2)

theorem s94_coeff_finiteRank {a : ℕ → Euc d → ℝ} (ha : ∀ i, IsR2Test (a i)) (hu : ∀ α, IsR2Test (u α)) (i j : ℕ) :
    r2WickCoeff μ a (r2CenterKernel μ (r2FiniteRankKernel c u)) i j =
      ∑ α, ∑ β, c α β * s94gam μ (u α) a i * s94gam μ (u β) a j := by
  unfold r2WickCoeff
  have hbd : ∀ f g : Euc d → ℝ, IsR2Test f → IsR2Test g → Integrable (fun x => Whole.projMean μ f x * Whole.projMean μ g x) μ :=
    fun f g hf hg => s94_integrable_projMean_mul μ hf hg
  have hinner : ∀ x, ∫ y, r2CenterKernel μ (r2FiniteRankKernel c u) x y * Whole.projMean μ (a i) x *
      Whole.projMean μ (a j) y ∂μ =
      ∑ α, ∑ β, c α β * (Whole.projMean μ (u α) x * Whole.projMean μ (a i) x) * s94gam μ (u β) a j := by
    intro x
    have e : ∀ y, r2CenterKernel μ (r2FiniteRankKernel c u) x y * Whole.projMean μ (a i) x * Whole.projMean μ (a j) y =
        ∑ α, ∑ β, (c α β * (Whole.projMean μ (u α) x * Whole.projMean μ (a i) x)) *
          (Whole.projMean μ (u β) y * Whole.projMean μ (a j) y) := fun y => by
      rw [s94_center_finiteRank hu, Finset.sum_mul, Finset.sum_mul]
      refine Finset.sum_congr rfl fun α _ => ?_
      rw [Finset.sum_mul, Finset.sum_mul]
      exact Finset.sum_congr rfl fun β _ => by ring
    simp_rw [e]
    rw [integral_finset_sum _ fun α _ => integrable_finset_sum _ fun β _ => (hbd _ _ (hu β) (ha j)).const_mul _]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [integral_finset_sum _ fun β _ => (hbd _ _ (hu β) (ha j)).const_mul _]
    refine Finset.sum_congr rfl fun β _ => ?_
    rw [integral_const_mul]
    simp only [s94gam]
  simp_rw [hinner]
  rw [integral_finset_sum _ fun α _ => integrable_finset_sum _ fun β _ =>
    ((hbd _ _ (hu α) (ha i)).const_mul (c α β)).mul_const _]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [integral_finset_sum _ fun β _ => ((hbd _ _ (hu α) (ha i)).const_mul (c α β)).mul_const _]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [integral_mul_const, integral_const_mul]
  simp only [s94gam]

end Kernel

end HRS.MS.R2Chaos
