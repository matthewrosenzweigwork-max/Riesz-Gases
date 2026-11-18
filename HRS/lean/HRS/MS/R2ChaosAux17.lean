import HRS.MS.R2ChaosAux16

/-!
# HRS.MS.R2ChaosAux17 -- the centered quadratic process of a time-constant finite-rank kernel

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

section Quad

variable {μ : Measure (Euc d)} [IsProbabilityMeasure μ] {N : ℕ}

theorem s94_abs_pair_empirical_le (hN : 0 < N) (x : EucConfig d N) {f : Euc d → ℝ} {C : ℝ}
    (hf : ∀ y, |f y| ≤ C) : |Whole.pair (Whole.empirical x) f| ≤ C := by
  haveI := Whole.empirical_isProbabilityMeasure hN x
  unfold Whole.pair
  rw [← Real.norm_eq_abs]
  refine (norm_integral_le_of_norm_le_const (C := C) (ae_of_all _ fun y => ?_)).trans (by simp)
  simpa using hf y

theorem s94_abs_pair_le (ν : Measure (Euc d)) [IsProbabilityMeasure ν] {f : Euc d → ℝ} {C : ℝ}
    (hf : ∀ y, |f y| ≤ C) : |Whole.pair ν f| ≤ C := by
  unfold Whole.pair
  rw [← Real.norm_eq_abs]
  refine (norm_integral_le_of_norm_le_const (C := C) (ae_of_all _ fun y => ?_)).trans (by simp)
  simpa using hf y

theorem s94_abs_empFluct_le (hN : 0 < N) {Ω : Type*} (X : ℝ≥0 → Ω → EucConfig d N) {a : Euc d → ℝ} {C : ℝ}
    (ha : ∀ y, |a y| ≤ C) (ζ : Ω) (t : ℝ) : |r2EmpFluct μ a X ζ t| ≤ Real.sqrt N * (2 * C) := by
  unfold r2EmpFluct
  rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
  refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
  have h1 := s94_abs_pair_empirical_le hN (X t.toNNReal ζ) ha
  have h2 := s94_abs_pair_le μ ha
  calc _ ≤ |Whole.pair (Whole.empirical (X t.toNNReal ζ)) a| + |Whole.pair μ a| := abs_sub _ _
    _ ≤ 2 * C := by linarith

theorem s94_gfun_continuous {m : ℕ} {c : Fin m → Fin m → ℝ} {u : Fin m → Euc d → ℝ} (hu : ∀ a, IsR2Test (u a)) :
    Continuous fun x : Euc d => ∑ a, ∑ b, c a b * u a x * u b x :=
  continuous_finset_sum _ fun a _ => continuous_finset_sum _ fun b _ =>
    ((continuous_const.mul (s94_test_continuous (hu a))).mul (s94_test_continuous (hu b)))

theorem s94_gfun_bounded {m : ℕ} {c : Fin m → Fin m → ℝ} {u : Fin m → Euc d → ℝ} (hu : ∀ a, IsR2Test (u a)) :
    ∃ C : ℝ, ∀ x, |∑ a, ∑ b, c a b * u a x * u b x| ≤ C := by
  have hb : ∀ a, ∃ C : ℝ, ∀ x, |u a x| ≤ C := fun a => s94_test_bounded (hu a)
  choose C hC using hb
  refine ⟨∑ a, ∑ b, |c a b| * C a * C b, fun x => ?_⟩
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun a _ => ?_)
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun b _ => ?_)
  rw [abs_mul, abs_mul]
  have h1 := hC a x
  have h2 := hC b x
  have h3 : 0 ≤ |u a x| := abs_nonneg _
  have h5 : 0 ≤ C a := h3.trans h1
  calc |c a b| * |u a x| * |u b x| ≤ |c a b| * C a * C b := by gcongr
    _ = _ := by ring

/-- `r2QuadFluct` of a time-constant finite-rank kernel. -/
theorem s94_quad_finiteRank {m : ℕ} {c : Fin m → Fin m → ℝ} {u : Fin m → Euc d → ℝ} (hu : ∀ a, IsR2Test (u a))
    (hc : ∀ a b, c a b = c b a) (hN : 0 < N) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → EucConfig d N) (hX : Measurable fun q : ℝ≥0 × Ω => X q.1 q.2)
    (t : ℝ) (ζ : Ω) :
    r2QuadFluct μ (fun _ => r2FiniteRankKernel c u) P X t ζ =
      (1 / 2) * ∑ a, ∑ b, c a b * (r2EmpFluct μ (u a) X ζ t * r2EmpFluct μ (u b) X ζ t -
          ∫ ζ', r2EmpFluct μ (u a) X ζ' t * r2EmpFluct μ (u b) X ζ' t ∂P) -
        (1 / 2) * (Whole.pair (Whole.empirical (X t.toNNReal ζ)) (fun x => ∑ a, ∑ b, c a b * u a x * u b x) -
          ∫ ζ', Whole.pair (Whole.empirical (X t.toNNReal ζ')) (fun x => ∑ a, ∑ b, c a b * u a x * u b x) ∂P) := by
  obtain ⟨Gf, hGf⟩ : ∃ f : Ω → ℝ, ∀ ζ, f ζ =
      Whole.pair (Whole.empirical (X t.toNNReal ζ)) (fun x => ∑ a, ∑ b, c a b * u a x * u b x) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨xi, hxi⟩ : ∃ f : Fin m → Ω → ℝ, ∀ a ζ, f a ζ = r2EmpFluct μ (u a) X ζ t := ⟨_, fun _ _ => rfl⟩
  have hid : ∀ ζ, (N : ℝ) * pairEnergy (r2FiniteRankKernel c u) (X t.toNNReal ζ) μ =
      (1 / 2) * ∑ a, ∑ b, c a b * (xi a ζ * xi b ζ) - (1 / 2) * Gf ζ := fun ζ => by
    rw [hGf]
    simp only [hxi]
    exact s94_N_pairEnergy_finiteRank hu hc hN (X t.toNNReal ζ)
  have hmX : Measurable fun ζ => X t.toNNReal ζ := hX.comp (measurable_prodMk_left)
  have hxim : ∀ a, Measurable (xi a) := fun a => by
    have : xi a = fun ζ => r2EmpFluct μ (u a) X ζ t := funext (hxi a)
    rw [this]
    have h1 := s94_empFluct_measurable (μ := μ) (N := N) (hu a) X hX
    have h2 : Measurable fun ζ : Ω => (t, ζ) := measurable_prodMk_left
    exact Measurable.comp (g := fun q : ℝ × Ω => r2EmpFluct μ (u a) X q.2 q.1) (f := fun ζ : Ω => (t, ζ)) h1 h2
  obtain ⟨Cg, hCg⟩ := s94_gfun_bounded (c := c) hu
  have hGm : Measurable Gf := by
    have : Gf = fun ζ => (N : ℝ)⁻¹ * ∑ i, (∑ a, ∑ b, c a b * u a (X t.toNNReal ζ i) * u b (X t.toNNReal ζ i)) := by
      funext ζ; rw [hGf, Whole.pair_empirical hN]
    rw [this]
    refine measurable_const.mul (Finset.measurable_sum _ fun i _ => ?_)
    exact (s94_gfun_continuous (c := c) hu).measurable.comp ((measurable_pi_apply i).comp hmX)
  have hGi : Integrable Gf P := Integrable.of_bound hGm.aestronglyMeasurable Cg
    (ae_of_all _ fun ζ => by
      rw [hGf]; simpa using s94_abs_pair_empirical_le hN (X t.toNNReal ζ) hCg)
  have hbd : ∀ a, ∃ C : ℝ, ∀ x, |u a x| ≤ C := fun a => s94_test_bounded (hu a)
  choose Cu hCu using hbd
  have hXi : ∀ a b, Integrable (fun ζ => xi a ζ * xi b ζ) P := fun a b => by
    refine Integrable.of_bound ((hxim a).mul (hxim b)).aestronglyMeasurable
      ((Real.sqrt N * (2 * Cu a)) * (Real.sqrt N * (2 * Cu b))) (ae_of_all _ fun ζ => ?_)
    rw [Real.norm_eq_abs, abs_mul, hxi, hxi]
    exact mul_le_mul (s94_abs_empFluct_le (μ := μ) hN X (hCu a) ζ t) (s94_abs_empFluct_le (μ := μ) hN X (hCu b) ζ t)
      (abs_nonneg _) ((abs_nonneg _).trans (s94_abs_empFluct_le (μ := μ) hN X (hCu a) ζ t))
  have i1 : Integrable (fun ζ => (1 / 2 : ℝ) * ∑ a, ∑ b, c a b * (xi a ζ * xi b ζ)) P :=
    (integrable_finset_sum _ fun a _ => integrable_finset_sum _ fun b _ => (hXi a b).const_mul (c a b)).const_mul _
  have hInt : ∫ ζ, ((1 / 2 : ℝ) * ∑ a, ∑ b, c a b * (xi a ζ * xi b ζ) - (1 / 2) * Gf ζ) ∂P =
      (1 / 2) * ∑ a, ∑ b, c a b * ∫ ζ, xi a ζ * xi b ζ ∂P - (1 / 2) * ∫ ζ, Gf ζ ∂P := by
    rw [integral_sub i1 (hGi.const_mul _), integral_const_mul, integral_const_mul,
      integral_finset_sum _ fun a _ => integrable_finset_sum _ fun b _ => (hXi a b).const_mul (c a b)]
    congr 2
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [integral_finset_sum _ fun b _ => (hXi a b).const_mul (c a b)]
    exact Finset.sum_congr rfl fun b _ => integral_const_mul _ _
  have hNp : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have e : ∫ ζ', pairEnergy (r2FiniteRankKernel c u) (X t.toNNReal ζ') μ ∂P =
      (N : ℝ)⁻¹ * ∫ ζ', ((1 / 2 : ℝ) * ∑ a, ∑ b, c a b * (xi a ζ' * xi b ζ') - (1 / 2) * Gf ζ') ∂P := by
    have : ∀ ζ', pairEnergy (r2FiniteRankKernel c u) (X t.toNNReal ζ') μ =
        (N : ℝ)⁻¹ * ((1 / 2 : ℝ) * ∑ a, ∑ b, c a b * (xi a ζ' * xi b ζ') - (1 / 2) * Gf ζ') := fun ζ' => by
      rw [← hid ζ']; field_simp
    simp_rw [this]
    exact integral_const_mul _ _
  unfold r2QuadFluct
  simp only
  rw [e]
  have h2 : (N : ℝ) * pairEnergy (r2FiniteRankKernel c u) (X t.toNNReal ζ) μ =
      (1 / 2 : ℝ) * ∑ a, ∑ b, c a b * (xi a ζ * xi b ζ) - (1 / 2) * Gf ζ := hid ζ
  rw [mul_sub, h2, ← mul_assoc, mul_inv_cancel₀ hNp, one_mul, hInt]
  simp only [hxi, hGf, mul_sub, Finset.sum_sub_distrib]
  ring

end Quad

end HRS.MS.R2Chaos
