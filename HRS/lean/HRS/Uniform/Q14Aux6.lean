import HRS.Uniform.Q14Aux5

/-!
# Q14, part 6: the transport bound `𝔟(C_μ, C_ν)² ≤ C q ∫ |x-y|² dπ` for a coupling `π`
-/

noncomputable section

open HRS
open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.Uniform.Q14

section Transport

variable {d : ℕ}

lemma q14_tdist_eq (x y : Torus d) : Torus.tdist x y = KernelGrad.tdist x y := rfl

lemma q14_tdist_sqrt (x y : Torus d) :
    Torus.tdist x y = Real.sqrt (∑ i, ‖(x - y) i‖ ^ 2) := by
  rw [q14_tdist_eq]; exact CoercAux.tdist_eq_sqrt x y

lemma q14_continuous_tdist : Continuous fun p : Torus d × Torus d => Torus.tdist p.1 p.2 := by
  simp_rw [q14_tdist_sqrt]
  fun_prop

lemma q14_tdist_le (x y : Torus d) : Torus.tdist x y ≤ d := by
  rw [q14_tdist_sqrt]
  refine Real.sqrt_le_iff.2 ⟨Nat.cast_nonneg d, ?_⟩
  calc ∑ i, ‖(x - y) i‖ ^ 2 ≤ ∑ _i : Fin d, (1 : ℝ) := by
        refine Finset.sum_le_sum fun i _ => ?_
        have h : ‖(x - y) i‖ ≤ 1 / 2 := by
          have := (AddCircle.norm_le_half_period (1 : ℝ) one_ne_zero : ‖(x - y) i‖ ≤ _)
          simpa using this
        nlinarith [norm_nonneg ((x - y) i)]
    _ = d := by simp
    _ ≤ (d : ℝ) ^ 2 := by
        rcases Nat.eq_zero_or_pos d with h0 | h0
        · simp [h0]
        · have : (1 : ℝ) ≤ d := by exact_mod_cast h0
          nlinarith

lemma q14_tdist_self (x : Torus d) : Torus.tdist x x = 0 := by
  rw [q14_tdist_eq]; exact CoercAux.tdist_self x

lemma q14_norm_bVec_sub_le {γ : ℝ} (hγ : (d : ℝ) / 2 + 2 < γ) (j : Fin d) (x y : Torus d) :
    ‖bVec γ j x - bVec γ j y‖ ≤ Real.sqrt (2 * q14S d (γ - 2)) * Torus.tdist x y := by
  have h := q14_norm_bVec_sub_sq_le hγ j x y
  have ht : 0 ≤ Torus.tdist x y := by unfold Torus.tdist; exact norm_nonneg _
  calc ‖bVec γ j x - bVec γ j y‖ = Real.sqrt (‖bVec γ j x - bVec γ j y‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt (2 * q14S d (γ - 2) * Torus.tdist x y ^ 2) := Real.sqrt_le_sqrt h
    _ = _ := by
        rw [Real.sqrt_mul (by have := q14S_nonneg d (γ - 2); positivity), Real.sqrt_sq ht]

lemma q14_continuous_bVec {γ : ℝ} (hγ : (d : ℝ) / 2 + 2 < γ) (j : Fin d) :
    Continuous (bVec γ j) := by
  refine continuous_iff_continuousAt.2 fun x₀ => ?_
  rw [ContinuousAt, tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero (fun y => dist_nonneg) (fun y => ?_)
    (g := fun y => Real.sqrt (2 * q14S d (γ - 2)) * Torus.tdist y x₀) ?_
  · rw [dist_eq_norm]; exact q14_norm_bVec_sub_le hγ j y x₀
  · have hc : Continuous fun y : Torus d => Torus.tdist y x₀ := by
      simp_rw [q14_tdist_eq]
      exact CoercAux.continuous_tdist_left x₀
    have := (hc.const_mul (Real.sqrt (2 * q14S d (γ - 2)))).tendsto x₀
    rw [q14_tdist_self, mul_zero] at this
    exact this

end Transport

section Cov

variable {d : ℕ}

lemma q14_covForm_apply {γ : ℝ} (hγ : (d : ℝ) / 2 + 2 < γ) {q : ℝ} (hq : 0 ≤ q)
    (μ : Measure (Torus d)) [IsFiniteMeasure μ] (x y : NegSobolev d γ) :
    covForm γ q μ x y = ∑ j : Fin d, ∫ a,
      inner ℝ (Real.sqrt (2 * q) • bVec γ j a) x * inner ℝ (Real.sqrt (2 * q) • bVec γ j a) y ∂μ := by
  unfold covForm
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [ChartAux.outerCov_apply (q14_continuous_bVec hγ j) (M := 2 * q14S d (γ - 1))
    (fun a => q14_norm_bVec_sq_le hγ j a) μ x y, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
  simp only [inner_smul_left, conj_trivial]
  have : Real.sqrt (2 * q) * Real.sqrt (2 * q) = 2 * q := Real.mul_self_sqrt (by positivity)
  calc 2 * q * (inner ℝ (bVec γ j a) x * inner ℝ (bVec γ j a) y)
      = (Real.sqrt (2 * q) * Real.sqrt (2 * q)) * (inner ℝ (bVec γ j a) x * inner ℝ (bVec γ j a) y) := by
        rw [this]
    _ = _ := by ring

end Cov

section Coupling

variable {d : ℕ}

lemma q14_integrable_tdist_sq (π : Measure (Torus d × Torus d)) [IsFiniteMeasure π] :
    Integrable (fun z : Torus d × Torus d => Torus.tdist z.1 z.2 ^ 2) π := by
  refine Integrable.of_bound (C := (d : ℝ) ^ 2)
    (q14_continuous_tdist.pow 2).aestronglyMeasurable (Filter.Eventually.of_forall fun z => ?_)
  have h0 : 0 ≤ Torus.tdist z.1 z.2 := by unfold Torus.tdist; exact norm_nonneg _
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact pow_le_pow_left₀ h0 (q14_tdist_le _ _) 2

theorem q14_bures2_coupling {γ : ℝ} (hγ : (d : ℝ) / 2 + 2 < γ) {q : ℝ} (hq : 0 ≤ q)
    (π : Measure (Torus d × Torus d)) [IsFiniteMeasure π] :
    Uniform.bures2 (covForm γ q (π.map Prod.fst)) (covForm γ q (π.map Prod.snd)) ≤
      4 * q * d * q14S d (γ - 2) * ∫ z, Torus.tdist z.1 z.2 ^ 2 ∂π := by
  set S₁ := q14S d (γ - 1) with hS₁
  set S₂ := q14S d (γ - 2) with hS₂
  have hS₁0 : 0 ≤ S₁ := q14S_nonneg d _
  have hS₂0 : 0 ≤ S₂ := q14S_nonneg d _
  set c := Real.sqrt (2 * q) with hc
  have hc0 : 0 ≤ c := Real.sqrt_nonneg _
  have hcc : c * c = 2 * q := Real.mul_self_sqrt (by positivity)
  have hbm : ∀ j, Measurable (bVec γ j) := fun j => (q14_continuous_bVec hγ j).measurable
  have hu : ∀ j, Measurable fun z : Torus d × Torus d => c • bVec γ j z.1 := fun j =>
    (hbm j |>.comp measurable_fst).const_smul c
  have hv : ∀ j, Measurable fun z : Torus d × Torus d => c • bVec γ j z.2 := fun j =>
    (hbm j |>.comp measurable_snd).const_smul c
  have hnorm : ∀ (j : Fin d) (a : Torus d), ‖c • bVec γ j a‖ ≤ c * Real.sqrt (2 * S₁) := by
    intro j a
    rw [norm_smul, Real.norm_of_nonneg hc0]
    refine mul_le_mul_of_nonneg_left ?_ hc0
    calc ‖bVec γ j a‖ = Real.sqrt (‖bVec γ j a‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ Real.sqrt (2 * S₁) := Real.sqrt_le_sqrt (q14_norm_bVec_sq_le hγ j a)
  have hmain := q14_bures2_le_family (ξ := π) (u := fun j z => c • bVec γ j z.1)
    (v := fun j z => c • bVec γ j z.2) hu hv (M := c * Real.sqrt (2 * S₁))
    (by positivity) (fun j z => hnorm j _) (fun j z => hnorm j _)
    (C := covForm γ q (π.map Prod.fst)) (D := covForm γ q (π.map Prod.snd))
    (fun x y => by
      rw [q14_covForm_apply hγ hq]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [integral_map measurable_fst.aemeasurable]
      exact (((q14_continuous_bVec hγ j).const_smul c).inner continuous_const |>.mul
        (((q14_continuous_bVec hγ j).const_smul c).inner continuous_const)).aestronglyMeasurable)
    (fun x y => by
      rw [q14_covForm_apply hγ hq]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [integral_map measurable_snd.aemeasurable]
      exact (((q14_continuous_bVec hγ j).const_smul c).inner continuous_const |>.mul
        (((q14_continuous_bVec hγ j).const_smul c).inner continuous_const)).aestronglyMeasurable)
  refine hmain.trans ?_
  have hpt : ∀ j (z : Torus d × Torus d), ‖c • bVec γ j z.1 - c • bVec γ j z.2‖ ^ 2 ≤
      (4 * q * S₂) * Torus.tdist z.1 z.2 ^ 2 := by
    intro j z
    rw [← smul_sub, norm_smul, Real.norm_of_nonneg hc0, mul_pow]
    have h1 := q14_norm_bVec_sub_sq_le hγ j z.1 z.2
    have : c ^ 2 = 2 * q := by rw [sq]; exact hcc
    rw [this]
    nlinarith [h1, hq]
  have hint : ∀ j, Integrable (fun z : Torus d × Torus d => ‖c • bVec γ j z.1 - c • bVec γ j z.2‖ ^ 2) π := by
    intro j
    refine Integrable.of_bound (C := (2 * (c * Real.sqrt (2 * S₁))) ^ 2)
      ((((hu j).sub (hv j)).norm).pow_const 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    refine pow_le_pow_left₀ (norm_nonneg _) ((norm_sub_le _ _).trans ?_) 2
    have := hnorm j z.1; have := hnorm j z.2; linarith
  calc ∑ j, ∫ z, ‖c • bVec γ j z.1 - c • bVec γ j z.2‖ ^ 2 ∂π
      ≤ ∑ _j : Fin d, ∫ z, (4 * q * S₂) * Torus.tdist z.1 z.2 ^ 2 ∂π := by
        refine Finset.sum_le_sum fun j _ => ?_
        exact integral_mono (hint j) ((q14_integrable_tdist_sq π).const_mul _) (hpt j)
    _ = 4 * q * d * S₂ * ∫ z, Torus.tdist z.1 z.2 ^ 2 ∂π := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, integral_const_mul]
        ring

end Coupling

section CovTrace

variable {d : ℕ}

lemma q14_covForm_trace {γ : ℝ} (hγ : (d : ℝ) / 2 + 2 < γ) {q : ℝ} (hq : 0 ≤ q)
    (μ : Measure (Torus d)) [IsFiniteMeasure μ] :
    IsTraceClassCov (covForm γ q μ) ∧
      traceNormForm (covForm γ q μ) ≤ 4 * q * d * q14S d (γ - 1) * (μ Set.univ).toReal := by
  set c := Real.sqrt (2 * q) with hc
  have hc0 : 0 ≤ c := Real.sqrt_nonneg _
  have hcc : c * c = 2 * q := Real.mul_self_sqrt (by positivity)
  have hbm : ∀ j, Measurable (bVec γ j) := fun j => (q14_continuous_bVec hγ j).measurable
  have hnorm : ∀ (j : Fin d) (a : Torus d), ‖c • bVec γ j a‖ ≤ c * Real.sqrt (2 * q14S d (γ - 1)) := by
    intro j a
    rw [norm_smul, Real.norm_of_nonneg hc0]
    refine mul_le_mul_of_nonneg_left ?_ hc0
    calc ‖bVec γ j a‖ = Real.sqrt (‖bVec γ j a‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ Real.sqrt (2 * q14S d (γ - 1)) := Real.sqrt_le_sqrt (q14_norm_bVec_sq_le hγ j a)
  obtain ⟨ι, hι, e, -⟩ := HilbertCLTAux.exists_hilbertBasis_type (H := NegSobolev d γ)
  haveI := hι
  obtain ⟨h1, h2⟩ := q14_form_of_family (ξ := μ) (u := fun j a => c • bVec γ j a)
    (fun j => (hbm j).const_smul c) hnorm (C := covForm γ q μ)
    (fun x y => q14_covForm_apply hγ hq μ x y) e
  refine ⟨h1, h2.trans_le ?_⟩
  have hpt : ∀ (j : Fin d) (a : Torus d), ‖c • bVec γ j a‖ ^ 2 ≤ 2 * q * (2 * q14S d (γ - 1)) := by
    intro j a
    rw [norm_smul, Real.norm_of_nonneg hc0, mul_pow]
    have : c ^ 2 = 2 * q := by rw [sq]; exact hcc
    rw [this]
    exact mul_le_mul_of_nonneg_left (q14_norm_bVec_sq_le hγ j a) (by positivity)
  calc ∑ j : Fin d, ∫ a, ‖c • bVec γ j a‖ ^ 2 ∂μ
      ≤ ∑ _j : Fin d, ∫ _a, 2 * q * (2 * q14S d (γ - 1)) ∂μ := by
        refine Finset.sum_le_sum fun j _ => ?_
        refine integral_mono ?_ (integrable_const _) (hpt j)
        refine Integrable.of_bound (C := (c * Real.sqrt (2 * q14S d (γ - 1))) ^ 2)
          ((((hbm j).const_smul c).norm.pow_const 2)).aestronglyMeasurable
          (Filter.Eventually.of_forall fun a => ?_)
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact pow_le_pow_left₀ (norm_nonneg _) (hnorm j a) 2
    _ = 4 * q * d * q14S d (γ - 1) * (μ Set.univ).toReal := by
        simp only [integral_const, smul_eq_mul, Measure.real, Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, nsmul_eq_mul]
        ring

end CovTrace

end HRS.Uniform.Q14
