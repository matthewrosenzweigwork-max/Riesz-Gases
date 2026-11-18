import HRS.MS.WrMargAux1

/-!
# HRS.MS.WrMargAux2 -- forms of the Euclidean marginal bound for later consumers (WR-4, part 2)

Consequences of `weak_marginal_strong_E` (`WrMargAux1`) with the same data `(d, s, βm, βp, M, A)`:

* `weak_marginal_pairGibbs_E`: the frozen `HRS.Whole.pairGibbs q N (τ β) μ` of `HRS/Whole/Static.lean`
  is well defined (`GibbsWellDefined`, normaliser `≥ 1`) and its first marginal is `μ.withDensity f` with the
  same bound (via `pairGibbs_eq_pairGibbsLawE`, `EWeakKernel.gibbsWellDefined_E`).
* `weak_marginal_aux_E`: the `ℝ≥0∞` form `∫⁻ ‖f - 1‖ₑ² dμ ≤ ofReal ((C δ_N)²)` (port of `weak_marginal_aux`).
* `wr4_zero_kernel_hyps`: non-vacuity of the kernel hypotheses (the zero kernel satisfies them).
Helper lemmas carry the prefix `wr4_`.
-/

set_option linter.unusedSectionVars false

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace HRS.MS.Wr

variable {d : ℕ}

/-- The Euclidean marginal bound for the frozen Gibbs law `HRS.Whole.pairGibbs` (and well-definedness). -/
theorem weak_marginal_pairGibbs_E (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d)
    (βm βp : ℝ) (hβm : 0 < βm) (M A : ℝ) :
    ∃ a₀ C : ℝ, 0 < a₀ ∧
      ∀ ρ : Euc d → ℝ, HRS.Whole.IsProbDensity ρ → (∀ x, ρ x ≤ M) →
      ∀ q : Euc d → Euc d → ℝ, Measurable (Function.uncurry q) → (∀ x y, q x y = q y x) →
        (∀ x y, 0 ≤ q x y) →
        (∀ x y, x ≠ y → q x y ≤ A * (1 + HRS.Whole.rieszWeight s (x - y))) →
      ∀ a : ℝ, 0 ≤ a → a < a₀ →
        (∀ x, ∫⁻ y, ENNReal.ofReal (q x y) ∂(HRS.Whole.withDensityReal ρ) ≤ ENNReal.ofReal a) →
      ∀ N : ℕ, ∀ hN : 2 ≤ N, ∀ β ∈ Set.Icc βm βp, ∀ τ ∈ Set.Icc (0 : ℝ) 1,
        HRS.Whole.GibbsWellDefined q N (τ * β) (HRS.Whole.withDensityReal ρ) ∧
        1 ≤ HRS.Whole.pairNormalizer q N (τ * β) (HRS.Whole.withDensityReal ρ) ∧
        ∃ f : Euc d → ℝ≥0∞,
          (HRS.Whole.pairGibbs q N (τ * β) (HRS.Whole.withDensityReal ρ)).map
              (fun X => X ⟨0, by omega⟩)
            = (HRS.Whole.withDensityReal ρ).withDensity f ∧ Measurable f ∧
          (∃ K : ℝ, ∀ x, (f x).toReal ≤ K) ∧
          Integrable (fun x => ((f x).toReal - 1) ^ 2) (HRS.Whole.withDensityReal ρ) ∧
          ∫ x, ((f x).toReal - 1) ^ 2 ∂(HRS.Whole.withDensityReal ρ)
            ≤ (C * deltaN d s N) ^ 2 := by
  obtain ⟨a₀, C, ha₀, H⟩ := weak_marginal_strong_E hd s hs0 hsd βm βp hβm M A
  refine ⟨a₀, C, ha₀, ?_⟩
  intro ρ hρ hM q hqm hqs hq0 hqA a ha0 ha hrow N hN β hβ τ hτ
  haveI : IsProbabilityMeasure (HRS.Whole.withDensityReal ρ) :=
    HRS.Whole.Q34.isProbabilityMeasure_nu hρ
  have hK : EWeakKernel (HRS.Whole.withDensityReal ρ) a q := ⟨hqm, hqs, hq0, hrow⟩
  have hβ0 : 0 < β := lt_of_lt_of_le hβm hβ.1
  have hκ₀ : 0 ≤ τ * β := mul_nonneg hτ.1 hβ0.le
  obtain ⟨hW, h1⟩ := hK.gibbsWellDefined_E ha0 hκ₀ (show 0 < N by omega)
  refine ⟨hW, h1, ?_⟩
  obtain ⟨f, hf1, hf2, hf3, hf4, hf5⟩ := H ρ hρ hM q hqm hqs hq0 hqA a ha0 ha hrow N hN β hβ τ hτ
  refine ⟨f, ?_, hf2, hf3, hf4, hf5⟩
  rw [pairGibbs_eq_pairGibbsLawE hW]
  exact hf1

set_option maxHeartbeats 400000 in
/-- The `ℝ≥0∞` form of the marginal bound (port of `weak_marginal_aux`). -/
theorem weak_marginal_aux_E (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d)
    (βm βp : ℝ) (hβm : 0 < βm) (M A : ℝ) :
    ∃ a₀ C : ℝ, 0 < a₀ ∧
      ∀ ρ : Euc d → ℝ, HRS.Whole.IsProbDensity ρ → (∀ x, ρ x ≤ M) →
      ∀ q : Euc d → Euc d → ℝ, Measurable (Function.uncurry q) → (∀ x y, q x y = q y x) →
        (∀ x y, 0 ≤ q x y) →
        (∀ x y, x ≠ y → q x y ≤ A * (1 + HRS.Whole.rieszWeight s (x - y))) →
      ∀ a : ℝ, 0 ≤ a → a < a₀ →
        (∀ x, ∫⁻ y, ENNReal.ofReal (q x y) ∂(HRS.Whole.withDensityReal ρ) ≤ ENNReal.ofReal a) →
      ∀ N : ℕ, ∀ hN : 2 ≤ N, ∀ β ∈ Set.Icc βm βp, ∀ τ ∈ Set.Icc (0 : ℝ) 1,
        ∃ f : Euc d → ℝ≥0∞,
          (pairGibbsLawE q N (τ * β) (HRS.Whole.withDensityReal ρ)).map
              (fun X => X ⟨0, by omega⟩)
            = (HRS.Whole.withDensityReal ρ).withDensity f ∧
          ∫⁻ x, ‖(f x).toReal - 1‖ₑ ^ 2 ∂(HRS.Whole.withDensityReal ρ)
            ≤ ENNReal.ofReal ((C * deltaN d s N) ^ 2) := by
  obtain ⟨a₀, C, ha₀, H⟩ := weak_marginal_strong_E hd s hs0 hsd βm βp hβm M A
  refine ⟨a₀, C, ha₀, ?_⟩
  intro ρ hρ hM q hqm hqs hq0 hqA a ha0 ha hrow N hN β hβ τ hτ
  obtain ⟨f, hf1, -, -, hint, hbound⟩ :=
    H ρ hρ hM q hqm hqs hq0 hqA a ha0 ha hrow N hN β hβ τ hτ
  refine ⟨f, hf1, ?_⟩
  have e : ∀ x, ‖(f x).toReal - 1‖ₑ ^ 2 = ENNReal.ofReal (((f x).toReal - 1) ^ 2) := by
    intro x
    rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
  simp_rw [e]
  rw [← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun x => sq_nonneg _)]
  exact ENNReal.ofReal_le_ofReal hbound

/-- Non-vacuity of the hypotheses: for `ρ` a probability density with `ρ ≤ M` the zero kernel satisfies all
kernel hypotheses of `weak_marginal_strong_E` with every `a ≥ 0` (so the quantifiers are not empty). -/
theorem wr4_zero_kernel_hyps (s : ℝ) (A : ℝ) (hA : 0 ≤ A) (ρ : Euc d → ℝ) {a : ℝ} (ha : 0 ≤ a) :
    Measurable (Function.uncurry fun _ _ : Euc d => (0 : ℝ)) ∧
      (∀ x y : Euc d, (0 : ℝ) = 0) ∧
      (∀ x y : Euc d, x ≠ y → (0 : ℝ) ≤ A * (1 + HRS.Whole.rieszWeight s (x - y))) ∧
      (∀ x : Euc d, ∫⁻ y, ENNReal.ofReal ((0 : ℝ)) ∂(HRS.Whole.withDensityReal ρ)
        ≤ ENNReal.ofReal a) := by
  refine ⟨measurable_const, fun _ _ => rfl, fun x y _ => ?_, fun x => by simp⟩
  have := wr3_rieszWeight_nonneg (d := d) s (x - y)
  positivity

end HRS.MS.Wr
