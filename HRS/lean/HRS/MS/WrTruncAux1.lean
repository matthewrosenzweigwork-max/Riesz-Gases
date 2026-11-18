import HRS.MS.WrPresAux2

/-!
# HRS.MS.WrTruncAux1 -- two-sided Euclidean weak pressure bound (WR-6)

Packet WR-6 of `docs/SUPP_FOUND_PACKETS.md` (Track D).  Whole-space port of
`HRS.weak_reference_pressure` (`HRS/Energy/WeakReference.lean:6251`):

* `weak_reference_pressure_E`: there are `a₀ > 0` and `C ≥ 0` (depending only on `(d, s, βm, βp, M, A)`,
  quantified before `ρ, q, a, N, β`) such that for every probability density `ρ ≤ M`, every symmetric
  nonnegative measurable kernel with the envelope `q x y ≤ A (1 + rieszWeight s (x - y))` (`x ≠ y`) and row
  bound `a < a₀`, all `N ≥ 2` and `β ∈ [βm, βp]`:
  `exp (-(C N δ_N)) ≤ pairPartitionE q N β (ρ dx) ≤ exp (C N δ_N)`.
* `weak_reference_pressure_pairNormalizer_E`: the same for the frozen Bochner normaliser
  `HRS.Whole.pairNormalizer`, with `GibbsWellDefined` and the real-logarithm form
  `|Real.log (pairNormalizer)| ≤ C N δ_N` (not a junk value: the normaliser is `≥ 1`).

Adjustment relative to the sketch: no truncation `q ∧ R`, `R → ∞` is needed.  The upper bound
`weak_pressure_upper_E` of WR-5 is already proved directly for the unbounded kernel with only the envelope
`A (1 + W_s)` and the row bound (the truncation is not used in the torus proof either), so the two-sided bound
is the upper bound combined with `EWeakKernel.one_le_partition_E` (lower bound `1 ≤ K`), exactly as in the
torus `weak_reference_pressure`.  The constant is replaced by `max C 0`.  Helper lemmas carry the prefix `wr6_`.
-/

set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory Function Set
open scoped ENNReal

noncomputable section

namespace HRS.MS.Wr

/-- `exp (-(C N δ_N)) ≤ 1` and `1 ≤ exp (C N δ_N)` when `C ≥ 0` and `δ_N ≥ 0` (helper). -/
theorem wr6_exp_neg_le_one {d : ℕ} {s : ℝ} {N : ℕ} {C : ℝ} (hC : 0 ≤ C) (hδ : 0 ≤ deltaN d s N) :
    Real.exp (-(C * N * deltaN d s N)) ≤ 1 := by
  refine Real.exp_le_one_iff.2 ?_
  have : 0 ≤ C * N * deltaN d s N := mul_nonneg (mul_nonneg hC (Nat.cast_nonneg N)) hδ
  linarith

/-- **Euclidean weak reference pressure** (two-sided; whole-space port of `HRS.weak_reference_pressure`). -/
theorem weak_reference_pressure_E {d : ℕ} (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d)
    (βm βp : ℝ) (hβm : 0 < βm) (M A : ℝ) :
    ∃ a₀ C : ℝ, 0 < a₀ ∧ 0 ≤ C ∧
      ∀ ρ : Euc d → ℝ, HRS.Whole.IsProbDensity ρ → (∀ x, ρ x ≤ M) →
      ∀ q : Euc d → Euc d → ℝ, Measurable (Function.uncurry q) → (∀ x y, q x y = q y x) →
        (∀ x y, 0 ≤ q x y) →
        (∀ x y, x ≠ y → q x y ≤ A * (1 + HRS.Whole.rieszWeight s (x - y))) →
      ∀ a : ℝ, 0 ≤ a → a < a₀ →
        (∀ x, ∫⁻ y, ENNReal.ofReal (q x y) ∂(HRS.Whole.withDensityReal ρ) ≤ ENNReal.ofReal a) →
      ∀ N : ℕ, 2 ≤ N → ∀ β ∈ Set.Icc βm βp,
        ENNReal.ofReal (Real.exp (-(C * N * deltaN d s N))) ≤
            pairPartitionE q N β (HRS.Whole.withDensityReal ρ) ∧
          pairPartitionE q N β (HRS.Whole.withDensityReal ρ) ≤
            ENNReal.ofReal (Real.exp (C * N * deltaN d s N)) := by
  obtain ⟨a₀, C₀, ha₀, hup⟩ := weak_pressure_upper_E hd s hs0 hsd βm βp hβm M A
  refine ⟨a₀, max C₀ 0, ha₀, le_max_right _ _, ?_⟩
  intro ρ hρ hM q hqm hqs hq0 hqA a ha0 ha hrow N hN β hβ
  haveI : IsProbabilityMeasure (HRS.Whole.withDensityReal ρ) :=
    HRS.Whole.Q34.isProbabilityMeasure_nu hρ
  have hK : EWeakKernel (HRS.Whole.withDensityReal ρ) a q := ⟨hqm, hqs, hq0, hrow⟩
  have hβ0 : 0 ≤ β := (hβm.trans_le hβ.1).le
  have hN0 : 0 < N := by omega
  have hδ : 0 ≤ deltaN d s N := HRS.deltaN_nonneg s (by omega)
  refine ⟨?_, ?_⟩
  · exact le_trans (ENNReal.ofReal_le_one.2 (wr6_exp_neg_le_one (le_max_right _ _) hδ))
      (hK.one_le_partition_E ha0 hβ0 hN0)
  · refine (hup ρ hρ hM q hqm hqs hq0 hqA a ha0 ha hrow N hN β hβ).trans ?_
    refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
    have : C₀ * ((N : ℝ) * deltaN d s N) ≤ max C₀ 0 * ((N : ℝ) * deltaN d s N) :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) (mul_nonneg (Nat.cast_nonneg N) hδ)
    linarith [show max C₀ 0 * N * deltaN d s N = max C₀ 0 * ((N : ℝ) * deltaN d s N) by ring,
      show C₀ * N * deltaN d s N = C₀ * ((N : ℝ) * deltaN d s N) by ring]

/-- Two-sided pressure bound for the frozen Bochner normaliser: `GibbsWellDefined`,
`e^{-C N δ_N} ≤ 1 ≤ K ≤ e^{C N δ_N}` and `|log K| ≤ C N δ_N`. -/
theorem weak_reference_pressure_pairNormalizer_E {d : ℕ} (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s)
    (hsd : s < d) (βm βp : ℝ) (hβm : 0 < βm) (M A : ℝ) :
    ∃ a₀ C : ℝ, 0 < a₀ ∧ 0 ≤ C ∧
      ∀ ρ : Euc d → ℝ, HRS.Whole.IsProbDensity ρ → (∀ x, ρ x ≤ M) →
      ∀ q : Euc d → Euc d → ℝ, Measurable (Function.uncurry q) → (∀ x y, q x y = q y x) →
        (∀ x y, 0 ≤ q x y) →
        (∀ x y, x ≠ y → q x y ≤ A * (1 + HRS.Whole.rieszWeight s (x - y))) →
      ∀ a : ℝ, 0 ≤ a → a < a₀ →
        (∀ x, ∫⁻ y, ENNReal.ofReal (q x y) ∂(HRS.Whole.withDensityReal ρ) ≤ ENNReal.ofReal a) →
      ∀ N : ℕ, 2 ≤ N → ∀ β ∈ Set.Icc βm βp,
        HRS.Whole.GibbsWellDefined q N β (HRS.Whole.withDensityReal ρ) ∧
        Real.exp (-(C * N * deltaN d s N)) ≤
          HRS.Whole.pairNormalizer q N β (HRS.Whole.withDensityReal ρ) ∧
        HRS.Whole.pairNormalizer q N β (HRS.Whole.withDensityReal ρ)
          ≤ Real.exp (C * N * deltaN d s N) ∧
        |Real.log (HRS.Whole.pairNormalizer q N β (HRS.Whole.withDensityReal ρ))|
          ≤ C * N * deltaN d s N := by
  obtain ⟨a₀, C, ha₀, hC, H⟩ := weak_reference_pressure_E hd s hs0 hsd βm βp hβm M A
  obtain ⟨a₁, C₁, ha₁, H1⟩ := weak_pressure_upper_pairNormalizer_E hd s hs0 hsd βm βp hβm M A
  refine ⟨min a₀ a₁, max C C₁, lt_min ha₀ ha₁, hC.trans (le_max_left _ _), ?_⟩
  intro ρ hρ hM q hqm hqs hq0 hqA a ha0 ha hrow N hN β hβ
  have haa₀ : a < a₀ := lt_of_lt_of_le ha (min_le_left _ _)
  have haa₁ : a < a₁ := lt_of_lt_of_le ha (min_le_right _ _)
  obtain ⟨hW, h1, hZ, -, hlog⟩ := H1 ρ hρ hM q hqm hqs hq0 hqA a ha0 haa₁ hrow N hN β hβ
  have hδ : 0 ≤ deltaN d s N := HRS.deltaN_nonneg s (by omega)
  have hnd : 0 ≤ (N : ℝ) * deltaN d s N := mul_nonneg (Nat.cast_nonneg N) hδ
  have hmono : C₁ * N * deltaN d s N ≤ max C C₁ * N * deltaN d s N := by
    have hm : C₁ ≤ max C C₁ := le_max_right _ _
    nlinarith
  have hpos : 0 < HRS.Whole.pairNormalizer q N β (HRS.Whole.withDensityReal ρ) := by linarith
  refine ⟨hW, ?_, ?_, ?_⟩
  · refine le_trans ?_ h1
    exact wr6_exp_neg_le_one (hC.trans (le_max_left _ _)) hδ
  · exact hZ.trans (Real.exp_le_exp.2 hmono)
  · rw [abs_of_nonneg (Real.log_nonneg h1)]
    exact hlog.trans hmono

end HRS.MS.Wr
