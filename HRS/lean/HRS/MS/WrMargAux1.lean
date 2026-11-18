import HRS.MS.WrAlgAux1
import HRS.MS.WrRowAux3

/-!
# HRS.MS.WrMargAux1 -- Euclidean L² cavity marginal `weak_marginal_strong_E` (WR-4)

Whole-space port of `HRS.weak_marginal_strong` (`HRS/Energy/WeakReference.lean:5834`).  The torus data
`(c₀, Λ, cstar, periodicRiesz)` are replaced by the Euclidean data `ρ ≤ M` only (no lower bound, no
smoothness) and the envelope `q x y ≤ A (1 + rieszWeight s (x - y))` for `x ≠ y`:

* `μ = withDensityReal ρ`, `ρ` a probability density on `ℝ^d` with `ρ ≤ M`;
* `q` a measurable symmetric nonnegative kernel with `q x y ≤ A (1 + W_s(x - y))` off the diagonal and
  row bound `∫⁻ ofReal (q x ·) dμ ≤ ofReal a`, `0 ≤ a < a₀`;
* for `N ≥ 2`, `β ∈ [βm, βp]`, `τ ∈ [0, 1]`, the first marginal of the Gibbs law
  `pairGibbsLawE q N (τ β) μ` (defined in `WrKerAux1`, equal to `HRS.Whole.pairGibbs` under
  `GibbsWellDefined`, see `WrMargAux2`) has a measurable bounded density `f` w.r.t. `μ` with
  `∫ (f - 1)² dμ ≤ (C δ_N)²`, and the integrand is integrable (so the bound is not the Bochner junk value `0`).

Differences from the torus statement (all harmless): no instance argument `IsProbabilityMeasure`
(it follows from `IsProbDensity`), the integrability conjunct, and `(cstar, hw, periodicRiesz)` replaced
by the envelope with `rieszWeight`.  The constants `a₀, C` depend only on `(d, s, βm, βp, M, A)`.
The proof copies the torus proof; the torus `row_bounds` is replaced by `wr3_row_bounds_delta` and the
Dobrushin/weak-potential layer by `EWeakKernel`, `mkV_E`, `pairGibbsLawE_eq_pinnedLaw_E`.
Helper lemmas carry the prefix `wr4_`.
-/

set_option linter.unusedSectionVars false

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace HRS.MS.Wr

variable {d : ℕ}

set_option maxHeartbeats 1600000 in
/-- **Euclidean L² cavity marginal.**  See the module docstring. -/
theorem weak_marginal_strong_E (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d)
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
            = (HRS.Whole.withDensityReal ρ).withDensity f ∧ Measurable f ∧
          (∃ K : ℝ, ∀ x, (f x).toReal ≤ K) ∧
          Integrable (fun x => ((f x).toReal - 1) ^ 2) (HRS.Whole.withDensityReal ρ) ∧
          ∫ x, ((f x).toReal - 1) ^ 2 ∂(HRS.Whole.withDensityReal ρ)
            ≤ (C * deltaN d s N) ^ 2 := by
  obtain ⟨Ca, Cb, hCa, hCb, hrows⟩ := wr3_row_bounds_delta hd hs0 hsd A M
  set P : ℝ := max βp 0 + 1 with hP
  have hP1 : 1 ≤ P := by have := le_max_right βp 0; linarith
  have hP0 : 0 < P := by linarith
  set E : ℝ := Real.exp (2 * P) with hE
  have hE1 : 1 ≤ E := Real.one_le_exp (by linarith)
  have hE0 : 0 < E := by linarith
  set G₁ : ℝ := 2 * P * E * Ca + P ^ 2 * E * Cb with hG₁
  have hG₁0 : 0 ≤ G₁ := by positivity
  set Kc : ℝ := Real.sqrt (2 * (Cb + Ca ^ 2 * E)) with hKc
  have hKc2 : Kc ^ 2 = 2 * (Cb + Ca ^ 2 * E) := Real.sq_sqrt (by positivity)
  have hKc0 : 0 ≤ Kc := Real.sqrt_nonneg _
  set C₀ : ℝ := 150 * G₁ ^ 2 + 214 * P ^ 2 * Kc ^ 2 + 12 * P ^ 2 with hC₀
  set C : ℝ := Real.sqrt C₀ with hCdef
  have hC₀0 : 0 ≤ C₀ := by positivity
  have hC2 : C ^ 2 = C₀ := Real.sq_sqrt hC₀0
  refine ⟨min 1 (1 / (16 * E * P)), C, lt_min one_pos (by positivity), ?_⟩
  intro ρ hρ hM q hqm hqs hq0 hqA a ha0 ha hrow N hN β hβ τ hτ
  have hprob : IsProbabilityMeasure (HRS.Whole.withDensityReal ρ) :=
    HRS.Whole.Q34.isProbabilityMeasure_nu hρ
  set μ : Measure (Euc d) := HRS.Whole.withDensityReal ρ with hμ
  have hK : EWeakKernel μ a q := ⟨hqm, hqs, hq0, hrow⟩
  have hβ0 : 0 < β := lt_of_lt_of_le hβm hβ.1
  have hκ₀ : 0 ≤ τ * β := mul_nonneg hτ.1 hβ0.le
  have hκP : τ * β ≤ P := by
    have h1 : τ * β ≤ 1 * β := mul_le_mul_of_nonneg_right hτ.2 hβ0.le
    have h2 := hβ.2
    have h3 := le_max_left βp 0
    linarith
  have ha1 : a < 1 := lt_of_lt_of_le ha (min_le_left _ _)
  have haE : a < 1 / (16 * E * P) := lt_of_lt_of_le ha (min_le_right _ _)
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  have hn : 0 < n := by omega
  set κ₀ : ℝ := τ * β with hκ₀def
  set V := mkV_E hK ha0 hκ₀ with hV
  have hNR : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have hN1R : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ n + 1 by omega)
  have hκaE : κ₀ * a ≤ 1 / (16 * E) := by
    have h1 : κ₀ * a ≤ P * a := mul_le_mul_of_nonneg_right hκP ha0
    have h2 : P * a ≤ P * (1 / (16 * E * P)) := mul_le_mul_of_nonneg_left haE.le hP0.le
    have h3 : P * (1 / (16 * E * P)) = 1 / (16 * E) := by field_simp
    linarith
  have hκa0 : 0 ≤ κ₀ * a := mul_nonneg hκ₀ ha0
  set D : ℝ := Real.exp (V.M + V.M' + κ₀ * V.γ) with hDdef
  have hVM : V.M = κ₀ * a := rfl
  have hVM' : V.M' = 0 := rfl
  have hVγ : V.γ = a := rfl
  have hDe : D = Real.exp (κ₀ * a + κ₀ * a) := by
    simp only [hDdef, hVM, hVM', hVγ]; congr 1; ring
  have hDE : D ≤ E := by
    rw [hDe]
    refine Real.exp_le_exp.2 ?_
    have : κ₀ * a ≤ P := by nlinarith
    linarith
  have hD1 : 1 ≤ D := by rw [hDe]; exact Real.one_le_exp (by linarith)
  have hs : κ₀ * V.γ * D ≤ 1 / 4 := by
    rw [hVγ]
    have : κ₀ * a * D ≤ (1 / (16 * E)) * E := mul_le_mul hκaE hDE (by linarith) (by positivity)
    have h2 : (1 / (16 * E)) * E = 1 / 16 := by field_simp
    linarith
  have hs2 : 214 * (κ₀ * V.γ) ^ 2 ≤ 1 := by
    rw [hVγ]
    have h1 : κ₀ * a ≤ 1 / 16 := by
      have : 1 / (16 * E) ≤ 1 / 16 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
      linarith
    have h2 : (κ₀ * a) ^ 2 ≤ (1 / 16) ^ 2 := pow_le_pow_left₀ hκa0 h1 2
    nlinarith
  have hκ : HRS.External.weakKappa V κ₀ ≤ 1 / 2 := by
    have : HRS.External.weakKappa V κ₀ = 4 * D * (κ₀ * a) := by
      simp only [HRS.External.weakKappa, hDdef, hVγ]
    rw [this]
    have h1 : D * (κ₀ * a) ≤ E * (1 / (16 * E)) := mul_le_mul hDE hκaE hκa0 hE0.le
    have h2 : E * (1 / (16 * E)) = 1 / 16 := by field_simp
    linarith
  set δ : ℝ := deltaN d s (n + 1) with hδdef
  have hδ0 : 0 ≤ δ := HRS.deltaN_nonneg s (by omega)
  have hδ1 : (((n + 1 : ℕ) : ℝ))⁻¹ ≤ δ := HRS.WeakRef.inv_le_deltaN hd hs0 hsd (by omega)
  have hrowsx := fun x => hrows ρ hρ hM q hqm hq0 hqA (n + 1) hN x
  have hT1 : ∀ x, ∫ y, max (q x y - ((n + 1 : ℕ) : ℝ)) 0 ∂μ ≤ Ca * δ := fun x => (hrowsx x).1.2
  have hT2 : ∀ x, ∫ y, (min (q x y) ((n + 1 : ℕ) : ℝ)) ^ 2 ∂μ ≤ Cb * (((n + 1 : ℕ) : ℝ) * δ) :=
    fun x => (hrowsx x).2.2
  have hT10 : ∀ x, 0 ≤ ∫ y, max (q x y - ((n + 1 : ℕ) : ℝ)) 0 ∂μ :=
    fun x => integral_nonneg fun y => le_max_right _ _
  have hT20 : ∀ x, 0 ≤ ∫ y, (min (q x y) ((n + 1 : ℕ) : ℝ)) ^ 2 ∂μ :=
    fun x => integral_nonneg fun y => sq_nonneg _
  have hnN : (n : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ n
  have hD0 : 0 ≤ D := by linarith
  set εG : ℝ := (2 * κ₀ * D * Ca + κ₀ ^ 2 * D * Cb) * δ with hεG
  have hKA : ∀ x, 2 * ((κ₀ / ((n + 1 : ℕ) : ℝ)) * (n * (D * ∫ z, max (V.q x z - ((n + 1 : ℕ) : ℝ)) 0 ∂μ)))
        + (κ₀ / ((n + 1 : ℕ) : ℝ)) ^ 2 / 2 * (2 * n * (D * ∫ z, (min (V.q x z) ((n + 1 : ℕ) : ℝ)) ^ 2 ∂μ))
        ≤ εG := fun x =>
    HRS.WeakRef.ka_alg hκ₀ hD0 (Nat.cast_nonneg n) hNR hnN hδ0 (hT10 x) (hT20 x) (hT1 x) (hT2 x)
  set εc : ℝ := Kc * δ with hεc
  have hKB : ∀ ν₁ ν₂ : Measure (Euc d), IsProbabilityMeasure ν₁ → IsProbabilityMeasure ν₂ →
        ν₁ ≤ ENNReal.ofReal D • μ → ν₂ ≤ ENNReal.ofReal D • μ →
        (∀ A, MeasurableSet A → |ν₁.real A - ν₂.real A| ≤ HRS.External.weakKappa V κ₀ / ((n + 1 : ℕ) : ℝ)) →
        ∫ x, (∫ y, V.q x y ∂ν₁ - ∫ y, V.q x y ∂ν₂) ^ 2 ∂μ ≤ εc ^ 2 := by
    intro ν₁ ν₂ _ _ h₁ h₂ hTV
    have hκ0 : 0 ≤ HRS.External.weakKappa V κ₀ := HRS.External.weakKappa_nonneg V hκ₀
    have hcv := HRS.WeakRef.Abs.conv_measures (μ := μ) (q := q) hqm hq0 hqs hK.wr1_integrable_row
      (N := ((n + 1 : ℕ) : ℝ)) (a₂ := Ca * δ) (b₁ := Cb * (((n + 1 : ℕ) : ℝ) * δ)) (D := D)
      (ε₀ := HRS.External.weakKappa V κ₀ / ((n + 1 : ℕ) : ℝ)) hNR.le (by positivity)
      (by have := hδ0; positivity) (fun x => hT1 x) (fun x => hT2 x) hD0 ν₁ ν₂ h₁ h₂ hTV
    refine hcv.trans ?_
    have hε0 : 0 ≤ HRS.External.weakKappa V κ₀ / ((n + 1 : ℕ) : ℝ) := div_nonneg hκ0 hNR.le
    have h2ε : 2 * (HRS.External.weakKappa V κ₀ / ((n + 1 : ℕ) : ℝ)) ≤ 1 / ((n + 1 : ℕ) : ℝ) := by
      rw [← mul_div_assoc]
      exact div_le_div_of_nonneg_right (by linarith) hNR.le
    have := HRS.WeakRef.kb_alg hε0 h2ε hN1R hCa hCb hD0 hDE hδ0 hδ1
    have hKcδ : εc ^ 2 = 2 * (Cb + Ca ^ 2 * E) * δ ^ 2 := by rw [hεc, mul_pow, hKc2]
    rw [hKcδ]
    exact this
  obtain ⟨f, hfmap, hfm, ⟨K, hK'⟩, hfint⟩ :=
    HRS.WeakRef.Abs.marginal_L2 V hκ₀ hn (fun x => rfl)
      (by show 0 ≤ κ₀ * a; exact hκa0) (le_refl _) hκ hs hs2 hKA hKB
  have hfin := HRS.WeakRef.final_alg (Kc := Kc) (a := a) hκ₀ hκP hD0 hDE hCa hCb hδ0 ha0 ha1.le hNR hδ1
  have hCδ : (C * δ) ^ 2 = C₀ * δ ^ 2 := by rw [mul_pow, hC2]
  have hbound : ∫ x, ((f x).toReal - 1) ^ 2 ∂μ ≤ (C * δ) ^ 2 := by
    rw [hVγ] at hfint
    calc ∫ x, ((f x).toReal - 1) ^ 2 ∂μ
        ≤ 150 * εG ^ 2 + 214 * κ₀ ^ 2 * εc ^ 2 + 12 * (κ₀ * a / ((n + 1 : ℕ) : ℝ)) ^ 2 := hfint
      _ ≤ (150 * (2 * P * E * Ca + P ^ 2 * E * Cb) ^ 2 + 214 * P ^ 2 * Kc ^ 2 + 12 * P ^ 2) * δ ^ 2 := hfin
      _ = (C * δ) ^ 2 := by rw [hCδ, hC₀, hG₁]
  have hmap : (pairGibbsLawE q (n + 1) (τ * β) μ).map (fun X => X ⟨0, by omega⟩)
      = μ.withDensity f := by
    rw [pairGibbsLawE_eq_pinnedLaw_E hK ha0 hκ₀ (Nat.succ_pos n)]
    exact hfmap
  have hfm' : Measurable fun x => (f x).toReal := hfm.ennreal_toReal
  have hint : Integrable (fun x => ((f x).toReal - 1) ^ 2) μ := by
    refine Integrable.of_bound ((hfm'.sub_const 1).pow_const 2).aestronglyMeasurable
      ((max K 0 + 1) ^ 2) (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have h0 : 0 ≤ (f x).toReal := ENNReal.toReal_nonneg
    have h1 := hK' x
    have h2 : |(f x).toReal - 1| ≤ max K 0 + 1 := by
      rw [abs_le]; constructor <;> linarith [le_max_left K 0, le_max_right K 0]
    calc ((f x).toReal - 1) ^ 2 = |(f x).toReal - 1| ^ 2 := (sq_abs _).symm
      _ ≤ (max K 0 + 1) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h2 2
  exact ⟨f, hmap, hfm, ⟨K, hK'⟩, hint, hbound⟩

end HRS.MS.Wr
