import HRS.Energy.PressureProof

/-!
# MOVSX Aux1: Lemma 5.7 (`N:lem:weak-pressure`) with a sup bound in place of smoothness

Copies of `weak_marginal_strong`, `weak_pressure_upper_proof`, `weak_reference_pressure`
(`HRS/Energy/WeakReference.lean`), whose proofs use the smoothness of `ρ` only through the sup bound
`ρ ≤ Λ0` (`WeakRef.le_cbNorm_zero`) and not at all the lower bound `c₀`.  The hypotheses `IsSmooth ρ`,
`c₀ ≤ ρ`, `cbNorm k ρ ≤ Λ k` are replaced by `ρ ≤ Λ0`.
-/

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace HRS

variable {d : ℕ}

set_option maxHeartbeats 1600000 in
/-- Strong form of the marginal bound `N:eq:weak-marginal` (real-valued `L²` integral, with a measurable
bounded density), proved by the cavity formula, the Laplace residual, the `L²` convolution estimate and the
Schur contraction (source lines 6206-6268). -/
theorem movsx_weak_marginal_strong (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d)
    (cstar : ℝ) (hw : ∀ z : Torus d, z ≠ 0 → 1 ≤ periodicRiesz d s z + cstar)
    (βm βp : ℝ) (hβm : 0 < βm) (Λ0 : ℝ) (A : ℝ) :
    ∃ a₀ C : ℝ, 0 < a₀ ∧
      ∀ ρ : Torus d → ℝ, IsProbDensity ρ → ∀ [IsProbabilityMeasure (withDensityReal ρ)],
        (∀ x, ρ x ≤ Λ0) →
      ∀ q : Torus d → Torus d → ℝ, Measurable (Function.uncurry q) → (∀ x y, q x y = q y x) →
        (∀ x y, 0 ≤ q x y) → (∀ x y, q x y ≤ A * (periodicRiesz d s (x - y) + cstar)) →
      ∀ a : ℝ, 0 ≤ a → a < a₀ →
        (∀ x, ∫⁻ y, ENNReal.ofReal (q x y) ∂(withDensityReal ρ) ≤ ENNReal.ofReal a) →
      ∀ N : ℕ, ∀ hN : 2 ≤ N, ∀ β ∈ Set.Icc βm βp, ∀ τ ∈ Set.Icc (0 : ℝ) 1,
        ∃ f : Torus d → ℝ≥0∞,
          (pairGibbsLaw q N (τ * β) (withDensityReal ρ)).map (fun X => X ⟨0, by omega⟩)
            = (withDensityReal ρ).withDensity f ∧ Measurable f ∧ (∃ K : ℝ, ∀ x, (f x).toReal ≤ K) ∧
          ∫ x, ((f x).toReal - 1) ^ 2 ∂(withDensityReal ρ) ≤ (C * deltaN d s N) ^ 2 := by
  set Λ₀ : ℝ := max Λ0 1 with hΛ₀
  have hΛ₀0 : 0 ≤ Λ₀ := by have := le_max_right Λ0 1; linarith
  obtain ⟨Ca, Cb, hCa, hCb, hrows⟩ := WeakRef.row_bounds hd hs0 hsd cstar hw A Λ₀ hΛ₀0
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
  intro ρ hρ hprob hρΛ q hqm hqs hq0 hqA a ha0 ha hrow N hN β hβ τ hτ
  set μ : Measure (Torus d) := withDensityReal ρ with hμ
  have hρle : ∀ x, ρ x ≤ Λ₀ := fun x =>
    (hρΛ x).trans (le_max_left _ _)
  have hK : WeakRef.WeakKernel μ a q := ⟨hqm, hqs, hq0, hrow⟩
  have hβ0 : 0 < β := lt_of_lt_of_le hβm hβ.1
  have hκ₀ : 0 ≤ τ * β := mul_nonneg hτ.1 hβ0.le
  have hκP : τ * β ≤ P := by
    have h1 : τ * β ≤ 1 * β := mul_le_mul_of_nonneg_right hτ.2 hβ0.le
    have h2 := hβ.2
    have h3 := le_max_left βp 0
    linarith
  have ha1 : a < 1 := lt_of_lt_of_le ha (min_le_left _ _)
  have haE : a < 1 / (16 * E * P) := lt_of_lt_of_le ha (min_le_right _ _)
  have hnN : 0 < N := by omega
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  have hn : 0 < n := by omega
  set κ₀ : ℝ := τ * β with hκ₀def
  set V := WeakRef.mkV hK ha0 hκ₀ with hV
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
  have hκ : External.weakKappa V κ₀ ≤ 1 / 2 := by
    have : External.weakKappa V κ₀ = 4 * D * (κ₀ * a) := by
      simp only [External.weakKappa, hDdef, hVγ]
    rw [this]
    have h1 : D * (κ₀ * a) ≤ E * (1 / (16 * E)) := mul_le_mul hDE hκaE hκa0 hE0.le
    have h2 : E * (1 / (16 * E)) = 1 / 16 := by field_simp
    linarith
  set δ : ℝ := deltaN d s (n + 1) with hδdef
  have hδ0 : 0 ≤ δ := deltaN_nonneg s (by omega)
  have hδ1 : (((n + 1 : ℕ) : ℝ))⁻¹ ≤ δ := WeakRef.inv_le_deltaN hd hs0 hsd (by omega)
  have hrowsx := fun x => hrows ρ hρle q hqm hq0 hqA (n + 1) hN x
  have hT1 : ∀ x, ∫ y, max (q x y - ((n + 1 : ℕ) : ℝ)) 0 ∂μ ≤ Ca * δ := fun x => (hrowsx x).1
  have hT2 : ∀ x, ∫ y, (min (q x y) ((n + 1 : ℕ) : ℝ)) ^ 2 ∂μ ≤ Cb * (((n + 1 : ℕ) : ℝ) * δ) :=
    fun x => (hrowsx x).2
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
    WeakRef.ka_alg hκ₀ hD0 (Nat.cast_nonneg n) hNR hnN hδ0 (hT10 x) (hT20 x) (hT1 x) (hT2 x)
  set εc : ℝ := Kc * δ with hεc
  have hKB : ∀ ν₁ ν₂ : Measure (Torus d), IsProbabilityMeasure ν₁ → IsProbabilityMeasure ν₂ →
        ν₁ ≤ ENNReal.ofReal D • μ → ν₂ ≤ ENNReal.ofReal D • μ →
        (∀ A, MeasurableSet A → |ν₁.real A - ν₂.real A| ≤ External.weakKappa V κ₀ / ((n + 1 : ℕ) : ℝ)) →
        ∫ x, (∫ y, V.q x y ∂ν₁ - ∫ y, V.q x y ∂ν₂) ^ 2 ∂μ ≤ εc ^ 2 := by
    intro ν₁ ν₂ _ _ h₁ h₂ hTV
    have hκ0 : 0 ≤ External.weakKappa V κ₀ := External.weakKappa_nonneg V hκ₀
    have hcv := WeakRef.Abs.conv_measures (μ := μ) (q := q) hqm hq0 hqs hK.integrable_row
      (N := ((n + 1 : ℕ) : ℝ)) (a₂ := Ca * δ) (b₁ := Cb * (((n + 1 : ℕ) : ℝ) * δ)) (D := D)
      (ε₀ := External.weakKappa V κ₀ / ((n + 1 : ℕ) : ℝ)) hNR.le (by positivity)
      (by have := hδ0; positivity) (fun x => hT1 x) (fun x => hT2 x) hD0 ν₁ ν₂ h₁ h₂ hTV
    refine hcv.trans ?_
    have hε0 : 0 ≤ External.weakKappa V κ₀ / ((n + 1 : ℕ) : ℝ) := div_nonneg hκ0 hNR.le
    have h2ε : 2 * (External.weakKappa V κ₀ / ((n + 1 : ℕ) : ℝ)) ≤ 1 / ((n + 1 : ℕ) : ℝ) := by
      rw [← mul_div_assoc]
      exact div_le_div_of_nonneg_right (by linarith) hNR.le
    have := WeakRef.kb_alg hε0 h2ε hN1R hCa hCb hD0 hDE hδ0 hδ1
    have hKcδ : εc ^ 2 = 2 * (Cb + Ca ^ 2 * E) * δ ^ 2 := by rw [hεc, mul_pow, hKc2]
    rw [hKcδ]
    exact this
  obtain ⟨f, hfmap, hfm, ⟨K, hK'⟩, hfint⟩ := WeakRef.Abs.marginal_L2 V hκ₀ hn (fun x => rfl)
    (by show 0 ≤ κ₀ * a; exact hκa0) (le_refl _) hκ hs hs2 hKA hKB
  have hfin := WeakRef.final_alg (Kc := Kc) (a := a) hκ₀ hκP hD0 hDE hCa hCb hδ0 ha0 ha1.le hNR hδ1
  have hCδ : (C * δ) ^ 2 = C₀ * δ ^ 2 := by rw [mul_pow, hC2]
  have hbound : ∫ x, ((f x).toReal - 1) ^ 2 ∂μ ≤ (C * δ) ^ 2 := by
    rw [hVγ] at hfint
    calc ∫ x, ((f x).toReal - 1) ^ 2 ∂μ
        ≤ 150 * εG ^ 2 + 214 * κ₀ ^ 2 * εc ^ 2 + 12 * (κ₀ * a / ((n + 1 : ℕ) : ℝ)) ^ 2 := hfint
      _ ≤ (150 * (2 * P * E * Ca + P ^ 2 * E * Cb) ^ 2 + 214 * P ^ 2 * Kc ^ 2 + 12 * P ^ 2) * δ ^ 2 := hfin
      _ = (C * δ) ^ 2 := by rw [hCδ, hC₀, hG₁]
  have hmap : (pairGibbsLaw q (n + 1) (τ * β) μ).map (fun X => X ⟨0, by omega⟩)
      = μ.withDensity f := by
    rw [WeakRef.pairGibbsLaw_eq_pinnedLaw hK ha0 hκ₀ (Nat.succ_pos n)]
    exact hfmap
  exact ⟨f, hmap, hfm, ⟨K, hK'⟩, hbound⟩

set_option maxHeartbeats 800000 in
theorem movsx_weak_pressure_upper_proof (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d)
    (cstar : ℝ) (hw : ∀ z : Torus d, z ≠ 0 → 1 ≤ periodicRiesz d s z + cstar)
    (βm βp : ℝ) (hβm : 0 < βm) (Λ0 : ℝ) (A : ℝ) :
    ∃ a₀ C : ℝ, 0 < a₀ ∧
      ∀ ρ : Torus d → ℝ, IsProbDensity ρ → (∀ x, ρ x ≤ Λ0) →
      ∀ q : Torus d → Torus d → ℝ, Measurable (Function.uncurry q) → (∀ x y, q x y = q y x) →
        (∀ x y, 0 ≤ q x y) → (∀ x y, q x y ≤ A * (periodicRiesz d s (x - y) + cstar)) →
      ∀ a : ℝ, 0 ≤ a → a < a₀ →
        (∀ x, ∫⁻ y, ENNReal.ofReal (q x y) ∂(withDensityReal ρ) ≤ ENNReal.ofReal a) →
      ∀ N : ℕ, 2 ≤ N → ∀ β ∈ Set.Icc βm βp,
        pairPartition q N β (withDensityReal ρ) ≤
          ENNReal.ofReal (Real.exp (C * N * deltaN d s N)) := by
  obtain ⟨a₀', Cm, ha₀', hmarg⟩ := movsx_weak_marginal_strong hd s hs0 hsd cstar hw βm βp hβm Λ0 A
  set Λ₀ : ℝ := max Λ0 1 with hΛ₀
  have hΛ₀0 : 0 ≤ Λ₀ := by have := le_max_right Λ0 1; linarith
  obtain ⟨Ca, Cb, hCa, hCb, hrows⟩ := WeakRef.row_bounds_real hd hs0 hsd cstar hw A Λ₀ hΛ₀0
  set P : ℝ := max βp 0 + 1 with hP
  have hP1 : 1 ≤ P := by have := le_max_right βp 0; linarith
  have hP0 : 0 < P := by linarith
  set E : ℝ := Real.exp (2 * P) with hE
  have hE1 : 1 ≤ E := Real.one_le_exp (by linarith)
  have hE0 : 0 < E := by linarith
  obtain ⟨Cw, hCw0, hWex⟩ := WeakRef.exists_W hd hs0 hsd hP1 hβm
  set Cm' : ℝ := |Cm| with hCm'
  have hCm0 : 0 ≤ Cm' := abs_nonneg _
  set A₁ : ℝ := 8 * E * Cb with hA₁
  set A₂ : ℝ := 12 * (1 + 2 * E * Ca) ^ 2 + 12 + 12 * E * Cm' ^ 2 with hA₂
  have hA₁0 : 0 ≤ A₁ := by positivity
  have hA₂0 : 0 ≤ A₂ := by positivity
  refine ⟨min a₀' (min 1 (1 / (16 * E * P))), P * (1 / 2 + A₁ * Cw + A₂ * P),
    lt_min ha₀' (lt_min one_pos (by positivity)), ?_⟩
  intro ρ hρ hρΛ q hqm hqs hq0 hqA a ha0 ha hrow N hN β hβ
  haveI hprob : IsProbabilityMeasure (withDensityReal ρ) := isProb_withDensityReal hρ
  set μ : Measure (Torus d) := withDensityReal ρ with hμ
  have hK : WeakRef.WeakKernel μ a q := ⟨hqm, hqs, hq0, hrow⟩
  have hρle : ∀ x, ρ x ≤ Λ₀ := fun x =>
    (hρΛ x).trans (le_max_left _ _)
  have hrowsx := fun x => hrows ρ hρle q hqm hq0 hqA x
  have ha₁ : a < a₀' := lt_of_lt_of_le ha (min_le_left _ _)
  have ha1 : a < 1 := lt_of_lt_of_le ha ((min_le_right _ _).trans (min_le_left _ _))
  have haE : a < 1 / (16 * E * P) :=
    lt_of_lt_of_le ha ((min_le_right _ _).trans (min_le_right _ _))
  have hβ0 : 0 < β := lt_of_lt_of_le hβm hβ.1
  have hβP : β ≤ P := by have := hβ.2; have := le_max_left βp 0; linarith
  have hN1 : 1 ≤ N := by omega
  obtain ⟨W₁, hW₁d, hW₁c, hW₁0, hW₁b⟩ := hWex N hN1
  have hpsiN := WeakRef.psi2_ge_one hd hs0 (show (1 : ℝ) ≤ N by exact_mod_cast hN1)
  have hNδ := WeakRef.mul_deltaN_eq_psi2 (d := d) s hN1
  set V : ℝ → ℝ := fun t => A₁ * WeakRef.psi2 d s (2 * N * P / t) + A₂ * WeakRef.psi2 d s N with hVdef
  set W : ℝ → ℝ := fun t => A₁ * W₁ t + A₂ * WeakRef.psi2 d s N * t with hWdef
  have hup := hK.pairPartition_upper ha0 (show 0 < N by omega) hβ0 (V := V) (W := W)
    ?_ ?_ ?_ ?_ ?_
  · refine hup.trans (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_))
    have hWβ : W β ≤ (A₁ * Cw + A₂ * P) * WeakRef.psi2 d s N := by
      have h1 := hW₁b β hβ.1 hβP
      have h2 : A₂ * WeakRef.psi2 d s N * β ≤ A₂ * P * WeakRef.psi2 d s N := by
        have : 0 ≤ A₂ * WeakRef.psi2 d s N := by positivity
        nlinarith
      simp only [hWdef]
      nlinarith [mul_le_mul_of_nonneg_left h1 hA₁0]
    have hS0 : 0 ≤ (1 / 2 + A₁ * Cw + A₂ * P) * WeakRef.psi2 d s N := by
      have : 0 ≤ 1 / 2 + A₁ * Cw + A₂ * P := by positivity
      exact mul_nonneg this (by linarith)
    have hx : a / 2 + W β ≤ (1 / 2 + A₁ * Cw + A₂ * P) * WeakRef.psi2 d s N := by nlinarith
    calc β * (a / 2 + W β) ≤ β * ((1 / 2 + A₁ * Cw + A₂ * P) * WeakRef.psi2 d s N) :=
          mul_le_mul_of_nonneg_left hx hβ0.le
      _ ≤ P * ((1 / 2 + A₁ * Cw + A₂ * P) * WeakRef.psi2 d s N) := mul_le_mul_of_nonneg_right hβP hS0
      _ = P * (1 / 2 + A₁ * Cw + A₂ * P) * ((N : ℝ) * deltaN d s N) := by rw [hNδ]; ring
      _ = _ := by ring
  · intro t ht
    have htβ : t ≤ β := ht.2
    have htP : t ≤ P := htβ.trans hβP
    have hτ : t / β ∈ Set.Icc (0 : ℝ) 1 := ⟨div_nonneg ht.1.le hβ0.le, (div_le_one hβ0).2 htβ⟩
    obtain ⟨f, hf1, hf2, -, hf4⟩ :=
      hmarg ρ hρ hρΛ q hqm hqs hq0 hqA a ha0 ha₁ hrow N hN β hβ (t / β) hτ
    rw [div_mul_cancel₀ _ hβ0.ne'] at hf1
    have hta : t * a ≤ 1 / (16 * E) := by
      have h1 : t * a ≤ P * a := mul_le_mul_of_nonneg_right htP ha0
      have h2 : P * a ≤ P * (1 / (16 * E * P)) := mul_le_mul_of_nonneg_left haE.le hP0.le
      have h3 : P * (1 / (16 * E * P)) = 1 / (16 * E) := by field_simp
      linarith
    have hf5 : ∫ x, ((f x).toReal - 1) ^ 2 ∂μ ≤ (Cm' * deltaN d s N) ^ 2 := by
      refine hf4.trans (le_of_eq ?_)
      rw [hCm', mul_pow, mul_pow, sq_abs]
    exact WeakRef.variance_at hd hs0 hsd hK ha0 ha1.le hCa hCb hCm0 hP1 hE
      (fun x => (hrowsx x).1) (fun x => (hrowsx x).2) hN ht.1 htP hta ⟨f, hf1, hf2, hf5⟩
  · intro t ht
    have htP : t ≤ P := ht.2.trans hβP
    have hL : (1 : ℝ) ≤ 2 * N * P / t := by
      rw [le_div_iff₀ ht.1]
      have : (1 : ℝ) ≤ N := by exact_mod_cast hN1
      nlinarith
    have := WeakRef.psi2_ge_one hd hs0 hL
    exact add_nonneg (mul_nonneg hA₁0 (by linarith)) (mul_nonneg hA₂0 (by linarith))
  · intro t ht
    have h := ((hW₁d t ht).const_mul A₁).add ((hasDerivAt_id t).const_mul (A₂ * WeakRef.psi2 d s N))
    exact h.congr_deriv (by simp [hVdef])
  · exact (hW₁c.const_mul A₁).add ((continuous_const.mul continuous_id).continuousWithinAt)
  · simp [hWdef, hW₁0]


theorem movsx_weak_reference_pressure (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d)
    (cstar : ℝ) (hw : ∀ z : Torus d, z ≠ 0 → 1 ≤ periodicRiesz d s z + cstar)
    (βm βp : ℝ) (hβm : 0 < βm) (Λ0 : ℝ) (A : ℝ) :
    ∃ a₀ C : ℝ, 0 < a₀ ∧
      ∀ ρ : Torus d → ℝ, IsProbDensity ρ → (∀ x, ρ x ≤ Λ0) →
      ∀ q : Torus d → Torus d → ℝ, Measurable (Function.uncurry q) → (∀ x y, q x y = q y x) →
        (∀ x y, 0 ≤ q x y) → (∀ x y, q x y ≤ A * (periodicRiesz d s (x - y) + cstar)) →
      ∀ a : ℝ, 0 ≤ a → a < a₀ →
        (∀ x, ∫⁻ y, ENNReal.ofReal (q x y) ∂(withDensityReal ρ) ≤ ENNReal.ofReal a) →
      ∀ N : ℕ, 2 ≤ N → ∀ β ∈ Set.Icc βm βp,
        ENNReal.ofReal (Real.exp (-(C * N * deltaN d s N))) ≤
            pairPartition q N β (withDensityReal ρ) ∧
          pairPartition q N β (withDensityReal ρ) ≤
            ENNReal.ofReal (Real.exp (C * N * deltaN d s N)) := by
  obtain ⟨a₀, C₀, ha₀, hup⟩ := movsx_weak_pressure_upper_proof hd s hs0 hsd cstar hw βm βp hβm Λ0 A
  refine ⟨a₀, max C₀ 0, ha₀, ?_⟩
  intro ρ hρ hρΛ q hqm hqs hq0 hqA a ha0 ha hrow N hN β hβ
  have : IsProbabilityMeasure (withDensityReal ρ) := isProb_withDensityReal hρ
  have hK : WeakRef.WeakKernel (withDensityReal ρ) a q := ⟨hqm, hqs, hq0, hrow⟩
  have hβ0 : 0 ≤ β := (hβm.trans_le hβ.1).le
  have hN0 : 0 < N := by omega
  have hδ : 0 ≤ (N : ℝ) * deltaN d s N :=
    mul_nonneg (Nat.cast_nonneg N) (deltaN_nonneg s (by omega))
  refine ⟨?_, ?_⟩
  · refine le_trans ?_ (hK.one_le_partition ha0 hβ0 hN0)
    refine ENNReal.ofReal_le_one.2 (Real.exp_le_one_iff.2 ?_)
    have : 0 ≤ max C₀ 0 * ((N : ℝ) * deltaN d s N) := mul_nonneg (le_max_right _ _) hδ
    linarith [show max C₀ 0 * N * deltaN d s N = max C₀ 0 * ((N : ℝ) * deltaN d s N) by ring]
  · refine (hup ρ hρ hρΛ q hqm hqs hq0 hqA a ha0 ha hrow N hN β hβ).trans ?_
    refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
    have : C₀ * ((N : ℝ) * deltaN d s N) ≤ max C₀ 0 * ((N : ℝ) * deltaN d s N) :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) hδ
    linarith [show max C₀ 0 * N * deltaN d s N = max C₀ 0 * ((N : ℝ) * deltaN d s N) by ring,
      show C₀ * N * deltaN d s N = C₀ * ((N : ℝ) * deltaN d s N) by ring]

end HRS

end
