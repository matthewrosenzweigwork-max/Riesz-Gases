import HRS.MS.S82RN10

/-!
# S8.2 R02 (S82R), N11: the pointwise pin comparison at the level of one weak potential
Constants `C` depend only on `d, q, M, Mψ, M₁, P, β, γ`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Function
open scoped ENNReal BigOperators

namespace HRS.MS.S82R
open HRS.External HRS HRS.Whole HRS.MS.Phase2S82

variable {d : ℕ}

theorem s82r_pin_density (hd : 2 ≤ d) {q : Euc d → ℝ} (hq : ShortRangePole d q) (M : ℝ)
    {Mψ M₁ P β γ : ℝ} (hβ : 0 < β) (hγ : 0 ≤ γ) (hP : β * γ ≤ P)
    (hα : β * γ * (Real.exp (Mψ + (M₁ + P)) + Real.exp (Mψ + (M₁ + P)) ^ 2) < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ρμ : Euc d → ℝ, HRS.Whole.IsProbDensity ρμ → (∀ x, ρμ x ≤ M) →
      ∀ (μ : Measure (Euc d)), μ = HRS.Whole.withDensityReal ρμ →
      ∀ (V : WeakPotential μ), (∀ x y, V.q x y = q (x - y)) →
      V.γ = γ → V.M ≤ Mψ → V.M' ≤ M₁ → IsField μ V.φ Mψ M₁ →
      ∀ {p n k : ℕ} [NeZero n] (pins : Fin p → Euc d), p ≤ k → k ≤ 4 → ∀ (i0 : Fin n),
      haveI : NeZero (n + k) := ⟨by have := NeZero.ne n; omega⟩
      ∀ᵐ z ∂μ,
        |(((pinnedLaw V (β / ((n + k : ℕ) : ℝ)) n pins).map (fun y => y i0)).rnDeriv μ z).toReal -
          ((RefMarg.cavMarg V (β / ((n + k : ℕ) : ℝ)) (n + k)).rnDeriv μ z).toReal| ≤
          C / ((n + k : ℕ) : ℝ) * (1 + ∑ ℓ, q (z - pins ℓ)) ∧
        (((pinnedLaw V (β / ((n + k : ℕ) : ℝ)) n pins).map (fun y => y i0)).rnDeriv μ z).toReal ≤
          Real.exp (Mψ + M₁ + β * γ) ∧
        ((RefMarg.cavMarg V (β / ((n + k : ℕ) : ℝ)) (n + k)).rnDeriv μ z).toReal ≤
          Real.exp (Mψ + M₁ + β * γ) := by
  obtain ⟨A1, B1, hA1, hB1, h1⟩ := s82r_pins_to_cav hd hq M hβ hγ hα
  obtain ⟨A2, B2, hA2, hB2, h2⟩ := s82r_cav_chain hd hq M hβ hγ hα
  set K : ℝ := Real.exp (Mψ + M₁ + β * γ) with hK
  have hK0 : 0 < K := Real.exp_pos _
  set C0 : ℝ := A1 + 4 * B1 + 4 * K * (A2 * γ + B2) with hC0
  have hC00 : 0 ≤ C0 := by positivity
  refine ⟨β * C0, mul_nonneg hβ.le hC00, fun ρμ hρ hM μ hμ V hVq hVγ hVM hVM' hψ p n k _ pins hpk hk4 i0 => ?_⟩
  subst hμ
  haveI : IsProbabilityMeasure (HRS.Whole.withDensityReal ρμ) := HRS.Whole.Q34.isProbabilityMeasure_nu hρ
  haveI : NeZero (n + k) := ⟨by have := NeZero.ne n; omega⟩
  have hn1 : 1 ≤ n := Nat.pos_of_ne_zero (NeZero.ne n)
  set N : ℕ := n + k with hN
  have hN0 : 0 < N := by omega
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN0
  set lam : ℝ := β / (N : ℝ) with hlam
  have hlam0 : 0 ≤ lam := by positivity
  have hlamN : lam * (N : ℝ) = β := by rw [hlam]; field_simp
  have hqm : Measurable q := hq.measurable
  have hq0 := hq.nonneg
  have hqi : ∀ w : Euc d, Integrable (fun u => q (u - w)) (HRS.Whole.withDensityReal ρμ) := fun w =>
    s82r_row_integrable hd hq hρ hM w
  -- marginal domination at every level
  have hmarg : ∀ m : ℕ, m ≤ N → ∀ [NeZero m] (i : Fin m),
      (pinnedLaw V lam m (fun e : Empty => e.elim)).map (fun y => y i) ≤
        ENNReal.ofReal K • (HRS.Whole.withDensityReal ρμ) := by
    intro m hm _ i
    have h := RefMarg.marginal_le_smul (B := Empty) V hβ.le hN0 (n := m) (by simpa using hm)
      (fun e : Empty => e.elim) i
    refine h.trans ?_
    intro A
    simp only [Measure.smul_apply, smul_eq_mul]
    gcongr
    rw [hK, hVγ]
    exact Real.exp_le_exp.2 (by linarith)
  have hmarg_pins : (pinnedLaw V lam n pins).map (fun y => y i0) ≤
      ENNReal.ofReal K • (HRS.Whole.withDensityReal ρμ) := by
    have h := RefMarg.marginal_le_smul (B := Fin p) V hβ.le hN0 (n := n)
      (by simp only [Fintype.card_fin]; omega) pins i0
    refine h.trans ?_
    intro A
    simp only [Measure.smul_apply, smul_eq_mul]
    gcongr
    rw [hK, hVγ]
    exact Real.exp_le_exp.2 (by linarith)
  have hPn : lam * ((p : ℝ) + n) * γ ≤ P := by
    refine le_trans ?_ hP
    have : lam * ((p : ℝ) + n) ≤ β := by
      rw [← hlamN]
      refine mul_le_mul_of_nonneg_left ?_ hlam0
      have : (p : ℝ) + n ≤ N := by exact_mod_cast (by omega : p + n ≤ N)
      exact this
    exact mul_le_mul_of_nonneg_right this hγ
  have hPN : lam * (N : ℝ) * γ ≤ P := by rw [hlamN]; exact hP
  have hnlN : ((N : ℝ) - 1) * lam ≤ β := by nlinarith [hlamN]
  have hnln : ((n : ℝ) - 1) * lam ≤ β := by
    have : (n : ℝ) ≤ N := by exact_mod_cast (by omega : n ≤ N)
    nlinarith [hlamN]
  have hcav : ∀ {S : Set (Euc d)}, MeasurableSet S →
      |(RefMarg.cavMarg V lam (n + k)).real S - (RefMarg.cavMarg V lam n).real S| ≤
        k * (K * (lam * (A2 * γ + B2))) * (HRS.Whole.withDensityReal ρμ).real S := fun {S} hS =>
    h2 ρμ hρ hM _ rfl V hVq hVγ hψ (N := N) (lam := lam) hlam0 hPN hnlN (K' := K) hK0.le hmarg
      (n := n) k (by omega) hS
  have hpins := h1 ρμ hρ hM _ rfl V hVq hVγ hψ (lam := lam) hlam0 (p := p) (n := n) pins hPn hnln
  set ρ : Euc d → ℝ := fun z => ∑ ℓ, lam * (A1 * q (z - pins ℓ) + B1) +
    k * (K * (lam * (A2 * γ + B2))) with hρdef
  have hρi : Integrable ρ (HRS.Whole.withDensityReal ρμ) :=
    (integrable_finset_sum _ fun ℓ _ =>
      (((hqi (pins ℓ)).const_mul A1).add (integrable_const B1)).const_mul lam).add (integrable_const _)
  have hset : ∀ S : Set (Euc d), MeasurableSet S →
      |((pinnedLaw V lam n pins).map (fun y => y i0)).real S -
        (RefMarg.cavMarg V lam (n + k)).real S| ≤ ∫ z in S, ρ z ∂(HRS.Whole.withDensityReal ρμ) := by
    intro S hS
    have ha := hpins i0 hS
    have hb := hcav hS
    have hint1 : Integrable (fun z => ∑ ℓ, lam * (A1 * q (z - pins ℓ) + B1)) (HRS.Whole.withDensityReal ρμ) :=
      integrable_finset_sum _ fun ℓ _ =>
        (((hqi (pins ℓ)).const_mul A1).add (integrable_const B1)).const_mul lam
    have e : ∫ z in S, ρ z ∂(HRS.Whole.withDensityReal ρμ) =
        ∫ z in S, ∑ ℓ, lam * (A1 * q (z - pins ℓ) + B1) ∂(HRS.Whole.withDensityReal ρμ) +
          k * (K * (lam * (A2 * γ + B2))) * (HRS.Whole.withDensityReal ρμ).real S := by
      rw [hρdef]
      simp only
      rw [integral_add hint1.integrableOn (integrable_const _).integrableOn]
      simp only [setIntegral_const, smul_eq_mul]
      ring
    rw [e]
    calc _ ≤ |((pinnedLaw V lam n pins).map (fun y => y i0)).real S - (RefMarg.cavMarg V lam n).real S| +
          |(RefMarg.cavMarg V lam n).real S - (RefMarg.cavMarg V lam (n + k)).real S| := abs_sub_le _ _ _
      _ ≤ _ := by
        refine add_le_add ha ?_
        rw [abs_sub_comm]
        exact hb
  haveI := isProb_pinnedLaw V hlam0 n pins
  haveI := isProb_pinnedLaw V hlam0 (n + k) (fun e : Empty => e.elim)
  haveI : IsProbabilityMeasure ((pinnedLaw V lam n pins).map (fun y => y i0)) :=
    inferInstance
  haveI : IsProbabilityMeasure (RefMarg.cavMarg V lam (n + k)) :=
    inferInstanceAs (IsProbabilityMeasure ((pinnedLaw V lam (n + k) (fun e : Empty => e.elim)).map
      (fun y => y 0)))
  have hm2 : RefMarg.cavMarg V lam (n + k) ≤ ENNReal.ofReal K • (HRS.Whole.withDensityReal ρμ) :=
    hmarg N le_rfl 0
  have hac1 := Measure.absolutelyContinuous_of_le_smul hmarg_pins
  have hac2 := Measure.absolutelyContinuous_of_le_smul hm2
  have habs := s82r_rn_abs_le hac1 hac2 hρi hset
  have hle1 := s82r_rn_le hK0.le hmarg_pins
  have hle2 := s82r_rn_le hK0.le hm2
  filter_upwards [habs, hle1, hle2] with z ha hb hc
  refine ⟨ha.trans ?_, hb, hc⟩
  have hsq : 0 ≤ ∑ ℓ, q (z - pins ℓ) := Finset.sum_nonneg fun ℓ _ => hq0 _
  have hρz : ρ z = lam * (A1 * ∑ ℓ, q (z - pins ℓ) + p * B1 + k * (K * (A2 * γ + B2))) := by
    rw [hρdef]
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    ring
  have hp4 : (p : ℝ) ≤ 4 := by exact_mod_cast (by omega : p ≤ 4)
  have hk4' : (k : ℝ) ≤ 4 := by exact_mod_cast hk4
  have hX : A1 * ∑ ℓ, q (z - pins ℓ) + p * B1 + k * (K * (A2 * γ + B2)) ≤ C0 * (1 + ∑ ℓ, q (z - pins ℓ)) := by
    have h3 : (k : ℝ) * (K * (A2 * γ + B2)) ≤ 4 * (K * (A2 * γ + B2)) :=
      mul_le_mul_of_nonneg_right hk4' (by positivity)
    have h4 : (p : ℝ) * B1 ≤ 4 * B1 := mul_le_mul_of_nonneg_right hp4 hB1
    have h5 : A1 * ∑ ℓ, q (z - pins ℓ) ≤ C0 * ∑ ℓ, q (z - pins ℓ) :=
      mul_le_mul_of_nonneg_right (by rw [hC0]; nlinarith [hB1, mul_nonneg hK0.le (add_nonneg (mul_nonneg hA2 hγ) hB2)]) hsq
    nlinarith [h3, h4, h5]
  rw [hρz]
  have : lam * (C0 * (1 + ∑ ℓ, q (z - pins ℓ))) = β * C0 / (N : ℝ) * (1 + ∑ ℓ, q (z - pins ℓ)) := by
    rw [hlam]; ring
  calc _ ≤ lam * (C0 * (1 + ∑ ℓ, q (z - pins ℓ))) := mul_le_mul_of_nonneg_left hX hlam0
    _ = _ := this

end HRS.MS.S82R

end
