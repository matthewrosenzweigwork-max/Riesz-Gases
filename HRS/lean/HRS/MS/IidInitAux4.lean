import HRS.MS.IidInitAux3
import HRS.MS.SuppU5
import HRS.Whole.AppendixALemmas2
import HRS.Whole.AppendixBField

/-!
# SA27, part 4: from the adjoint inputs to the `C_b^1` data, and the coupling at one time

* `sa27_psi_facts`, `sa27_fieldInput`: `AdjointInputOneD` at order `j ≥ 1` gives the `C_b^1` bound (`AdjointInputOne`)
  needed by S.B.2.
* `sa27_time_coupling`: for the particle coefficient `S.coeff N` and the limiting coefficient `L.coeff S`, two `H^{-q}`
  representatives of `φ ↦ A_N η(U_N^{0,t}φ)` and `φ ↦ A η(U_∞^{0,t}φ)` of the same bridge are `L²`-close:
  `E‖Y - J‖² ≤ ((K_st⁺ + K_adj⁺) Δ_N)²` (`AdjointStabilityInputRd`, `Δ_N = coeffDiscrepancyRd`).
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MS.IidInit

open HRS HRS.Whole HRS.MP.HNegInfra HRS.MP.RdProp HRS.U5 HRS.Whole.AppendixA
open HRS.Whole.AppendixALemmas (AdjointInputOneD AdjointDerivInput)

variable {d : ℕ}

/-- The `C_b^1` data of the orbit at one time from `AdjointInputOneD` at order `j ≥ 1`. -/
theorem sa27_psi_facts {Γ : ℝ} {j : ℕ} (hj : 1 ≤ j) {C : WholeCoeff d} {T K : ℝ}
    (h : AdjointInputOneD Γ j C T K) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    (∀ φ, IsSobolevTest Γ φ → MemCb 1 (propagatorW C 0 t φ) ∧
        cbNorm 1 (propagatorW C 0 t φ) ≤ ((1 + d) * K) * HRS.Whole.sobolevNorm Γ φ ∧
        ∀ x, |propagatorW C 0 t φ x| ≤ K * HRS.Whole.sobolevNorm Γ φ) ∧
    (∀ (φ φ₂ : Euc d → ℝ) (c : ℝ), IsSobolevTest Γ φ → IsSobolevTest Γ φ₂ →
      propagatorW C 0 t (φ + c • φ₂) = propagatorW C 0 t φ + c • propagatorW C 0 t φ₂) := by
  refine ⟨fun φ hφ => ?_, fun φ φ₂ c hφ hφ₂ => ?_⟩
  · obtain ⟨-, hcd, -, hbd⟩ := h 0 t le_rfl ht.1 ht.2 φ hφ
    have h0 : ∀ x, |propagatorW C 0 t φ x| ≤ K * HRS.Whole.sobolevNorm Γ φ := fun x => by
      have := hbd 0 (Nat.zero_le _) (fun l => l.elim0) x
      simpa [partialDeriv] using this
    have h1 : ∀ (i : Fin 1 → Fin d) (x : Euc d),
        |partialDeriv i (propagatorW C 0 t φ) x| ≤ K * HRS.Whole.sobolevNorm Γ φ :=
      fun i x => hbd 1 hj i x
    have hcd1 : ContDiff ℝ 1 (propagatorW C 0 t φ) :=
      hcd.of_le (by exact_mod_cast hj)
    obtain ⟨hm, hn⟩ := sa27_cb1_of_partial hcd1 h0 h1
    exact ⟨hm, by simpa [mul_assoc] using hn, h0⟩
  · obtain ⟨-, -, hlin, -⟩ := h 0 t le_rfl ht.1 ht.2 φ hφ
    exact hlin φ₂ hφ₂ c

/-- `AdjointDerivInput` at order `j ≥ 1` gives the `C_b^1` adjoint input of S.B.2. -/
theorem sa27_fieldInput {Γ : ℝ} {j : ℕ} (hj : 1 ≤ j) {Cf : ℕ → WholeCoeff d} {T K : ℝ}
    (h : AdjointDerivInput Γ j Cf T K) : AdjointFieldInput Γ Cf T ((1 + d) * K) := by
  intro N hN t ht
  refine ⟨fun φ hφ => (h N hN 0 t le_rfl ht.1 ht.2 φ hφ).1, ?_, ?_⟩
  · intro φ₁ φ₂ hφ₁ hφ₂ c r hr
    obtain ⟨-, -, hlin, -⟩ := h N hN r t hr.1 hr.2 ht.2 φ₁ hφ₁
    exact hlin φ₂ hφ₂ c
  · intro φ hφ
    exact ⟨((sa27_psi_facts hj (h N hN) ht).1 φ hφ).1, ((sa27_psi_facts hj (h N hN) ht).1 φ hφ).2.1⟩

theorem sa27_cb_sup {j : ℕ} {f : Euc d → ℝ} (hf : MemCb j f) (x : Euc d) : |f x| ≤ cbNorm j f := by
  have h0 : BddAbove (Set.range fun z => ‖iteratedFDeriv ℝ 0 f z‖) := hf.2 0 (Nat.zero_le _)
  have h1 : ‖f x‖ ≤ ⨆ z, ‖iteratedFDeriv ℝ 0 f z‖ := by
    have := le_ciSup h0 x
    simpa using this
  unfold cbNorm
  have hnn : ∀ i ∈ Finset.range (j + 1), 0 ≤ ⨆ z : Euc d, ‖iteratedFDeriv ℝ i f z‖ := fun i _ =>
    Real.iSup_nonneg fun _ => norm_nonneg _
  have := Finset.single_le_sum hnn (Finset.mem_range.2 (Nat.succ_pos j))
  rw [← Real.norm_eq_abs]
  exact h1.trans this

/-- `‖F‖ₑ ^ 2` as the `ofReal` of the real square (junk-free). -/
theorem sa27_enorm_sq {E : Type*} [NormedAddCommGroup E] (F : E) :
    ‖F‖ₑ ^ 2 = ENNReal.ofReal (‖F‖ ^ 2) := by
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

/-- The pointwise bound on `A_N U_N^{0,t}φ - A U_∞^{0,t}φ` from the stability input. -/
theorem sa27_orbit_bound (S : WholeMainData d) (L : LimitCoeffsRd d) (q m m₀ : ℕ) (Kadj Kst : ℝ)
    (hAdjL : AdjointInputOneD (q : ℝ) (m₀ + 1) (L.coeff S) S.T Kadj)
    (hStab : AdjointStabilityInputRd S L q (m₀ + 1) m Kst)
    (N : ℕ) (hN : 1 ≤ N) (hΔ : coeffDiscrepancyRd S L m N ≠ ⊤) (hA1 : S.AN N ≤ 1) (hA0 : 0 ≤ S.AN N)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) S.T) (hj : 1 ≤ m₀ + 1) :
    ∀ φ, IsSobolevTest (q : ℝ) φ → ∀ x,
      |S.AN N * propagatorW (S.coeff N) 0 t φ x - L.A * propagatorW (L.coeff S) 0 t φ x| ≤
        ((max Kst 0 + max Kadj 0) * (coeffDiscrepancyRd S L m N).toReal) *
          HRS.Whole.sobolevNorm (q : ℝ) φ := by
  set Dr : ℝ := (coeffDiscrepancyRd S L m N).toReal with hDr
  have hDr0 : 0 ≤ Dr := ENNReal.toReal_nonneg
  obtain ⟨hf2, hl2⟩ := sa27_psi_facts hj hAdjL ht
  -- `|A_N - A| ≤ Δ_N`
  have hAΔ : |S.AN N - L.A| ≤ Dr := by
    have h1 : ENNReal.ofReal |S.AN N - L.A| ≤ coeffDiscrepancyRd S L m N := by
      unfold coeffDiscrepancyRd
      refine le_trans (ENNReal.ofReal_le_ofReal ?_) le_self_add
      have := abs_nonneg (S.invβ N - L.invβ)
      have := abs_nonneg (2 * S.qN N - 2 * L.invβstar)
      linarith
    exact (ENNReal.ofReal_le_iff_le_toReal hΔ).1 h1
  intro φ hφ x
  have hsn : 0 ≤ HRS.Whole.sobolevNorm (q : ℝ) φ := Real.sqrt_nonneg _
  obtain ⟨hmcb, hcb⟩ := (hStab N hN 0 t le_rfl ht.1 ht.2 φ hφ).2.2
  have hdiff : |propagatorW (S.coeff N) 0 t φ x - propagatorW (L.coeff S) 0 t φ x| ≤
      max Kst 0 * HRS.Whole.sobolevNorm (q : ℝ) φ * Dr := by
    have h1 := sa27_cb_sup hmcb x
    have h2 : ENNReal.ofReal (cbNorm (m₀ + 1) fun x => propagatorW (S.coeff N) 0 t φ x -
        propagatorW (L.coeff S) 0 t φ x) ≤
        ENNReal.ofReal (max Kst 0 * HRS.Whole.sobolevNorm (q : ℝ) φ * Dr) := by
      refine hcb.trans ?_
      calc ENNReal.ofReal (Kst * HRS.Whole.sobolevNorm (q : ℝ) φ) * coeffDiscrepancyRd S L m N
          ≤ ENNReal.ofReal (max Kst 0 * HRS.Whole.sobolevNorm (q : ℝ) φ) *
              coeffDiscrepancyRd S L m N :=
            mul_le_mul' (ENNReal.ofReal_le_ofReal
              (mul_le_mul_of_nonneg_right (le_max_left _ _) hsn)) le_rfl
        _ = ENNReal.ofReal (max Kst 0 * HRS.Whole.sobolevNorm (q : ℝ) φ * Dr) := by
            rw [ENNReal.ofReal_mul (mul_nonneg (le_max_right _ _) hsn), hDr,
              ENNReal.ofReal_toReal hΔ]
    have h3 := (ENNReal.ofReal_le_ofReal_iff
      (mul_nonneg (mul_nonneg (le_max_right _ _) hsn) hDr0)).1 h2
    exact h1.trans h3
  have hU : |propagatorW (L.coeff S) 0 t φ x| ≤ max Kadj 0 * HRS.Whole.sobolevNorm (q : ℝ) φ :=
    ((hf2 φ hφ).2.2 x).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hsn)
  calc |S.AN N * propagatorW (S.coeff N) 0 t φ x - L.A * propagatorW (L.coeff S) 0 t φ x|
      = |S.AN N * (propagatorW (S.coeff N) 0 t φ x - propagatorW (L.coeff S) 0 t φ x) +
          (S.AN N - L.A) * propagatorW (L.coeff S) 0 t φ x| := by ring_nf
    _ ≤ |S.AN N * (propagatorW (S.coeff N) 0 t φ x - propagatorW (L.coeff S) 0 t φ x)| +
          |(S.AN N - L.A) * propagatorW (L.coeff S) 0 t φ x| := abs_add_le _ _
    _ ≤ (max Kst 0 * HRS.Whole.sobolevNorm (q : ℝ) φ * Dr) +
          Dr * (max Kadj 0 * HRS.Whole.sobolevNorm (q : ℝ) φ) := by
        rw [abs_mul, abs_mul, abs_of_nonneg hA0]
        refine add_le_add ?_ (mul_le_mul hAΔ hU (abs_nonneg _) hDr0)
        calc S.AN N * |_| ≤ 1 * (max Kst 0 * HRS.Whole.sobolevNorm (q : ℝ) φ * Dr) :=
              mul_le_mul hA1 hdiff (abs_nonneg _) zero_le_one
          _ = _ := one_mul _
    _ = (max Kst 0 + max Kadj 0) * Dr * HRS.Whole.sobolevNorm (q : ℝ) φ := by ring

/-- The `L²` coupling at one time between the particle and the limiting transported fields. -/
theorem sa27_time_coupling (S : WholeMainData d) (L : LimitCoeffsRd d) (q m m₀ : ℕ) (Kadj Kst : ℝ)
    (hm₀ : 1 ≤ m₀) (hAdj : AdjointDerivInput (q : ℝ) (m₀ + 1) S.coeff S.T Kadj)
    (hAdjL : AdjointInputOneD (q : ℝ) (m₀ + 1) (L.coeff S) S.T Kadj)
    (hStab : AdjointStabilityInputRd S L q (m₀ + 1) m Kst)
    (N : ℕ) (hN : 1 ≤ N) (hΔ : coeffDiscrepancyRd S L m N ≠ ⊤) (hA1 : S.AN N ≤ 1) (hA0 : 0 ≤ S.AN N)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) S.T)
    {Ω' : Type*} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (η : Ω' → (Euc d → ℝ) → ℝ) (hη : IsGaussianBridgeW P' S.μ0 η)
    (Y J : Ω' → HNeg d (q : ℝ))
    (hY : ∀ φ, IsSobolevTest (q : ℝ) φ → ∀ᵐ ζ ∂P',
      HNeg.pairing φ (Y ζ) = S.AN N * η ζ (propagatorW (S.coeff N) 0 t φ))
    (hJ : ∀ φ, IsSobolevTest (q : ℝ) φ → ∀ᵐ ζ ∂P',
      HNeg.pairing φ (J ζ) = L.A * η ζ (propagatorW (L.coeff S) 0 t φ)) :
    ∫⁻ ζ, ‖Y ζ - J ζ‖ₑ ^ 2 ∂P' ≤
      ENNReal.ofReal (((max Kst 0 + max Kadj 0) * (coeffDiscrepancyRd S L m N).toReal) ^ 2) := by
  haveI := S.hμ0
  have hj : 1 ≤ m₀ + 1 := by omega
  obtain ⟨hf1, hl1⟩ := sa27_psi_facts hj (hAdj N hN) ht
  obtain ⟨hf2, hl2⟩ := sa27_psi_facts hj hAdjL ht
  exact sa27_coupling (Γ := (q : ℝ)) S.μ0 (S.AN N) L.A
    ((max Kst 0 + max Kadj 0) * (coeffDiscrepancyRd S L m N).toReal)
    (mul_nonneg (add_nonneg (le_max_right _ _) (le_max_right _ _)) ENNReal.toReal_nonneg)
    (propagatorW (S.coeff N) 0 t) (propagatorW (L.coeff S) 0 t)
    (fun φ hφ => (hf1 φ hφ).1) (fun φ hφ => (hf2 φ hφ).1) hl1 hl2
    (sa27_orbit_bound S L q m m₀ Kadj Kst hAdjL hStab N hN hΔ hA1 hA0 ht hj)
    P' η hη.1 hη.2 Y J hY hJ

end HRS.MS.IidInit
