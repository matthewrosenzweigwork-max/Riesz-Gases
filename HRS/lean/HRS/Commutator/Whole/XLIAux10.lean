import HRS.Commutator.Whole.XLIAux9

/-!
# X-LI part 10: uniform decay of kernels of symbols and scale-dependent dyadic kernel families
-/

open MeasureTheory Metric Set Filter
open scoped ENNReal NNReal FourierTransform ContDiff Convolution Topology SchwartzMap

noncomputable section

namespace HRS.Commutator.Whole.XLI

open HRS.Commutator.Whole

variable {d : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin d)

/-- uniform decay of the inverse Fourier transform of a smooth symbol supported in `B̄(0,R)` with
uniformly bounded derivatives of order `≤ n` -/
lemma decay_fourierInv_unif (R : ℝ) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (θ : 𝔼 → ℂ), ContDiff ℝ ∞ θ → (∀ η : 𝔼, R < ‖η‖ → θ η = 0) →
      ∀ B : ℝ, 0 ≤ B → (∀ i ≤ n, ∀ η, ‖iteratedFDeriv ℝ i θ η‖ ≤ B) → ∀ y : 𝔼,
        ‖y‖ ^ n * ‖𝓕⁻ θ y‖ ≤ C * B := by
  set V : ℝ := (volume (closedBall (0 : 𝔼) R)).toReal with hV
  have hV0 : 0 ≤ V := ENNReal.toReal_nonneg
  refine ⟨(2 * (n : ℝ) + 2) ^ n * ((n + 1 : ℝ) * V), by positivity, ?_⟩
  intro θ hθ hs B hB0 hB y
  have hcs : HasCompactSupport θ := by
    refine HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : 𝔼) R) ?_
    intro η hη
    by_contra h
    exact hη (hs η (by simpa using h))
  have hint : ∀ i : ℕ, Integrable (fun v : 𝔼 => ‖v‖ ^ 0 * ‖iteratedFDeriv ℝ i θ v‖) := by
    intro i
    have h1 : Continuous (fun v : 𝔼 => ‖iteratedFDeriv ℝ i θ v‖) :=
      (hθ.continuous_iteratedFDeriv (by exact_mod_cast le_top)).norm
    have h2 : HasCompactSupport (fun v : 𝔼 => ‖iteratedFDeriv ℝ i θ v‖) :=
      (hcs.iteratedFDeriv i).norm
    simpa using h1.integrable_of_hasCompactSupport h2
  have key := Real.pow_mul_norm_iteratedFDeriv_fourier_le (K := 0) (N := ⊤) (f := θ) (k := 0)
    (n := n) hθ (fun k m hk _ => by
      have : k = 0 := by simpa using hk
      subst this
      exact hint m) le_rfl le_top (-y)
  have hts : tsupport θ ⊆ closedBall (0 : 𝔼) R := by
    refine closure_minimal ?_ isClosed_closedBall
    intro η hη
    by_contra h
    exact hη (hs η (by simpa using h))
  have hbd : ∀ i ≤ n, ∫ v : 𝔼, ‖v‖ ^ 0 * ‖iteratedFDeriv ℝ i θ v‖ ≤ B * V := by
    intro i hi
    have hpt : ∀ v : 𝔼, ‖v‖ ^ 0 * ‖iteratedFDeriv ℝ i θ v‖ ≤
        (closedBall (0 : 𝔼) R).indicator (fun _ => B) v := by
      intro v
      by_cases hv : v ∈ closedBall (0 : 𝔼) R
      · rw [Set.indicator_of_mem hv]; simpa using hB i hi v
      · rw [Set.indicator_of_notMem hv]
        have : iteratedFDeriv ℝ i θ v = 0 := by
          by_contra h0
          exact hv (hts (tsupport_iteratedFDeriv_subset (𝕜 := ℝ) i (subset_closure h0)))
        simp [this]
    have hind : Integrable ((closedBall (0 : 𝔼) R).indicator (fun _ => B)) :=
      (integrable_indicator_iff measurableSet_closedBall).2
        (integrableOn_const measure_closedBall_lt_top.ne)
    calc _ ≤ ∫ v : 𝔼, (closedBall (0 : 𝔼) R).indicator (fun _ => B) v :=
          integral_mono (hint i) hind hpt
      _ = _ := by
          rw [integral_indicator_const _ measurableSet_closedBall]
          simp [Measure.real, mul_comm, hV]
  rw [Real.fourierInv_eq_fourier_neg]
  simp only [norm_neg, norm_iteratedFDeriv_zero] at key ⊢
  refine key.trans ?_
  have hsum : ∑ p ∈ Finset.range (0 + 1) ×ˢ Finset.range (n + 1),
      ∫ v : 𝔼, ‖v‖ ^ p.1 * ‖iteratedFDeriv ℝ p.2 θ v‖ =
      ∑ i ∈ Finset.range (n + 1), ∫ v : 𝔼, ‖v‖ ^ 0 * ‖iteratedFDeriv ℝ i θ v‖ := by
    simp only [zero_add, Finset.range_one]
    rw [Finset.singleton_product, Finset.sum_map]
    rfl
  have h2 : ((2:ℝ) * ((0:ℕ):ℝ) + 2) ^ n ≤ (2 * (n : ℝ) + 2) ^ n := by
    gcongr; simp
  rw [hsum, pow_zero, one_mul]
  have hsum2 : ∑ i ∈ Finset.range (n + 1), ∫ v : 𝔼, ‖v‖ ^ 0 * ‖iteratedFDeriv ℝ i θ v‖
      ≤ (n + 1 : ℝ) * (B * V) := by
    calc _ ≤ ∑ i ∈ Finset.range (n + 1), (B * V) := by
          refine Finset.sum_le_sum fun i hi => hbd i (by simpa [Nat.lt_succ_iff] using hi)
      _ = (n + 1 : ℝ) * (B * V) := by simp
  have hnn : 0 ≤ ∑ i ∈ Finset.range (n + 1), ∫ v : 𝔼, ‖v‖ ^ 0 * ‖iteratedFDeriv ℝ i θ v‖ :=
    Finset.sum_nonneg fun i _ => integral_nonneg fun v => by positivity
  calc ((2:ℝ) * ((0:ℕ):ℝ) + 2) ^ n * ∑ i ∈ Finset.range (n + 1),
        ∫ v : 𝔼, ‖v‖ ^ 0 * ‖iteratedFDeriv ℝ i θ v‖
      ≤ (2 * (n : ℝ) + 2) ^ n * ∑ i ∈ Finset.range (n + 1),
        ∫ v : 𝔼, ‖v‖ ^ 0 * ‖iteratedFDeriv ℝ i θ v‖ := mul_le_mul_of_nonneg_right h2 hnn
    _ ≤ (2 * (n : ℝ) + 2) ^ n * ((n + 1 : ℝ) * (B * V)) := by gcongr
    _ = (2 * (n : ℝ) + 2) ^ n * ((n + 1 : ℝ) * V) * B := by ring

/-- decay in the form `|𝓕⁻θ(y)| (1+|y|)^{d+1} ≤ C B` -/
lemma decay_dec_unif (R : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (θ : 𝔼 → ℂ), ContDiff ℝ ∞ θ → (∀ η : 𝔼, R < ‖η‖ → θ η = 0) →
      ∀ B : ℝ, 0 ≤ B → (∀ i ≤ d + 1, ∀ η, ‖iteratedFDeriv ℝ i θ η‖ ≤ B) → ∀ y : 𝔼,
        ‖𝓕⁻ θ y‖ * (1 + ‖y‖) ^ (d + 1) ≤ C * B := by
  obtain ⟨C0, hC0, h0⟩ := decay_fourierInv_unif (d := d) R 0
  obtain ⟨C1, hC1, h1⟩ := decay_fourierInv_unif (d := d) R (d + 1)
  refine ⟨2 ^ (d + 1) * (C0 + C1), by positivity, ?_⟩
  intro θ hθ hs B hB0 hB y
  have e0 := h0 θ hθ hs B hB0 (fun i hi η => hB i (by omega) η) y
  have e1 := h1 θ hθ hs B hB0 hB y
  simp only [pow_zero, one_mul] at e0
  have hb : (1 + ‖y‖) ^ (d + 1) ≤ 2 ^ (d + 1) * (1 + ‖y‖ ^ (d + 1)) := by
    rcases le_total ‖y‖ 1 with h | h
    · have : (1 + ‖y‖) ^ (d + 1) ≤ 2 ^ (d + 1) := pow_le_pow_left₀ (by positivity) (by linarith) _
      nlinarith [pow_nonneg (norm_nonneg y) (d + 1), pow_pos (by norm_num : (0:ℝ) < 2) (d + 1)]
    · have : (1 + ‖y‖) ^ (d + 1) ≤ (2 * ‖y‖) ^ (d + 1) := pow_le_pow_left₀ (by positivity) (by linarith) _
      rw [mul_pow] at this
      nlinarith [pow_pos (by norm_num : (0:ℝ) < 2) (d + 1)]
  calc ‖𝓕⁻ θ y‖ * (1 + ‖y‖) ^ (d + 1) ≤ ‖𝓕⁻ θ y‖ * (2 ^ (d + 1) * (1 + ‖y‖ ^ (d + 1))) := by gcongr
    _ = 2 ^ (d + 1) * (‖𝓕⁻ θ y‖ + ‖y‖ ^ (d + 1) * ‖𝓕⁻ θ y‖) := by ring
    _ ≤ 2 ^ (d + 1) * (C0 * B + C1 * B) := by gcongr
    _ = _ := by ring

/-- the dyadic kernel with scale-dependent symbol profile `Θ j`: symbol `Θ j (2^{-j} ·)` -/
def dK (Θ : ℤ → 𝔼 → ℂ) (j : ℤ) : 𝔼 → ℂ := 𝓕⁻ (fun ξ => Θ j (((2 : ℝ) ^ j)⁻¹ • ξ))

lemma dK_eq_symK (Θ : ℤ → 𝔼 → ℂ) (j : ℤ) : dK Θ j = symK (Θ j) j := rfl

/-- a family of symbol profiles supported in `B̄(0,R)` with uniformly bounded derivatives -/
structure SymFam (R : ℝ) (Θ : ℤ → 𝔼 → ℂ) : Prop where
  smooth : ∀ j, ContDiff ℝ ∞ (Θ j)
  supp : ∀ j (η : 𝔼), R < ‖η‖ → Θ j η = 0
  bdd : ∃ B : ℝ, 0 ≤ B ∧ ∀ j, ∀ i ≤ d + 1, ∀ η, ‖iteratedFDeriv ℝ i (Θ j) η‖ ≤ B

lemma SymFam.cs {R : ℝ} {Θ : ℤ → 𝔼 → ℂ} (h : SymFam R Θ) (j : ℤ) : HasCompactSupport (Θ j) := by
  refine HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : 𝔼) R) ?_
  intro η hη
  by_contra hc
  exact hη (h.supp j η (by simpa using hc))

lemma dK_continuous {R : ℝ} {Θ : ℤ → 𝔼 → ℂ} (h : SymFam R Θ) (j : ℤ) : Continuous (dK Θ j) :=
  symK_continuous (h.smooth j) (h.cs j) j

lemma dK_integrable {R : ℝ} {Θ : ℤ → 𝔼 → ℂ} (h : SymFam R Θ) (j : ℤ) : Integrable (dK Θ j) :=
  symK_integrable (h.smooth j) (h.cs j) j

lemma dK_fourier {R : ℝ} {Θ : ℤ → 𝔼 → ℂ} (h : SymFam R Θ) (j : ℤ) (ξ : 𝔼) :
    𝓕 (dK Θ j) ξ = Θ j (((2 : ℝ) ^ j)⁻¹ • ξ) :=
  symK_fourier (h.smooth j) (h.cs j) j ξ

lemma dK_dec {R : ℝ} {Θ : ℤ → 𝔼 → ℂ} (h : SymFam R Θ) :
    ∃ A : ℝ≥0∞, A ≠ ⊤ ∧ ∀ j, DecK A j (dK Θ j) := by
  obtain ⟨C, hC0, hC⟩ := decay_dec_unif (d := d) R
  obtain ⟨B, hB0, hB⟩ := h.bdd
  refine ⟨ENNReal.ofReal (C * B), ENNReal.ofReal_ne_top, fun j x => ?_⟩
  have hM := hC (Θ j) (h.smooth j) (h.supp j) B hB0 (hB j)
  have hs0 : 0 < (2 : ℝ) ^ j := zpow_pos (by norm_num) j
  have hn : ‖((2 : ℝ) ^ j) • x‖ = (2 : ℝ) ^ j * ‖x‖ := by
    rw [norm_smul, Real.norm_of_nonneg hs0.le]
  have h1 := hM (((2 : ℝ) ^ j) • x)
  rw [hn] at h1
  have hpos : 0 < (1 + (2 : ℝ) ^ j * ‖x‖) ^ (d + 1) := by positivity
  have h2 : ‖𝓕⁻ (Θ j) (((2 : ℝ) ^ j) • x)‖ ≤ C * B * ((1 + (2 : ℝ) ^ j * ‖x‖) ^ (d + 1))⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ hpos]; exact h1
  have h3 : ‖dK Θ j x‖ ≤ (C * B) * (((2 : ℝ) ^ j) ^ d * ((1 + (2 : ℝ) ^ j * ‖x‖) ^ (d + 1))⁻¹) := by
    show ‖symK (Θ j) j x‖ ≤ _
    rw [symK_eq, norm_smul, Real.norm_of_nonneg (by positivity)]
    calc ((2 : ℝ) ^ j) ^ d * ‖𝓕⁻ (Θ j) (((2 : ℝ) ^ j) • x)‖
        ≤ ((2 : ℝ) ^ j) ^ d * (C * B * ((1 + (2 : ℝ) ^ j * ‖x‖) ^ (d + 1))⁻¹) := by gcongr
      _ = _ := by ring
  rw [← ofReal_norm]
  unfold Phi
  rw [← ENNReal.ofReal_mul (mul_nonneg hC0 hB0)]
  exact ENNReal.ofReal_le_ofReal h3

/-- orthogonality for a family of kernels with scale-dependent symbol profiles -/
lemma dK_orth {R : ℝ} {Θ : ℤ → 𝔼 → ℂ} (h : SymFam R Θ) {A : ℝ≥0∞}
    (hA : A ≠ ⊤) (hdec : ∀ j, DecK A j (dK Θ j)) {M : ℝ≥0∞}
    (hM : ∀ ξ : 𝔼, ∑' j : ℤ, ‖Θ j (((2 : ℝ) ^ j)⁻¹ • ξ)‖ₑ ^ 2 ≤ M) :
    ∀ u : 𝔼 → ℂ, Measurable u → Integrable u → ∫⁻ x, ‖u x‖ₑ ^ 2 < ⊤ →
      ∑' j, ∫⁻ x, ‖cv (dK Θ j) u x‖ₑ ^ 2 ≤ M * ∫⁻ x, ‖u x‖ₑ ^ 2 := by
  intro u hu hui hufin
  have hu2 : MemLp u 2 volume := memLp_two_of_lintegral hu.aestronglyMeasurable hufin
  have hKm : ∀ j, Measurable (dK Θ j) := fun j => (dK_continuous h j).measurable
  have hFu : Continuous (𝓕 u) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (by exact continuous_inner) hui
  have hpl : ∀ j, ∫⁻ x, ‖cv (dK Θ j) u x‖ₑ ^ 2 =
      ∫⁻ ξ, ‖Θ j (((2 : ℝ) ^ j)⁻¹ • ξ)‖ₑ ^ 2 * ‖𝓕 u ξ‖ₑ ^ 2 := by
    intro j
    have hvm : Measurable (cv (dK Θ j) u) := measurable_cv (hKm j) hu
    have hvint : Integrable (cv (dK Θ j) u) :=
      Integrable.integrable_convolution (ContinuousLinearMap.mul ℂ ℂ) (dK_integrable h j) hui
    have hv2 : MemLp (cv (dK Θ j) u) 2 volume := by
      refine memLp_two_of_lintegral hvm.aestronglyMeasurable ?_
      refine lt_of_le_of_lt (lintegral_cv_sq_le (hdec j) (hKm j) hu) ?_
      exact ENNReal.mul_lt_top (ENNReal.mul_lt_top (ENNReal.mul_lt_top hA.lt_top KP_ne_top.lt_top)
        (ENNReal.mul_lt_top hA.lt_top KP_ne_top.lt_top)) hufin
    rw [← plancherel_L1L2 hvint hv2]
    refine lintegral_congr fun ξ => ?_
    have := Real.fourier_mul_convolution_eq (dK_integrable h j) hui ξ
    rw [show cv (dK Θ j) u = (dK Θ j ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] u) from rfl, this,
      dK_fourier h, enorm_mul, mul_pow]
  calc ∑' j : ℤ, ∫⁻ x, ‖cv (dK Θ j) u x‖ₑ ^ 2
      = ∑' j : ℤ, ∫⁻ ξ, ‖Θ j (((2 : ℝ) ^ j)⁻¹ • ξ)‖ₑ ^ 2 * ‖𝓕 u ξ‖ₑ ^ 2 := tsum_congr hpl
    _ = ∫⁻ ξ, ∑' j : ℤ, ‖Θ j (((2 : ℝ) ^ j)⁻¹ • ξ)‖ₑ ^ 2 * ‖𝓕 u ξ‖ₑ ^ 2 := by
        rw [lintegral_tsum]
        intro j
        exact ((((h.smooth j).continuous.comp (continuous_const_smul _)).measurable.enorm.pow_const 2).mul
          (hFu.measurable.enorm.pow_const 2)).aemeasurable
    _ ≤ ∫⁻ ξ, M * ‖𝓕 u ξ‖ₑ ^ 2 := by
        refine lintegral_mono fun ξ => ?_
        rw [ENNReal.tsum_mul_right]
        exact mul_le_mul_left (hM ξ) _
    _ = M * ∫⁻ ξ, ‖𝓕 u ξ‖ₑ ^ 2 := lintegral_const_mul _ (hFu.measurable.enorm.pow_const 2)
    _ = M * ∫⁻ x, ‖u x‖ₑ ^ 2 := by rw [plancherel_L1L2 hui hu2]

/-- a reproducing family from scale-dependent profiles `Θ` and a reproducing partner `Θ'` -/
lemma isLPRep_dK {R R' : ℝ} {Θ Θ' : ℤ → 𝔼 → ℂ} (h : SymFam R Θ) (h' : SymFam R' Θ')
    (hrep : ∀ j ξ, Θ' j ξ * Θ j ξ = Θ j ξ)
    {M : ℝ≥0∞} (hM : M ≠ ⊤)
    (hsum : ∀ ξ : 𝔼, ∑' j : ℤ, ‖Θ j (((2 : ℝ) ^ j)⁻¹ • ξ)‖ₑ ^ 2 ≤ M) :
    IsLPRep (fun j => dK Θ j) := by
  obtain ⟨A, hA, hdec⟩ := dK_dec h
  obtain ⟨A', hA', hdec'⟩ := dK_dec h'
  refine ⟨⟨fun j => (dK_continuous h j).measurable, ⟨A, hA, hdec⟩,
    ⟨M, hM, dK_orth h hA hdec hsum⟩⟩, ?_⟩
  refine ⟨fun j => dK Θ' j, A', hA', hdec', fun j => (dK_continuous h' j).measurable, ?_⟩
  intro F hF B hB hFB j x
  have hBr : ∀ x, ‖F x‖ ≤ B.toReal := fun x => by
    have := hFB x
    rw [← ofReal_norm] at this
    exact (ENNReal.ofReal_le_iff_le_toReal hB).1 this
  exact symK_rep (h.smooth j) (h.cs j) (h'.smooth j) (h'.cs j) (hrep j) hF hBr j x

end HRS.Commutator.Whole.XLI
