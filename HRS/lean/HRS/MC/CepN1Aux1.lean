import Mathlib.Probability.BrownianMotion.Basic
import Mathlib.Probability.Martingale.OptionalStopping
import Mathlib.Probability.ConditionalExpectation

/-!
# Packet CEPN1, part 1: Kolmogorov (Doob) maximal inequality for pre-Brownian motion
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal

noncomputable section

namespace HRS.MC.CepN1

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- second moment of a centered Gaussian -/
theorem cepn1_integral_sq_gaussian (v : ℝ≥0) : ∫ x, x ^ 2 ∂gaussianReal 0 v = v := by
  have h := variance_fun_id_gaussianReal (μ := 0) (v := v)
  rw [variance_eq_integral (by fun_prop)] at h
  simpa [integral_id_gaussianReal] using h

theorem cepn1_integral_sq {Z : ℝ≥0 → Ω → ℝ} (hZ : IsPreBrownianReal Z P) (t : ℝ≥0) :
    ∫ ω, (Z t ω) ^ 2 ∂P = t := by
  have := (hZ.hasLaw_eval t).integral_comp (f := fun x : ℝ => x ^ 2) (by fun_prop)
  have h2 := cepn1_integral_sq_gaussian t
  simp only [Function.comp_def] at this
  rw [← h2, ← this]

theorem cepn1_memLp_two {Z : ℝ≥0 → Ω → ℝ} (hZ : IsPreBrownianReal Z P) (t : ℝ≥0) :
    MemLp (Z t) 2 P := (hZ.isGaussianProcess.hasGaussianLaw_eval t).memLp_two


/-- The natural filtration of a measurable process along a monotone time sequence. -/
def cepn1_filt {Z : ℝ≥0 → Ω → ℝ} (hm : ∀ t, Measurable (Z t)) (τ : ℕ → ℝ≥0) (hτ : Monotone τ) :
    Filtration ℕ mΩ where
  seq k := MeasurableSpace.comap (fun ω (u : Set.Iic (τ k)) => Z u ω) inferInstance
  mono' k l hkl := by
    rintro s ⟨S, hS, rfl⟩
    refine ⟨(fun g : Set.Iic (τ l) → ℝ => fun u : Set.Iic (τ k) => g ⟨u, (u.2.trans (hτ hkl))⟩) ⁻¹' S,
      ?_, rfl⟩
    exact (measurable_pi_iff.2 fun u => measurable_pi_apply _) hS
  le' k := (measurable_pi_iff.2 fun u : Set.Iic (τ k) => hm u).comap_le

theorem cepn1_filt_meas {Z : ℝ≥0 → Ω → ℝ} (hm : ∀ t, Measurable (Z t)) (τ : ℕ → ℝ≥0)
    (hτ : Monotone τ) (k : ℕ) :
    Measurable[(cepn1_filt hm τ hτ) k] (Z (τ k)) := by
  have h1 : Measurable[(cepn1_filt hm τ hτ) k]
      (fun ω (u : Set.Iic (τ k)) => Z u ω) := comap_measurable _
  exact (measurable_pi_apply (⟨τ k, Set.mem_Iic.2 le_rfl⟩ : Set.Iic (τ k))).comp h1


theorem cepn1_indep_incr [IsProbabilityMeasure P] {Z : ℝ≥0 → Ω → ℝ} (hZ : IsPreBrownianReal Z P)
    (hm : ∀ t, Measurable (Z t)) (τ : ℕ → ℝ≥0) (hτ : Monotone τ) (k : ℕ) :
    Indep (MeasurableSpace.comap (fun ω => Z (τ (k + 1)) ω - Z (τ k) ω) inferInstance)
      ((cepn1_filt hm τ hτ) k) P := by
  have h := hZ.indepFun_shift (τ k)
  have hφ : Measurable (fun g : ℝ≥0 → ℝ => g (τ (k + 1) - τ k)) :=
    measurable_pi_apply (τ (k + 1) - τ k)
  have h2 := h.comp (γ := ℝ) (γ' := Set.Iic (τ k) → ℝ) hφ (measurable_id (α := Set.Iic (τ k) → ℝ))
  have e : τ k + (τ (k + 1) - τ k) = τ (k + 1) := add_tsub_cancel_of_le (hτ (Nat.le_succ k))
  have e2 : ((fun g : ℝ≥0 → ℝ => g (τ (k + 1) - τ k)) ∘ fun ω t => Z (τ k + t) ω - Z (τ k) ω) =
      fun ω => Z (τ (k + 1)) ω - Z (τ k) ω := by
    funext ω; simp [e]
  rw [e2] at h2
  exact h2


theorem cepn1_submart [IsProbabilityMeasure P] {Z : ℝ≥0 → Ω → ℝ} (hZ : IsPreBrownianReal Z P)
    (hm : ∀ t, Measurable (Z t)) (τ : ℕ → ℝ≥0) (hτ : Monotone τ) :
    Submartingale (fun k ω => (Z (τ k) ω) ^ 2) (cepn1_filt hm τ hτ) P := by
  have hint : ∀ k, Integrable (fun ω => (Z (τ k) ω) ^ 2) P :=
    fun k => (cepn1_memLp_two hZ _).integrable_sq
  refine submartingale_nat ?_ hint ?_
  · intro k
    exact ((cepn1_filt_meas hm τ hτ k).pow_const 2).stronglyMeasurable
  · intro k
    set ℱ := cepn1_filt hm τ hτ with hℱ
    have hle : ℱ k ≤ mΩ := ℱ.le k
    have hXm : StronglyMeasurable[ℱ k] (Z (τ k)) := (cepn1_filt_meas hm τ hτ k).stronglyMeasurable
    have hX2 := cepn1_memLp_two hZ (τ k)
    have hY2 := cepn1_memLp_two hZ (τ (k + 1))
    have hD2 : MemLp (fun ω => Z (τ (k + 1)) ω - Z (τ k) ω) 2 P := hY2.sub hX2
    have hDint : Integrable (fun ω => Z (τ (k + 1)) ω - Z (τ k) ω) P := hD2.integrable one_le_two
    have hXD : Integrable (fun ω => Z (τ k) ω * (Z (τ (k + 1)) ω - Z (τ k) ω)) P :=
      hX2.integrable_mul hD2
    have hX2i : Integrable (fun ω => (Z (τ k) ω) ^ 2) P := hint k
    -- conditional expectation of the increment vanishes
    have hDc : P[fun ω => Z (τ (k + 1)) ω - Z (τ k) ω | ℱ k] =ᵐ[P] fun _ => (0 : ℝ) := by
      have h1 := condExp_indep_eq (m₁ := MeasurableSpace.comap
        (fun ω => Z (τ (k + 1)) ω - Z (τ k) ω) inferInstance) (m₂ := ℱ k)
        (Measurable.comap_le (hm (τ (k + 1)) |>.sub (hm (τ k)))) hle
        (comap_measurable _ |>.stronglyMeasurable) (cepn1_indep_incr hZ hm τ hτ k)
      have h0 : P[fun ω => Z (τ (k + 1)) ω - Z (τ k) ω] = 0 := by
        rw [integral_sub (hY2.integrable one_le_two) (hX2.integrable one_le_two),
          hZ.integral_eval, hZ.integral_eval, sub_zero]
      simpa [h0] using h1
    have hlow : (fun ω => (Z (τ k) ω) ^ 2 + 2 * (Z (τ k) ω * (Z (τ (k + 1)) ω - Z (τ k) ω))) ≤ᵐ[P]
        fun ω => (Z (τ (k + 1)) ω) ^ 2 := by
      refine Filter.Eventually.of_forall fun ω => ?_
      simp only
      nlinarith [sq_nonneg (Z (τ (k + 1)) ω - Z (τ k) ω)]
    have hmono := condExp_mono (m := ℱ k) (hX2i.add (hXD.const_mul 2)) (hint (k + 1)) hlow
    have hadd := condExp_add (m := ℱ k) hX2i (hXD.const_mul 2)
    have hsm : P[fun ω => (2 : ℝ) * (Z (τ k) ω * (Z (τ (k + 1)) ω - Z (τ k) ω)) | ℱ k]
        =ᵐ[P] fun _ => (0 : ℝ) := by
      have h1 := condExp_smul (μ := P) (2 : ℝ)
        (fun ω => Z (τ k) ω * (Z (τ (k + 1)) ω - Z (τ k) ω)) (ℱ k)
      have h2 := condExp_mul_of_stronglyMeasurable_left (μ := P) hXm hXD hDint
      have e : (fun ω => (2 : ℝ) * (Z (τ k) ω * (Z (τ (k + 1)) ω - Z (τ k) ω))) =
          (2 : ℝ) • (fun ω => Z (τ k) ω * (Z (τ (k + 1)) ω - Z (τ k) ω)) := by
        funext ω; simp
      rw [e]
      filter_upwards [h1, h2, hDc] with ω a b c
      rw [a]
      have b' : P[fun ω => Z (τ k) ω * (Z (τ (k + 1)) ω - Z (τ k) ω) | ℱ k] ω =
          Z (τ k) ω * P[fun ω => Z (τ (k + 1)) ω - Z (τ k) ω | ℱ k] ω := b
      show (2 : ℝ) * _ = 0
      rw [b', c]; simp
    have hself : P[fun ω => (Z (τ k) ω) ^ 2 | ℱ k] = fun ω => (Z (τ k) ω) ^ 2 :=
      condExp_of_stronglyMeasurable hle (hXm.pow 2) hX2i
    filter_upwards [hmono, hadd, hsm] with ω a b c
    rw [hself] at b
    try simp only [Pi.add_apply] at b
    linarith [b, c]


theorem cepn1_max_meas [IsProbabilityMeasure P] {Z : ℝ≥0 → Ω → ℝ} (hZ : IsPreBrownianReal Z P)
    (hm : ∀ t, Measurable (Z t)) (τ : ℕ → ℝ≥0) (hτ : Monotone τ) {ρ : ℝ} (hρ : 0 < ρ) (n : ℕ) :
    ENNReal.ofReal (ρ ^ 2) * P {ω | ∃ k ≤ n, ρ < |Z (τ k) ω|} ≤ ENNReal.ofReal (τ n) := by
  have hsub := cepn1_submart hZ hm τ hτ
  have hnn : (0 : ℕ → Ω → ℝ) ≤ fun k ω => (Z (τ k) ω) ^ 2 := fun k ω => sq_nonneg _
  have key := maximal_ineq hsub hnn (ε := (ρ ^ 2).toNNReal) n
  have hε : (((ρ ^ 2).toNNReal : ℝ≥0) : ℝ) = ρ ^ 2 := Real.coe_toNNReal _ (sq_nonneg _)
  rw [hε] at key
  have hsubset : {ω | ∃ k ≤ n, ρ < |Z (τ k) ω|} ⊆
      {ω | ρ ^ 2 ≤ (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
        fun k => (Z (τ k) ω) ^ 2} := by
    rintro ω ⟨k, hk, hk2⟩
    have h1 : ρ ^ 2 ≤ (Z (τ k) ω) ^ 2 := by
      have := abs_nonneg (Z (τ k) ω)
      nlinarith [sq_abs (Z (τ k) ω)]
    exact h1.trans (Finset.le_sup' (fun k => (Z (τ k) ω) ^ 2) (Finset.mem_range.2 (Nat.lt_succ_of_le hk)))
  calc ENNReal.ofReal (ρ ^ 2) * P {ω | ∃ k ≤ n, ρ < |Z (τ k) ω|}
      ≤ ((ρ ^ 2).toNNReal : ℝ≥0∞) * P {ω | ρ ^ 2 ≤ (Finset.range (n + 1)).sup'
          Finset.nonempty_range_add_one fun k => (Z (τ k) ω) ^ 2} := by
        exact mul_le_mul' le_rfl (measure_mono hsubset)
    _ ≤ _ := key
    _ ≤ ENNReal.ofReal (∫ ω, (Z (τ n) ω) ^ 2 ∂P) := by
        apply ENNReal.ofReal_le_ofReal
        exact setIntegral_le_integral ((cepn1_memLp_two hZ _).integrable_sq)
          (Filter.Eventually.of_forall fun ω => sq_nonneg _)
    _ = ENNReal.ofReal (τ n) := by rw [cepn1_integral_sq hZ]

/-- **Kolmogorov / Doob maximal inequality for pre-Brownian motion** along a monotone time sequence. -/
theorem cepn1_max [IsProbabilityMeasure P] {Z : ℝ≥0 → Ω → ℝ} (hZ : IsPreBrownianReal Z P)
    (τ : ℕ → ℝ≥0) (hτ : Monotone τ) {ρ : ℝ} (hρ : 0 < ρ) (n : ℕ) :
    ENNReal.ofReal (ρ ^ 2) * P {ω | ∃ k ≤ n, ρ < |Z (τ k) ω|} ≤ ENNReal.ofReal (τ n) := by
  set Z' : ℝ≥0 → Ω → ℝ := fun t => (hZ.aemeasurable t).mk (Z t) with hZ'
  have hae : ∀ t, Z t =ᵐ[P] Z' t := fun t => (hZ.aemeasurable t).ae_eq_mk
  have hZp : IsPreBrownianReal Z' P := hZ.congr hae
  have hm : ∀ t, Measurable (Z' t) := fun t => (hZ.aemeasurable t).measurable_mk
  refine le_trans ?_ (cepn1_max_meas hZp hm τ hτ hρ n)
  refine mul_le_mul' le_rfl (measure_mono_ae ?_)
  have : ∀ᵐ ω ∂P, ∀ k : ℕ, Z (τ k) ω = Z' (τ k) ω := ae_all_iff.2 fun k => hae _
  filter_upwards [this] with ω hω
  rintro ⟨k, hk, hk2⟩
  exact ⟨k, hk, by rwa [← hω k]⟩

end HRS.MC.CepN1
