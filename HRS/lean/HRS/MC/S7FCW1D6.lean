import HRS.Prob.Metrics

/-!
# `W_q` interpolation (FC-D6)

Proof file for `s7_FC_D6_interp` of `HRS/MC/S7FCPlan.lean`.  Uses only `HRS/Prob/Metrics.lean`.
Helpers carry the prefix `S7FCW1_`.

Key point: `c a ^ q` for an arbitrary (possibly non-measurable) `c` satisfies the Lyapunov inequality
`∫⁻ c^q ≤ (∫⁻ c)^θ (∫⁻ c^p)^{1-θ}` with `q = θ + (1-θ) p`; the proof passes to a measurable minorant
of `c^q` (`exists_measurable_le_lintegral_eq`) and applies Hölder to its roots.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

open HRS

namespace HRS.MC.Sec7.S7FCW1

/-- Lyapunov interpolation for lower integrals of arbitrary functions. -/
theorem S7FCW1_lyapunov {α : Type*} [MeasurableSpace α] (ρ : Measure α) {q p θ : ℝ}
    (hq : 0 < q) (hp : 0 < p) (hθ0 : 0 < θ) (hθ1 : θ < 1) (hqp : θ + (1 - θ) * p = q)
    (c : α → ℝ≥0∞) :
    ∫⁻ a, c a ^ q ∂ρ ≤ (∫⁻ a, c a ∂ρ) ^ θ * (∫⁻ a, c a ^ p ∂ρ) ^ (1 - θ) := by
  obtain ⟨g, hgm, hgc, hint⟩ := exists_measurable_le_lintegral_eq ρ (fun a => c a ^ q)
  set A : α → ℝ≥0∞ := fun a => g a ^ (1 / q) with hA
  set B' : α → ℝ≥0∞ := fun a => g a ^ (p / q) with hB
  have hAm : Measurable A := hgm.pow_const _
  have hBm : Measurable B' := hgm.pow_const _
  have hAc : ∀ a, A a ≤ c a := fun a => by
    calc g a ^ (1 / q) ≤ (c a ^ q) ^ (1 / q) := ENNReal.rpow_le_rpow (hgc a) (by positivity)
      _ = c a := by rw [← ENNReal.rpow_mul, mul_one_div_cancel hq.ne', ENNReal.rpow_one]
  have hBc : ∀ a, B' a ≤ c a ^ p := fun a => by
    calc g a ^ (p / q) ≤ (c a ^ q) ^ (p / q) := ENNReal.rpow_le_rpow (hgc a) (by positivity)
      _ = c a ^ p := by
          rw [← ENNReal.rpow_mul]
          congr 1
          field_simp
  have hsplit : ∀ a, g a = A a ^ θ * B' a ^ (1 - θ) := fun a => by
    simp only [hA, hB]
    rw [← ENNReal.rpow_mul, ← ENNReal.rpow_mul,
      ← ENNReal.rpow_add_of_nonneg (1 / q * θ) (p / q * (1 - θ))
        (mul_nonneg (by positivity) hθ0.le) (mul_nonneg (div_nonneg hp.le hq.le) (by linarith))]
    have hsum : 1 / q * θ + p / q * (1 - θ) = 1 := by
      field_simp
      linarith
    rw [hsum, ENNReal.rpow_one]
  have hHC : Real.HolderConjugate (1 / θ) (1 / (1 - θ)) := by
    rw [Real.holderConjugate_iff]
    refine ⟨one_lt_one_div hθ0 hθ1, ?_⟩
    rw [inv_div, inv_div]
    ring
  have H := ENNReal.lintegral_mul_le_Lp_mul_Lq ρ hHC
    (f := fun a => A a ^ θ) (g := fun a => B' a ^ (1 - θ))
    (hAm.pow_const θ).aemeasurable (hBm.pow_const (1 - θ)).aemeasurable
  have e1 : ∀ a, (A a ^ θ) ^ (1 / θ) = A a := fun a => by
    rw [← ENNReal.rpow_mul, mul_one_div_cancel hθ0.ne', ENNReal.rpow_one]
  have e2 : ∀ a, (B' a ^ (1 - θ)) ^ (1 / (1 - θ)) = B' a := fun a => by
    rw [← ENNReal.rpow_mul, mul_one_div_cancel (by linarith : (1 - θ) ≠ 0), ENNReal.rpow_one]
  simp only [e1, e2, one_div_one_div, Pi.mul_apply] at H
  calc ∫⁻ a, c a ^ q ∂ρ = ∫⁻ a, g a ∂ρ := hint
    _ = ∫⁻ a, A a ^ θ * B' a ^ (1 - θ) ∂ρ := lintegral_congr fun a => hsplit a
    _ ≤ (∫⁻ a, A a ∂ρ) ^ θ * (∫⁻ a, B' a ∂ρ) ^ (1 - θ) := H
    _ ≤ (∫⁻ a, c a ∂ρ) ^ θ * (∫⁻ a, c a ^ p ∂ρ) ^ (1 - θ) :=
        mul_le_mul' (ENNReal.rpow_le_rpow (lintegral_mono hAc) hθ0.le)
          (ENNReal.rpow_le_rpow (lintegral_mono hBc) (by linarith))

/-- **D6 (`W_q` interpolation)**, proof of `s7_FC_D6_interp`. -/
theorem s7_FC_D6_interp_proof {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [MeasurableSpace B]
    [BorelSpace B] (μ ν : Measure B) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (q δ : ℝ)
    (hq : 1 ≤ q) (hδ : 0 < δ) (M : ℝ≥0∞) (hM : M ≠ ⊤) (hμ : ∫⁻ x, ‖x‖ₑ ^ (q + δ) ∂μ ≤ M)
    (hν : ∫⁻ x, ‖x‖ₑ ^ (q + δ) ∂ν ≤ M) :
    wassersteinE q μ ν ^ q ≤ wassersteinE 1 μ ν ^ (δ / (q + δ - 1)) *
      (2 ^ (q + δ) * M) ^ ((q - 1) / (q + δ - 1)) := by
  rcases eq_or_lt_of_le hq with rfl | hq1
  · rw [show (1 : ℝ) + δ - 1 = δ by ring, div_self hδ.ne', sub_self, zero_div, ENNReal.rpow_one,
      ENNReal.rpow_zero, mul_one]
  -- Notation: `θ = δ/(q+δ-1) ∈ (0,1)`, `1 - θ = (q-1)/(q+δ-1)`, `p = q + δ`.
  have hD : 0 < q + δ - 1 := by linarith
  have hD' : q + δ - 1 ≠ 0 := hD.ne'
  obtain ⟨θ, hθdef⟩ : ∃ θ : ℝ, θ = δ / (q + δ - 1) := ⟨_, rfl⟩
  have hθ0 : 0 < θ := by rw [hθdef]; exact div_pos hδ hD
  have hθ1 : θ < 1 := by rw [hθdef, div_lt_one hD]; linarith
  have h1θ : (q - 1) / (q + δ - 1) = 1 - θ := by
    rw [hθdef]; field_simp; ring
  have hqp : θ + (1 - θ) * (q + δ) = q := by
    rw [hθdef]; field_simp; ring
  rw [← hθdef, h1θ]
  -- The constant `K = (2^(q+δ) M)^(1-θ)` is finite.
  have hK : (2 ^ (q + δ) * M) ^ (1 - θ) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (by linarith)
      (ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by linarith) ENNReal.ofNat_ne_top) hM)
  -- Pointwise bound for `(‖a - b‖ₑ)^(q+δ)`.
  have hFm : Measurable (fun x : B => ENNReal.ofReal ‖x‖ ^ (q + δ)) :=
    (ENNReal.continuous_rpow_const.comp (ENNReal.continuous_ofReal.comp continuous_norm)).measurable
  have hFe : ∀ x : B, ENNReal.ofReal ‖x‖ ^ (q + δ) = ‖x‖ₑ ^ (q + δ) := fun x => by
    rw [ofReal_norm]
  -- The `(q+δ)`-moment of the coupling cost.
  have hmom : ∀ π ∈ couplings μ ν,
      ∫⁻ z, ENNReal.ofReal ‖z.1 - z.2‖ ^ (q + δ) ∂π ≤ 2 ^ (q + δ) * M := by
    intro π hπ
    have hπ' : IsCoupling π μ ν := hπ
    have hpt : ∀ z : B × B, ENNReal.ofReal ‖z.1 - z.2‖ ^ (q + δ) ≤
        2 ^ (q + δ - 1) * (ENNReal.ofReal ‖z.1‖ ^ (q + δ) + ENNReal.ofReal ‖z.2‖ ^ (q + δ)) := by
      intro z
      have hle : ENNReal.ofReal ‖z.1 - z.2‖ ≤ ENNReal.ofReal ‖z.1‖ + ENNReal.ofReal ‖z.2‖ := by
        rw [← ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)]
        exact ENNReal.ofReal_le_ofReal (norm_sub_le _ _)
      calc ENNReal.ofReal ‖z.1 - z.2‖ ^ (q + δ)
          ≤ (ENNReal.ofReal ‖z.1‖ + ENNReal.ofReal ‖z.2‖) ^ (q + δ) :=
            ENNReal.rpow_le_rpow hle (by linarith)
        _ ≤ 2 ^ (q + δ - 1) * (ENNReal.ofReal ‖z.1‖ ^ (q + δ) + ENNReal.ofReal ‖z.2‖ ^ (q + δ)) :=
            ENNReal.rpow_add_le_mul_rpow_add_rpow _ _ (by linarith)
    have hF1 : ∫⁻ z, ENNReal.ofReal ‖z.1‖ ^ (q + δ) ∂π ≤ M := by
      have : ∫⁻ z, ENNReal.ofReal ‖z.1‖ ^ (q + δ) ∂π = ∫⁻ x, ENNReal.ofReal ‖x‖ ^ (q + δ) ∂μ := by
        have h0 : ∫⁻ x, ENNReal.ofReal ‖x‖ ^ (q + δ) ∂(π.map Prod.fst) =
            ∫⁻ z, ENNReal.ofReal ‖z.1‖ ^ (q + δ) ∂π := lintegral_map hFm measurable_fst
        rw [← h0, hπ'.1]
      rw [this]
      simp only [hFe]
      exact hμ
    have hF2 : ∫⁻ z, ENNReal.ofReal ‖z.2‖ ^ (q + δ) ∂π ≤ M := by
      have : ∫⁻ z, ENNReal.ofReal ‖z.2‖ ^ (q + δ) ∂π = ∫⁻ x, ENNReal.ofReal ‖x‖ ^ (q + δ) ∂ν := by
        have h0 : ∫⁻ x, ENNReal.ofReal ‖x‖ ^ (q + δ) ∂(π.map Prod.snd) =
            ∫⁻ z, ENNReal.ofReal ‖z.2‖ ^ (q + δ) ∂π := lintegral_map hFm measurable_snd
        rw [← h0, hπ'.2]
      rw [this]
      simp only [hFe]
      exact hν
    have hmeasF1 : Measurable (fun z : B × B => ENNReal.ofReal ‖z.1‖ ^ (q + δ)) :=
      hFm.comp measurable_fst
    have hmeasF2 : Measurable (fun z : B × B => ENNReal.ofReal ‖z.2‖ ^ (q + δ)) :=
      hFm.comp measurable_snd
    calc ∫⁻ z, ENNReal.ofReal ‖z.1 - z.2‖ ^ (q + δ) ∂π
        ≤ ∫⁻ z, 2 ^ (q + δ - 1) * (ENNReal.ofReal ‖z.1‖ ^ (q + δ) + ENNReal.ofReal ‖z.2‖ ^ (q + δ)) ∂π :=
          lintegral_mono hpt
      _ = 2 ^ (q + δ - 1) * (∫⁻ z, ENNReal.ofReal ‖z.1‖ ^ (q + δ) ∂π +
            ∫⁻ z, ENNReal.ofReal ‖z.2‖ ^ (q + δ) ∂π) := by
          rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg (by linarith) ENNReal.ofNat_ne_top),
            lintegral_add_left hmeasF1]
      _ ≤ 2 ^ (q + δ - 1) * (M + M) := by gcongr
      _ = 2 ^ (q + δ) * M := by
          have h2 : (2 : ℝ≥0∞) ^ (q + δ) = 2 ^ (q + δ - 1) * 2 := by
            conv_lhs => rw [show q + δ = (q + δ - 1) + 1 by ring]
            rw [ENNReal.rpow_add _ _ two_ne_zero ENNReal.ofNat_ne_top, ENNReal.rpow_one]
          rw [h2]
          ring
  -- Per-coupling bound.
  have hcoup : ∀ π ∈ couplings μ ν,
      wassersteinE q μ ν ^ q ≤ (∫⁻ z, ENNReal.ofReal (‖z.1 - z.2‖ ^ (1 : ℝ)) ∂π) ^ θ *
        (2 ^ (q + δ) * M) ^ (1 - θ) := by
    intro π hπ
    have hπ' : IsCoupling π μ ν := hπ
    have hq0 : 0 < q := by linarith
    have hp0 : 0 < q + δ := by linarith
    -- W_q^q ≤ ∫ ‖z‖^q dπ
    have s1 : wassersteinE q μ ν ≤ (∫⁻ z, ENNReal.ofReal (‖z.1 - z.2‖ ^ q) ∂π) ^ (1 / q) :=
      wassersteinE_le_cost hπ'
    have s1' : wassersteinE q μ ν ^ q ≤ ∫⁻ z, ENNReal.ofReal (‖z.1 - z.2‖ ^ q) ∂π := by
      calc wassersteinE q μ ν ^ q
          ≤ ((∫⁻ z, ENNReal.ofReal (‖z.1 - z.2‖ ^ q) ∂π) ^ (1 / q)) ^ q :=
            ENNReal.rpow_le_rpow s1 hq0.le
        _ = ∫⁻ z, ENNReal.ofReal (‖z.1 - z.2‖ ^ q) ∂π := by
            rw [← ENNReal.rpow_mul, one_div_mul_cancel hq0.ne', ENNReal.rpow_one]
    -- Lyapunov on the coupling
    have s2 := S7FCW1_lyapunov π (q := q) (p := q + δ) (θ := θ) hq0 hp0 hθ0 hθ1 hqp
      (fun z => ENNReal.ofReal ‖z.1 - z.2‖)
    have e_q : ∫⁻ z, ENNReal.ofReal (‖z.1 - z.2‖ ^ q) ∂π =
        ∫⁻ z, ENNReal.ofReal ‖z.1 - z.2‖ ^ q ∂π := by
      refine lintegral_congr fun z => ?_
      rw [ofReal_norm_rpow hq0.le]
    have e_1 : ∫⁻ z, ENNReal.ofReal (‖z.1 - z.2‖ ^ (1 : ℝ)) ∂π = ∫⁻ z, ENNReal.ofReal ‖z.1 - z.2‖ ∂π := by
      refine lintegral_congr fun z => ?_
      rw [Real.rpow_one]
    rw [e_1]
    have s3 := hmom π hπ
    calc wassersteinE q μ ν ^ q
        ≤ ∫⁻ z, ENNReal.ofReal (‖z.1 - z.2‖ ^ q) ∂π := s1'
      _ = ∫⁻ z, ENNReal.ofReal ‖z.1 - z.2‖ ^ q ∂π := e_q
      _ ≤ (∫⁻ z, ENNReal.ofReal ‖z.1 - z.2‖ ∂π) ^ θ *
            (∫⁻ z, ENNReal.ofReal ‖z.1 - z.2‖ ^ (q + δ) ∂π) ^ (1 - θ) := s2
      _ ≤ (∫⁻ z, ENNReal.ofReal ‖z.1 - z.2‖ ∂π) ^ θ * (2 ^ (q + δ) * M) ^ (1 - θ) := by
          gcongr
  -- Conclude by the infimum.
  have hW1 : wassersteinE 1 μ ν =
      ⨅ π : couplings μ ν, ∫⁻ z, ENNReal.ofReal (‖z.1 - z.2‖ ^ (1 : ℝ)) ∂π.1 := by
    unfold wassersteinE
    simp only [div_one, ENNReal.rpow_one]
  have hmapI : (⨅ π : couplings μ ν, ∫⁻ z, ENNReal.ofReal (‖z.1 - z.2‖ ^ (1 : ℝ)) ∂π.1) ^ θ =
      ⨅ π : couplings μ ν, (∫⁻ z, ENNReal.ofReal (‖z.1 - z.2‖ ^ (1 : ℝ)) ∂π.1) ^ θ :=
    Monotone.map_iInf_of_continuousAt (f := fun x : ℝ≥0∞ => x ^ θ)
      ENNReal.continuous_rpow_const.continuousAt
      (fun a b hab => ENNReal.rpow_le_rpow hab hθ0.le) (ENNReal.top_rpow_of_pos hθ0)
  rw [← hW1] at hmapI
  rcases eq_or_ne (((2 : ℝ≥0∞) ^ (q + δ) * M) ^ (1 - θ)) 0 with hK0 | hK0
  · -- the constant vanishes: use the product coupling
    have hπ0 : (μ.prod ν) ∈ couplings μ ν := by constructor <;> simp
    have := hcoup _ hπ0
    rw [hK0, mul_zero] at this ⊢
    exact this
  · -- the constant is positive and finite: divide
    have hdiv : wassersteinE q μ ν ^ q / (2 ^ (q + δ) * M) ^ (1 - θ) ≤
        wassersteinE 1 μ ν ^ θ := by
      rw [hmapI]
      refine le_iInf fun π => ?_
      exact ENNReal.div_le_of_le_mul (hcoup π π.2)
    rw [ENNReal.div_le_iff hK0 hK] at hdiv
    exact hdiv

end HRS.MC.Sec7.S7FCW1

end
