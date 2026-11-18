import HRS.MS.FldRemCen1

/-!
# S5.3 (`field_remainder_centered`), part 2: the mean functional is bounded

`s53_mean_bound`: `|ℓ f| ≤ C_m cbNorm 2 f` on `C_b²` (gliding hump over `g_n` with `ℓ g_n ≥ 4^n`, `cbNorm 2 g_n ≤ 1`:
the series `F = ∑ 2^{-n} g_n` is in `C_b²` and `D F(X) = lim D S_N(X)` for **every** configuration `X`, while
`∑ 2^{-n} (D g_n(X_0) - ℓ g_n)` converges a.s. by the variance bound, which contradicts `∑ 2^{-n} ℓ g_n = ∞`).
-/

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S53

open HRS HRS.Whole

variable {d N : ℕ} {s : ℝ} {ρ : Euc d → ℝ} {Mρ : ℝ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {X' : ℝ≥0 → Ω → EucConfig d N} {T CA δ : ℝ}

/-- The series `D F(X) = lim D S_N(X)` for a normalised sequence. -/
lemma s53_series_limit (ctx : S53Ctx s ρ Mρ) (hN : 0 < N) {g : ℕ → Euc d → ℝ}
    (hg : ∀ n, MemCb 2 (g n)) (hgc : ∀ n, cbNorm 2 (g n) ≤ 1) (X : EucConfig d N) :
    ∃ F : Euc d → ℝ, MemCb 2 F ∧
      Tendsto (fun M => ∑ n ∈ Finset.range M, (1 / 2 : ℝ) ^ n * s53_Dk s ρ (g n) X) atTop
        (nhds (s53_Dk s ρ F X)) := by
  set u : ℕ → Euc d → ℝ := fun n x => (1 / 2 : ℝ) ^ n * g n x with hu
  have hum : ∀ n, MemCb 2 (u n) := fun n => s53_memCb_const_mul _ (hg n)
  have hv : Summable fun n : ℕ => (1 / 2 : ℝ) ^ n := summable_geometric_two
  have hb : ∀ n, ∀ k ≤ 2, ∀ x, ‖iteratedFDeriv ℝ k (u n) x‖ ≤ (1 / 2 : ℝ) ^ n := fun n k hk x => by
    have := s53_iter_const_mul_le ((1 / 2 : ℝ) ^ n) (hg n) (hgc n) hk x
    rwa [abs_of_nonneg (by positivity)] at this
  obtain ⟨hFm, -⟩ := s53_tsum_memCb hum hv hb
  refine ⟨fun x => ∑' n, u n x, hFm, ?_⟩
  -- tails
  have hsum : ∀ x, Summable fun n => u n x := fun x =>
    Summable.of_norm_bounded hv fun n => by
      have := hb n 0 (by norm_num) x
      rwa [norm_iteratedFDeriv_zero] at this
  have htail : ∀ M : ℕ, MemCb 2 (fun x => ∑' n, u (n + M) x) ∧
      ∀ x, ‖iteratedFDeriv ℝ 2 (fun x => ∑' n, u (n + M) x) x‖ ≤ 2 * (1 / 2 : ℝ) ^ M := fun M => by
    have hv' : Summable fun n : ℕ => (1 / 2 : ℝ) ^ (n + M) := (summable_nat_add_iff M).2 hv
    obtain ⟨hm, hbd⟩ := s53_tsum_memCb (u := fun n => u (n + M)) (fun n => hum _) hv'
      (fun n k hk x => hb (n + M) k hk x)
    refine ⟨hm, fun x => (hbd 2 le_rfl x).trans (le_of_eq ?_)⟩
    simp only [pow_add]
    rw [tsum_mul_right, tsum_geometric_two]
  have hdec : ∀ M : ℕ, (fun x => ∑' n, u n x) = fun x => (∑ n ∈ Finset.range M, u n x) + ∑' n, u (n + M) x := by
    intro M; funext x
    rw [(hsum x).sum_add_tsum_nat_add M]
  refine tendsto_iff_norm_sub_tendsto_zero.2 ?_
  have hlim : ∀ M : ℕ, ‖∑ n ∈ Finset.range M, (1 / 2 : ℝ) ^ n * s53_Dk s ρ (g n) X -
      s53_Dk s ρ (fun x => ∑' n, u n x) X‖ ≤ (s + 1) * (2 * (1 / 2 : ℝ) ^ M) * s53_cX s Mρ X := by
    intro M
    obtain ⟨hSm, hSD⟩ := s53_finsum_Dk ctx hum M X
    obtain ⟨hRm, hRb⟩ := htail M
    have e1 : s53_Dk s ρ (fun x => ∑' n, u n x) X =
        s53_Dk s ρ (fun x => ∑ n ∈ Finset.range M, u n x) X + s53_Dk s ρ (fun x => ∑' n, u (n + M) x) X := by
      rw [hdec M]; exact s53_Dk_add ctx hSm hRm X
    have e2 : ∑ n ∈ Finset.range M, (1 / 2 : ℝ) ^ n * s53_Dk s ρ (g n) X =
        s53_Dk s ρ (fun x => ∑ n ∈ Finset.range M, u n x) X := by
      rw [hSD]
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [hu]; exact (s53_Dk_const_mul _ ((hg n).1.of_le (by norm_num)) X).symm
    rw [e2, e1, sub_add_cancel_left, norm_neg, Real.norm_eq_abs]
    refine (s53_Dk_bound ctx.hs0 ctx.hM0 ctx.hρ ctx.hrow hN hRm X).trans ?_
    have hsup : (⨆ x, ‖iteratedFDeriv ℝ 2 (fun x => ∑' n, u (n + M) x) x‖) ≤ 2 * (1 / 2 : ℝ) ^ M :=
      ciSup_le hRb
    have hs1 : 0 ≤ s + 1 := by linarith [ctx.hs0]
    have := s53_cX_nonneg (s := s) ctx.hM0 X
    gcongr
  refine squeeze_zero (fun _ => norm_nonneg _) hlim ?_
  have h0 : Tendsto (fun M : ℕ => (1 / 2 : ℝ) ^ M) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  simpa using (h0.const_mul (2 : ℝ)).const_mul (s + 1) |>.mul_const (s53_cX s Mρ X)


lemma s53_enorm_le_one_add_sq (x : ℝ≥0∞) : x ≤ 1 + x ^ 2 := by
  rcases le_total x 1 with h | h
  · exact h.trans le_self_add
  · calc x ≤ x ^ 2 := by
          rw [sq]; exact le_mul_of_one_le_left' h
      _ ≤ 1 + x ^ 2 := le_add_self

/-- **The mean functional is bounded on `C_b²`.** -/
lemma s53_mean_bound [IsProbabilityMeasure P] (ctx : S53Ctx s ρ Mρ) (hN : 0 < N) (hδ : 0 ≤ δ)
    (H : S53Var s ρ P X' T CA δ) :
    ∃ Cm : ℝ, 0 ≤ Cm ∧ ∀ f : Euc d → ℝ, MemCb 2 f → |s53_ell s ρ P X' f| ≤ Cm * cbNorm 2 f := by
  by_contra hcon
  have hcon' : ∀ C : ℝ, 0 ≤ C → ∃ f : Euc d → ℝ, MemCb 2 f ∧ C * cbNorm 2 f < |s53_ell s ρ P X' f| := by
    intro C hC
    by_contra h
    apply hcon
    refine ⟨C, hC, fun f hf => ?_⟩
    by_contra h'
    exact h ⟨f, hf, not_le.1 h'⟩
  obtain ⟨g, hg, hgc, hgl⟩ := s53_hump_seq ctx hN hcon'
  set ℓ : ℕ → ℝ := fun n => s53_ell s ρ P X' (g n) with hℓ
  have hmeas : ∀ n, Measurable fun ζ => s53_Dk s ρ (g n) (X' 0 ζ) := fun n =>
    (s53_Dk_meas_config ctx.hρ ((hg n).1.of_le (by norm_num))).comp (H.meas 0)
  set Dt : ℕ → Ω → ℝ := fun n ζ => s53_Dk s ρ (g n) (X' 0 ζ) - ℓ n with hDt
  have hDtm : ∀ n, Measurable (Dt n) := fun n => (hmeas n).sub_const _
  set B : ℝ≥0∞ := 1 + ENNReal.ofReal (max CA 0 * δ) with hB
  have hBfin : B ≠ ⊤ := ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, ENNReal.ofReal_ne_top⟩
  have hint : ∀ n, ∫⁻ ζ, ‖Dt n ζ‖ₑ ∂P ≤ B := fun n => by
    have h1 : ∫⁻ ζ, ‖Dt n ζ‖ₑ ∂P ≤ ∫⁻ ζ, (1 + ‖Dt n ζ‖ₑ ^ 2) ∂P :=
      lintegral_mono fun ζ => s53_enorm_le_one_add_sq _
    rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one] at h1
    refine h1.trans (add_le_add le_rfl ?_)
    have hev : ∫⁻ ζ, ‖Dt n ζ‖ₑ ^ 2 ∂P = evariance (fun ζ => s53_Dk s ρ (g n) (X' 0 ζ)) P := rfl
    rw [hev]
    have hN1 : (1 : ℝ≥0∞) ≤ N := by exact_mod_cast hN
    refine le_trans (le_mul_of_one_le_left' hN1) ((H.var (g n) (hg n)).trans (ENNReal.ofReal_le_ofReal ?_))
    have hp : (⨆ x, ‖iteratedFDeriv ℝ 2 (g n) x‖) ≤ 1 := (s53_p_le_cb (hg n)).trans (hgc n)
    have hp0 := s53_cbSup_nonneg (g n)
    have hp2 : (⨆ x, ‖iteratedFDeriv ℝ 2 (g n) x‖) ^ 2 ≤ 1 := by nlinarith
    have : CA * δ ≤ max CA 0 * δ := mul_le_mul_of_nonneg_right (le_max_left _ _) hδ
    have h0 : 0 ≤ max CA 0 * δ := mul_nonneg (le_max_right _ _) hδ
    calc CA * δ * (⨆ x, ‖iteratedFDeriv ℝ 2 (g n) x‖) ^ 2 ≤ max CA 0 * δ * (⨆ x, ‖iteratedFDeriv ℝ 2 (g n) x‖) ^ 2 := by
          gcongr
      _ ≤ max CA 0 * δ * 1 := by gcongr
      _ = max CA 0 * δ := mul_one _
  -- the random series converges a.s.
  have hser : ∫⁻ ζ, ∑' n, ENNReal.ofReal ((1 / 2 : ℝ) ^ n) * ‖Dt n ζ‖ₑ ∂P ≠ ⊤ := by
    rw [lintegral_tsum fun n => ((hDtm n).enorm.const_mul _).aemeasurable]
    simp only [lintegral_const_mul _ (hDtm _).enorm]
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum fun n => mul_le_mul_right (hint n) _)
    rw [ENNReal.tsum_mul_right, ← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) summable_geometric_two,
      tsum_geometric_two]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hBfin
  have hae : ∀ᵐ ζ ∂P, ∑' n, ENNReal.ofReal ((1 / 2 : ℝ) ^ n) * ‖Dt n ζ‖ₑ < ⊤ :=
    ae_lt_top (Measurable.tsum fun n => (hDtm n).enorm.const_mul _) hser
  obtain ⟨ζ0, hζ0⟩ := hae.exists
  -- summability of the centered series at `ζ0`
  have hsa : Summable fun n => (1 / 2 : ℝ) ^ n * Dt n ζ0 := by
    have h1 : Summable fun n => (ENNReal.ofReal ((1 / 2 : ℝ) ^ n) * ‖Dt n ζ0‖ₑ).toReal :=
      ENNReal.summable_toReal hζ0.ne
    refine Summable.of_norm_bounded h1 fun n => ?_
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (1 / 2) ^ n),
      ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity), toReal_enorm]
  -- the series of `D g_n` at `X' 0 ζ0`
  obtain ⟨F, hFm, hFlim⟩ := s53_series_limit ctx hN hg hgc (X' 0 ζ0)
  have hsplit : ∀ M : ℕ, ∑ n ∈ Finset.range M, (1 / 2 : ℝ) ^ n * s53_Dk s ρ (g n) (X' 0 ζ0) =
      ∑ n ∈ Finset.range M, (1 / 2 : ℝ) ^ n * Dt n ζ0 + ∑ n ∈ Finset.range M, (1 / 2 : ℝ) ^ n * ℓ n := by
    intro M
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    simp only [hDt]; ring
  have hlim2 : Tendsto (fun M => ∑ n ∈ Finset.range M, (1 / 2 : ℝ) ^ n * ℓ n) atTop
      (nhds (s53_Dk s ρ F (X' 0 ζ0) - ∑' n, (1 / 2 : ℝ) ^ n * Dt n ζ0)) := by
    have := hFlim.sub hsa.hasSum.tendsto_sum_nat
    refine this.congr fun M => ?_
    rw [hsplit M]; ring
  have hge : ∀ M : ℕ, (M : ℝ) ≤ ∑ n ∈ Finset.range M, (1 / 2 : ℝ) ^ n * ℓ n := by
    intro M
    have : ∀ n ∈ Finset.range M, (1 : ℝ) ≤ (1 / 2 : ℝ) ^ n * ℓ n := by
      intro n _
      have h4 : (4 : ℝ) ^ n < ℓ n := hgl n
      have h2 : (2 : ℝ) ^ n ≤ 4 ^ n := pow_le_pow_left₀ (by norm_num) (by norm_num) n
      have h1 : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
      have h5 : (1 / 2 : ℝ) ^ n * 2 ^ n = 1 := by rw [← mul_pow]; norm_num
      calc (1 : ℝ) = (1 / 2 : ℝ) ^ n * 2 ^ n := h5.symm
        _ ≤ (1 / 2 : ℝ) ^ n * ℓ n := by
            apply mul_le_mul_of_nonneg_left _ (by positivity); linarith
    calc (M : ℝ) = ∑ _n ∈ Finset.range M, (1 : ℝ) := by simp
      _ ≤ _ := Finset.sum_le_sum this
  have hat : Tendsto (fun M : ℕ => ∑ n ∈ Finset.range M, (1 / 2 : ℝ) ^ n * ℓ n) atTop atTop :=
    tendsto_atTop_mono hge tendsto_natCast_atTop_atTop
  exact not_tendsto_nhds_of_tendsto_atTop hat _ hlim2

end HRS.MS.S53
