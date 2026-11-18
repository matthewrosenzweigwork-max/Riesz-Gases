import HRS.MC.S7E5

/-!
# E718A: Proposition 7.18, non-tightness and absence of a square-mean limit

Proofs of the two statements `HRS.chaos_laws_not_tight` and `HRS.chaos_no_L2_limit` (stated in `HRS/MC/S7Chaos.lean`, with
the statements below copied verbatim).  Both follow from the proved packets `S7E4.e4_sigma_top` (the variance of `Q_ε`
tends to infinity) and `S7E5.s7_E5_not_tight_proof` (`P(|Q_ε| > R) → 1`).

* Not tight: a tight family has, for the level `1/2`, a compact set `K ⊆ [-R,R]` with `P(Q_{ε_n} ∉ K) ≤ 1/2` for all `n`,
  hence `P(|Q_{ε_n}| > R) ≤ 1/2`, against `P(|Q_{ε_n}| > R) → 1`.
* No limit in square mean: if `E|Q_{ε_n} - Q₀|² → 0`, then `Q₀` is square integrable (as `Q_{ε_n}` is for one `n`, since
  `E Q_{ε_n}² > 0` there), and `E Q_{ε_n}² ≤ 2 E|Q_{ε_n} - Q₀|² + 2 E Q₀²` stays bounded, against `E Q_ε² → ∞`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal

noncomputable section

namespace HRS.MC.E718

open HRS HRS.Sec7 HRS.MC.Sec7

variable {d : ℕ}

theorem chaos_laws_not_tight_proof (hd : 2 ≤ d) {s : ℝ} (hs : (d : ℝ) / 2 ≤ s) (hsd : s < d) {β : ℝ}
    (hβ : 0 < β) (ρ : Torus d → ℝ) (hρ : SmoothPosDensity ρ) (φ : Torus d → ℝ)
    (hφ : Torus.IsSmooth φ) (hnc : ∃ x y, φ x ≠ φ y) (e : ℕ → Torus d → ℝ)
    (he : IsONBL2Zero (withDensityReal ρ) e) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (G : ℕ → Ω → ℝ) (hG : s7_GaussData d s β ρ e P G) (Q : ℝ → Ω → ℝ)
    (hQ : ∀ ε, 0 < ε → AEMeasurable (Q ε) P ∧ s7_IsChaosLimit d s β ρ e P G (hCut d s φ ε) (Q ε))
    (ε : ℕ → ℝ) (hε0 : ∀ n, 0 < ε n) (hε : Tendsto ε atTop (𝓝 0)) :
    ¬ IsTightMeasureSet (Set.range fun n : ℕ => P.map (Q (ε n))) := by
  intro htight
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le] at htight
  obtain ⟨K, hK, hKb⟩ := htight (1 / 2) (by norm_num)
  obtain ⟨R, hR⟩ := hK.isBounded.exists_norm_le
  have h5 := HRS.MC.Sec7.E5.s7_E5_not_tight_proof hd hs hsd hβ ρ hρ φ hφ hnc e he P G hG Q hQ R
  have hεw : Tendsto ε atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨hε, Eventually.of_forall hε0⟩
  have h6 := h5.comp hεw
  have h7 : ∀ᶠ n in atTop, (1 / 2 : ℝ≥0∞) < P {ω | R < |Q (ε n) ω|} :=
    h6.eventually (lt_mem_nhds (by
      rw [ENNReal.div_lt_iff (Or.inl (by norm_num)) (Or.inl (by norm_num))]; norm_num))
  obtain ⟨n, hn⟩ := h7.exists
  have hmeas : AEMeasurable (Q (ε n)) P := (hQ (ε n) (hε0 n)).1
  have h8 := hKb (P.map (Q (ε n))) ⟨n, rfl⟩
  rw [Measure.map_apply_of_aemeasurable hmeas hK.isClosed.measurableSet.compl] at h8
  have hsub : {ω | R < |Q (ε n) ω|} ⊆ Q (ε n) ⁻¹' Kᶜ := by
    intro ω hω hmem
    have := hR _ hmem
    rw [Real.norm_eq_abs] at this
    exact absurd hω (not_lt.2 this)
  exact absurd (lt_of_lt_of_le hn ((measure_mono hsub).trans h8)) (lt_irrefl _)

theorem enorm_sq_eq (x : ℝ) : ‖x‖ₑ ^ 2 = ENNReal.ofReal (x ^ 2) := by
  rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg x), sq_abs]

theorem enorm_sq_le (a b : ℝ) : ‖a‖ₑ ^ 2 ≤ 2 * ‖a - b‖ₑ ^ 2 + 2 * ‖b‖ₑ ^ 2 := by
  rw [enorm_sq_eq, enorm_sq_eq, enorm_sq_eq]
  have h : a ^ 2 ≤ 2 * (a - b) ^ 2 + 2 * b ^ 2 := by nlinarith [sq_nonneg (a - 2 * b)]
  calc ENNReal.ofReal (a ^ 2) ≤ ENNReal.ofReal (2 * (a - b) ^ 2 + 2 * b ^ 2) := ENNReal.ofReal_le_ofReal h
    _ = 2 * ENNReal.ofReal ((a - b) ^ 2) + 2 * ENNReal.ofReal (b ^ 2) := by
        rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul (by norm_num),
          ENNReal.ofReal_mul (by norm_num)]
        simp

theorem integral_sq_eq_toReal {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) {f : Ω → ℝ}
    (hf : AEMeasurable f P) : ∫ ω, f ω ^ 2 ∂P = (∫⁻ ω, ‖f ω‖ₑ ^ 2 ∂P).toReal := by
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun ω => sq_nonneg (f ω))
    ((hf.pow_const 2).aestronglyMeasurable)]
  simp_rw [enorm_sq_eq]

theorem chaos_no_L2_limit_proof (hd : 2 ≤ d) {s : ℝ} (hs : (d : ℝ) / 2 ≤ s) (hsd : s < d) {β : ℝ}
    (hβ : 0 < β) (ρ : Torus d → ℝ) (hρ : SmoothPosDensity ρ) (φ : Torus d → ℝ)
    (hφ : Torus.IsSmooth φ) (hnc : ∃ x y, φ x ≠ φ y) (e : ℕ → Torus d → ℝ)
    (he : IsONBL2Zero (withDensityReal ρ) e) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (G : ℕ → Ω → ℝ) (hG : s7_GaussData d s β ρ e P G) (Q : ℝ → Ω → ℝ)
    (hQ : ∀ ε, 0 < ε → AEMeasurable (Q ε) P ∧ s7_IsChaosLimit d s β ρ e P G (hCut d s φ ε) (Q ε))
    (ε : ℕ → ℝ) (hε0 : ∀ n, 0 < ε n) (hε : Tendsto ε atTop (𝓝 0)) :
    ¬ ∃ Q₀ : Ω → ℝ, AEMeasurable Q₀ P ∧
      Tendsto (fun n : ℕ => ∫⁻ ω, ‖Q (ε n) ω - Q₀ ω‖ₑ ^ 2 ∂P) atTop (𝓝 0) := by
  rintro ⟨Q₀, hQ₀, hlim⟩
  have hεw : Tendsto ε atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨hε, Eventually.of_forall hε0⟩
  have hσ := (HRS.MC.Sec7.E4.e4_sigma_top hd hs hsd hβ ρ hρ φ hφ hnc e he P G hG Q hQ).comp hεw
  have hmeas : ∀ n, AEMeasurable (Q (ε n)) P := fun n => (hQ (ε n) (hε0 n)).1
  have hd1 : ∀ᶠ n in atTop, ∫⁻ ω, ‖Q (ε n) ω - Q₀ ω‖ₑ ^ 2 ∂P ≤ 1 :=
    hlim.eventually (ge_mem_nhds (by norm_num))
  have hbig : ∀ᶠ n in atTop, (1 : ℝ) ≤ ∫ ω, Q (ε n) ω ^ 2 ∂P := hσ.eventually_ge_atTop 1
  obtain ⟨n0, hn0a, hn0b⟩ := (hd1.and hbig).exists
  have hfin : ∫⁻ ω, ‖Q (ε n0) ω‖ₑ ^ 2 ∂P ≠ ⊤ := by
    intro htop
    rw [integral_sq_eq_toReal P (hmeas n0), htop] at hn0b
    simp at hn0b
    linarith
  -- `Q₀` is square integrable
  have hmeasD : ∀ n, AEMeasurable (fun ω => ‖Q (ε n) ω - Q₀ ω‖ₑ ^ 2) P := fun n =>
    (((hmeas n).sub hQ₀).enorm).pow_const 2
  have hmeasQ : ∀ n, AEMeasurable (fun ω => ‖Q (ε n) ω‖ₑ ^ 2) P := fun n =>
    ((hmeas n).enorm).pow_const 2
  have hmeas0 : AEMeasurable (fun ω => ‖Q₀ ω‖ₑ ^ 2) P := hQ₀.enorm.pow_const 2
  set L0 : ℝ≥0∞ := ∫⁻ ω, ‖Q₀ ω‖ₑ ^ 2 ∂P with hL0def
  have hL0 : L0 ≤ 2 * 1 + 2 * ∫⁻ ω, ‖Q (ε n0) ω‖ₑ ^ 2 ∂P := by
    calc L0 ≤ ∫⁻ ω, (2 * ‖Q (ε n0) ω - Q₀ ω‖ₑ ^ 2 + 2 * ‖Q (ε n0) ω‖ₑ ^ 2) ∂P := by
          refine lintegral_mono fun ω => ?_
          have := enorm_sq_le (Q₀ ω) (Q (ε n0) ω)
          rwa [enorm_sub_rev] at this
      _ = 2 * ∫⁻ ω, ‖Q (ε n0) ω - Q₀ ω‖ₑ ^ 2 ∂P + 2 * ∫⁻ ω, ‖Q (ε n0) ω‖ₑ ^ 2 ∂P := by
          rw [lintegral_add_left' ((hmeasD n0).const_mul 2), lintegral_const_mul'' _ (hmeasD n0),
            lintegral_const_mul'' _ (hmeasQ n0)]
      _ ≤ _ := by gcongr
  have hL0fin : L0 ≠ ⊤ :=
    ne_top_of_le_ne_top (by simp [ENNReal.mul_eq_top, hfin]) hL0
  -- the second moments of `Q (ε n)` stay bounded
  set B : ℝ≥0∞ := 2 * 1 + 2 * L0 with hBdef
  have hBfin : B ≠ ⊤ := by simp [hBdef, ENNReal.mul_eq_top, hL0fin]
  have hbd : ∀ᶠ n in atTop, ∫ ω, Q (ε n) ω ^ 2 ∂P ≤ B.toReal := by
    filter_upwards [hd1] with n hn
    rw [integral_sq_eq_toReal P (hmeas n)]
    refine ENNReal.toReal_mono hBfin ?_
    calc ∫⁻ ω, ‖Q (ε n) ω‖ₑ ^ 2 ∂P
        ≤ ∫⁻ ω, (2 * ‖Q (ε n) ω - Q₀ ω‖ₑ ^ 2 + 2 * ‖Q₀ ω‖ₑ ^ 2) ∂P :=
          lintegral_mono fun ω => enorm_sq_le (Q (ε n) ω) (Q₀ ω)
      _ = 2 * ∫⁻ ω, ‖Q (ε n) ω - Q₀ ω‖ₑ ^ 2 ∂P + 2 * L0 := by
          rw [lintegral_add_left' ((hmeasD n).const_mul 2), lintegral_const_mul'' _ (hmeasD n),
            lintegral_const_mul'' _ hmeas0]
      _ ≤ 2 * 1 + 2 * L0 := by gcongr
  obtain ⟨n1, hn1⟩ := (hbd.and (hσ.eventually_ge_atTop (B.toReal + 1))).exists
  have h1 := hn1.1
  have h2 := hn1.2
  have h2' : B.toReal + 1 ≤ ∫ ω, Q (ε n1) ω ^ 2 ∂P := h2
  linarith

end HRS.MC.E718

end
