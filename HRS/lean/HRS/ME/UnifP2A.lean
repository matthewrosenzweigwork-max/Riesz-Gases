import HRS.ME.NfUPU1aA

/-!
# Uniform Lemma 4.5 (`M:R:lem:integrals`, `critical_integrals`), packet P2

`critical_integrals_unif`: the constants `C`, `C_v`, `C_M` of `HRS.critical_integrals` are chosen before the
density `ρ` and before `β`; the density enters only through `SmoothPosDensity ρ` and `ρ ≤ Λ`.  The lower bound
`c₀ ≤ ρ` is not used.  The pieces `conj_trunc`, `conj_pow`, `conj_expo` are reused from `HRS.ME.NfU`
(`NfUPU1aA`); `conj_schur` and `conj_last` are copied with `Λ` a parameter; `conj_small` does not involve `ρ`.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

namespace HRS.ME.Unif

open HRS HRS.PoleCavityAux HRS.KernelAux HRS.KernelAux2

variable {d : ℕ} {s : ℝ}

/-- Uniform `conj_schur`: the constant depends on `Λ` only. -/
theorem conj_schur_unif (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) (c : ℝ) (Λ : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ ρ : Torus d → ℝ, SmoothPosDensity ρ → (∀ x, ρ x ≤ Λ) →
      ∀ f : Torus d → ℝ, Measurable f →
      ∫⁻ x, (∫⁻ y, ENNReal.ofReal (gPlus d s c (x - y)) * ‖f y‖ₑ ∂(withDensityReal ρ)) ^ 2
          ∂(withDensityReal ρ) ≤
        ENNReal.ofReal C * ∫⁻ y, ‖f y‖ₑ ^ 2 ∂(withDensityReal ρ) := by
  obtain ⟨hs0, hsd⟩ := hs_aux hd hcrit
  have hgm := measurable_gPlus hd hs0 hsd c
  set a : Torus d → ℝ≥0∞ := fun z => ENNReal.ofReal (gPlus d s c z) with ha
  have ham : Measurable a := ENNReal.measurable_ofReal.comp hgm
  set S : ℝ≥0∞ := ENNReal.ofReal Λ * ∫⁻ z, a z with hS
  have hSfin : S ≠ ∞ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (lintegral_gPlus_lt_top hd hcrit c).ne
  refine ⟨(S ^ 2).toReal + 1, by positivity, fun ρ hρ hΛ f hf => ?_⟩
  have hprob := isProbabilityMeasure_mu hρ
  set μ := withDensityReal ρ with hμ
  have h1 : ∀ x, ∫⁻ y, a (x - y) ∂μ ≤ S := fun x =>
    lintegral_conv_le ρ Λ hΛ a x
  have h2 : ∀ y, ∫⁻ x, a (x - y) ∂μ ≤ S := by
    intro y
    have : ∀ x, a (x - y) = a (y - x) := fun x => by
      simp only [ha]; rw [← gPlus_neg (s := s) c (y - x), neg_sub]
    simp_rw [this]
    exact h1 y
  have hFm : Measurable fun y => ‖f y‖ₑ := hf.enorm
  have hSq : S ^ 2 ≤ ENNReal.ofReal ((S ^ 2).toReal + 1) := by
    rw [ENNReal.ofReal_add ENNReal.toReal_nonneg zero_le_one, ENNReal.ofReal_toReal
      (ENNReal.pow_ne_top hSfin)]
    exact le_self_add
  calc ∫⁻ x, (∫⁻ y, a (x - y) * ‖f y‖ₑ ∂μ) ^ 2 ∂μ
      ≤ ∫⁻ x, S * ∫⁻ y, a (x - y) * ‖f y‖ₑ ^ 2 ∂μ ∂μ := by
        refine lintegral_mono fun x => ?_
        refine (weighted_cs μ (fun y => a (x - y)) (fun y => ‖f y‖ₑ)
          (ham.comp (measurable_const.sub measurable_id)) hFm).trans ?_
        exact mul_le_mul' (h1 x) le_rfl
    _ = S * ∫⁻ x, ∫⁻ y, a (x - y) * ‖f y‖ₑ ^ 2 ∂μ ∂μ := lintegral_const_mul' _ _ hSfin
    _ = S * ∫⁻ y, ∫⁻ x, a (x - y) * ‖f y‖ₑ ^ 2 ∂μ ∂μ := by
        congr 1
        refine lintegral_lintegral_swap (f := fun x y => a (x - y) * ‖f y‖ₑ ^ 2) ?_
        exact ((ham.comp (measurable_fst.sub measurable_snd)).mul
          ((hFm.comp measurable_snd).pow_const 2)).aemeasurable
    _ = S * ∫⁻ y, (∫⁻ x, a (x - y) ∂μ) * ‖f y‖ₑ ^ 2 ∂μ := by
        congr 1
        refine lintegral_congr fun y => ?_
        exact lintegral_mul_const _ (ham.comp (measurable_id.sub measurable_const))
    _ ≤ S * ∫⁻ y, S * ‖f y‖ₑ ^ 2 ∂μ := by
        refine mul_le_mul' le_rfl (lintegral_mono fun y => ?_)
        exact mul_le_mul' (h2 y) le_rfl
    _ = S * (S * ∫⁻ y, ‖f y‖ₑ ^ 2 ∂μ) := by
        congr 1; exact lintegral_const_mul' _ _ hSfin
    _ = S ^ 2 * ∫⁻ y, ‖f y‖ₑ ^ 2 ∂μ := by ring
    _ ≤ _ := mul_le_mul' hSq le_rfl


/-- Uniform `conj_last`: the constant depends on `Λ` only (not on `β ≥ 0` or on `ρ ≤ Λ`). -/
theorem conj_last_unif (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) (c : ℝ)
    (hc : ∀ z, 0 ≤ periodicRiesz d s z + c) (Λ : ℝ) :
    ∃ C : ℝ, ∀ ρ : Torus d → ℝ, SmoothPosDensity ρ → (∀ x, ρ x ≤ Λ) →
      ∀ β : ℝ, 0 ≤ β → ∀ N : ℕ, 2 ≤ N → ∀ x : Torus d, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ∫⁻ z, (∫⁻ y, ENNReal.ofReal (gPlus d s c (x - y) *
            Real.exp (-(t * (β / N)) * gPlus d s c (x - y)) * gPlus d s c (y - z))
            ∂(withDensityReal ρ)) ^ 2 ∂(withDensityReal ρ) ≤ ENNReal.ofReal C := by
  obtain ⟨hs0, hsd⟩ := hs_aux hd hcrit
  have hgm := measurable_gPlus hd hs0 hsd c
  set a : Torus d → ℝ≥0∞ := fun z => ENNReal.ofReal (gPlus d s c z) with ha
  have ham : Measurable a := ENNReal.measurable_ofReal.comp hgm
  set Ab := ∫⁻ z, (a z ^ (2 / 3 : ℝ)) ^ 2 with hAb
  have hAbfin : Ab ≠ ∞ := A_finite hd hcrit c hc
  set B : ℝ≥0∞ := ENNReal.ofReal Λ ^ 3 * Ab ^ 3 with hB
  have hBfin : B ≠ ∞ := ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
    (ENNReal.pow_ne_top hAbfin)
  refine ⟨B.toReal, fun ρ hρ hΛ β hβ N hN x t ht => ?_⟩
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  -- pointwise reduction
  have hpt : ∀ z y, ENNReal.ofReal (gPlus d s c (x - y) *
      Real.exp (-(t * (β / N)) * gPlus d s c (x - y)) * gPlus d s c (y - z)) ≤
        a (x - y) * a (y - z) := by
    intro z y
    have h0 := hc (x - y)
    have h0' := hc (y - z)
    have hg1 : 0 ≤ gPlus d s c (x - y) := h0
    have hg2 : 0 ≤ gPlus d s c (y - z) := h0'
    have hE : Real.exp (-(t * (β / N)) * gPlus d s c (x - y)) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have : 0 ≤ t * (β / N) := by have := ht.1; positivity
      nlinarith
    simp only [ha]
    rw [← ENNReal.ofReal_mul hg1]
    refine ENNReal.ofReal_le_ofReal ?_
    have hE0 := (Real.exp_pos (-(t * (β / N)) * gPlus d s c (x - y))).le
    calc gPlus d s c (x - y) * Real.exp (-(t * (β / N)) * gPlus d s c (x - y)) *
          gPlus d s c (y - z) ≤ gPlus d s c (x - y) * 1 * gPlus d s c (y - z) := by gcongr
      _ = _ := by ring
  set K : Torus d → ℝ≥0∞ := fun u => ∫⁻ w, a w * a (u - w) with hK
  have hJ : ∀ z, ∫⁻ y, a (x - y) * a (y - z) = K (x - z) := by
    intro z
    have := lintegral_sub_left_torus (fun w => a w * a (x - z - w)) x
    simp only [hK]
    rw [← this]
    refine lintegral_congr fun y => ?_
    show a (x - y) * a (y - z) = a (x - y) * a (x - z - (x - y))
    congr 2
    abel
  have hKm : Measurable K := by
    refine Measurable.lintegral_prod_right' (f := fun p : Torus d × Torus d => a p.2 * a (p.1 - p.2)) ?_
    exact (ham.comp measurable_snd).mul (ham.comp (measurable_fst.sub measurable_snd))
  have hKint : ∫⁻ u, K u ^ 2 ≤ Ab ^ 3 := young_sq a ham hAbfin
  calc ∫⁻ z, (∫⁻ y, ENNReal.ofReal (gPlus d s c (x - y) *
            Real.exp (-(t * (β / N)) * gPlus d s c (x - y)) * gPlus d s c (y - z))
            ∂(withDensityReal ρ)) ^ 2 ∂(withDensityReal ρ)
      ≤ ∫⁻ z, (ENNReal.ofReal Λ * K (x - z)) ^ 2 ∂(withDensityReal ρ) := by
        refine lintegral_mono fun z => ?_
        refine pow_le_pow_left' ?_ 2
        calc _ ≤ ∫⁻ y, a (x - y) * a (y - z) ∂(withDensityReal ρ) :=
              lintegral_mono fun y => hpt z y
          _ ≤ ENNReal.ofReal Λ * ∫⁻ y, a (x - y) * a (y - z) :=
              lintegral_mu_le_vol hΛ (fun y => a (x - y) * a (y - z))
          _ = _ := by rw [hJ z]
    _ ≤ ENNReal.ofReal Λ * ∫⁻ z, (ENNReal.ofReal Λ * K (x - z)) ^ 2 :=
        lintegral_mu_le_vol hΛ (fun z => (ENNReal.ofReal Λ * K (x - z)) ^ 2)
    _ = ENNReal.ofReal Λ * (ENNReal.ofReal Λ ^ 2 * ∫⁻ z, K (x - z) ^ 2) := by
        congr 1
        rw [← lintegral_const_mul' _ _ (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)]
        simp_rw [mul_pow]
    _ = ENNReal.ofReal Λ ^ 3 * ∫⁻ u, K u ^ 2 := by
        rw [lintegral_sub_left_torus (fun u => K u ^ 2) x]; ring
    _ ≤ B := by
        calc _ ≤ ENNReal.ofReal Λ ^ 3 * Ab ^ 3 := mul_le_mul' le_rfl hKint
          _ = B := rfl
    _ = ENNReal.ofReal B.toReal := (ENNReal.ofReal_toReal hBfin).symm


/-- **Lemma 4.5 (`critical_integrals`), uniform form.** All constants are chosen after `d, s, c, Λ ≥ 1` and
before `β` and `ρ` (smooth positive density with `ρ ≤ Λ`). -/
theorem critical_integrals_unif (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) (c : ℝ)
    (hc : ∀ z, 0 ≤ periodicRiesz d s z + c) (Λ : ℝ) (hΛ : 1 ≤ Λ) :
    ∃ C : ℝ,
      (∀ ρ : Torus d → ℝ, SmoothPosDensity ρ → (∀ x, ρ x ≤ Λ) →
        (∀ H : ℝ, 2 ≤ H → ∀ x : Torus d,
          ∫⁻ y, ENNReal.ofReal (gTrunc d s c H (x - y) ^ 2) ∂(withDensityReal ρ) ≤
              ENNReal.ofReal (C * Real.log H) ∧
            ∫⁻ y, ENNReal.ofReal (gPlus d s c (x - y) - gTrunc d s c H (x - y))
                ∂(withDensityReal ρ) ≤ ENNReal.ofReal (C / H)) ∧
        (∀ f : Torus d → ℝ, Measurable f →
          ∫⁻ x, (∫⁻ y, ENNReal.ofReal (gPlus d s c (x - y)) * ‖f y‖ₑ ∂(withDensityReal ρ)) ^ 2
              ∂(withDensityReal ρ) ≤
            ENNReal.ofReal C * ∫⁻ y, ‖f y‖ₑ ^ 2 ∂(withDensityReal ρ)) ∧
        (∀ u : ℝ, 0 < u → u ≤ 1 → ∀ x : Torus d,
          ∫⁻ y, ENNReal.ofReal (gPlus d s c (x - y) ^ 2 * Real.exp (-u * gPlus d s c (x - y)))
              ∂(withDensityReal ρ) ≤ ENNReal.ofReal (C * (1 + |Real.log u|))) ∧
        (∀ β : ℝ, 0 ≤ β → ∀ N : ℕ, 2 ≤ N → ∀ x : Torus d, ∀ t ∈ Set.Icc (0 : ℝ) 1,
          ∫⁻ z, (∫⁻ y, ENNReal.ofReal (gPlus d s c (x - y) *
                Real.exp (-(t * (β / N)) * gPlus d s c (x - y)) * gPlus d s c (y - z))
                ∂(withDensityReal ρ)) ^ 2 ∂(withDensityReal ρ) ≤ ENNReal.ofReal C)) ∧
      (∀ v : ℝ, 2 < v → ∃ Cv : ℝ, ∀ ρ : Torus d → ℝ, SmoothPosDensity ρ → (∀ x, ρ x ≤ Λ) →
        ∀ H : ℝ, 2 ≤ H → ∀ x : Torus d,
          ∫⁻ y, ENNReal.ofReal (gTrunc d s c H (x - y) ^ v) ∂(withDensityReal ρ) ≤
            ENNReal.ofReal (Cv * H ^ (v - 2))) ∧
      (∀ M : ℝ, ∃ CM : ℝ, ∀ (w : Torus d → ℝ) (e : ℝ), Measurable w → (∀ y, |w y| ≤ M) →
        e ≤ 1 → ∫⁻ y, ‖w y‖ₑ ≤ ENNReal.ofReal e → ∀ x : Torus d,
          ∫⁻ y, ENNReal.ofReal (gPlus d s c (x - y)) * ‖w y‖ₑ ≤
            ENNReal.ofReal (CM * Real.sqrt e)) := by
  obtain ⟨C1, hC1, h1⟩ := NfU.conj_trunc_unif hd hcrit c hc Λ hΛ
  obtain ⟨C3, hC3, h3⟩ := conj_schur_unif hd hcrit c Λ
  obtain ⟨C5, hC5, h5⟩ := NfU.conj_expo_unif hd hcrit c hc Λ hΛ
  obtain ⟨C6, h6⟩ := conj_last_unif hd hcrit c hc Λ
  refine ⟨max (max C1 C3) (max C5 C6), ?_, ?_, ?_⟩
  · intro ρ hρ hΛρ
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro H hH x
      have hlog : 0 ≤ Real.log H := Real.log_nonneg (by linarith)
      have hH0 : 0 < H := by linarith
      have hm : C1 ≤ max (max C1 C3) (max C5 C6) := (le_max_left _ _).trans (le_max_left _ _)
      refine ⟨(h1 ρ hρ hΛρ H hH x).1.trans (ENNReal.ofReal_le_ofReal ?_),
        (h1 ρ hρ hΛρ H hH x).2.trans (ENNReal.ofReal_le_ofReal ?_)⟩
      · exact mul_le_mul_of_nonneg_right hm hlog
      · exact div_le_div_of_nonneg_right hm hH0.le
    · intro f hf
      refine (h3 ρ hρ hΛρ f hf).trans ?_
      gcongr
      exact (le_max_right C1 C3).trans (le_max_left _ _)
    · intro u hu hu1 x
      refine (h5 ρ hρ hΛρ u hu hu1 x).trans (ENNReal.ofReal_le_ofReal ?_)
      exact mul_le_mul_of_nonneg_right ((le_max_left C5 C6).trans (le_max_right _ _))
        (by positivity)
    · intro β hβ N hN x t ht
      exact (h6 ρ hρ hΛρ β hβ N hN x t ht).trans (ENNReal.ofReal_le_ofReal
        ((le_max_right C5 C6).trans (le_max_right _ _)))
  · intro v hv
    obtain ⟨Cv, -, hv'⟩ := NfU.conj_pow_unif hd hcrit c hc v hv Λ hΛ
    exact ⟨Cv, hv'⟩
  · intro M
    obtain ⟨CM, hCM⟩ := PoleCavityAux.conj_small hd hcrit c hc M
    exact ⟨CM, hCM⟩

end HRS.ME.Unif

end
