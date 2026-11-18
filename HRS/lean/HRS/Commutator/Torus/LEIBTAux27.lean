import HRS.Commutator.Torus.LEIBTAux26

/-!
# LEIB-T: the main theorem
-/

noncomputable section

open MeasureTheory Filter Topology Metric Set
open scoped ENNReal NNReal BigOperators FourierTransform ContDiff SchwartzMap RealInnerProductSpace
  ComplexConjugate

namespace HRS.Commutator.TorusNote

open HRS

variable {d : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin d)

theorem leibt_main (hd : 1 ≤ d) (α : ℝ) (hα : 0 < α) (r p₁ q₁ p₂ q₂ : ℝ≥0∞)
    (hr : 1 < r) (hr' : r < ⊤) (hp₁ : 1 < p₁) (hq₁ : 1 < q₁) (hp₂ : 1 < p₂) (hq₂ : 1 < q₂)
    (h1 : p₁⁻¹ + q₁⁻¹ = r⁻¹) (h2 : p₂⁻¹ + q₂⁻¹ = r⁻¹) :
    ∃ C : ℝ, 0 < C ∧ ∀ η : ℝ, 0 < η → η ≤ 1 → ∀ f g h F G H : Torus d → ℝ,
      Torus.IsSmooth f → Torus.IsSmooth g → (∀ x, h x = f x * g x) →
      Integrable F → Integrable G → Integrable H →
      IsBesselRepT η α f F → IsBesselRepT η α g G → IsBesselRepT η α h H →
        eLpNorm H r volume ≤ ENNReal.ofReal C *
          (eLpNorm F p₁ volume * eLpNorm g q₁ volume + eLpNorm G p₂ volume * eLpNorm f q₂ volume) := by
  obtain ⟨Cl, hClTop, hCl⟩ := HRS.Commutator.Whole.XLI.main_uncond (d := d) α hd hα hr hr' hp₁ hq₁
    hp₂ hq₂ h1 h2
  have hc1 : (1 : ℝ) ≤ 2 * d + 1 := by linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
  refine ⟨Cl.toReal * (2 * d + 1 : ℝ) ^ d + 1, by positivity, ?_⟩
  intro η hη hη1 f g h F G H hf hg hh hFi hGi hHi hrF hrG hrH
  have hhS := leibt_smooth_mul hf hg hh
  have hfc := leibt_continuous_of_smooth hf
  have hgc := leibt_continuous_of_smooth hg
  have hp₁0 : p₁ ≠ 0 := by intro h0; rw [h0] at hp₁; simp at hp₁
  have hq₁0 : q₁ ≠ 0 := by intro h0; rw [h0] at hq₁; simp at hq₁
  have hp₂0 : p₂ ≠ 0 := by intro h0; rw [h0] at hp₂; simp at hp₂
  have hq₂0 : q₂ ≠ 0 := by intro h0; rw [h0] at hq₂; simp at hq₂
  -- weights
  obtain ⟨K₁, hK₁⟩ := leibt_wt_finite (d := d) p₁
  obtain ⟨K₂, hK₂⟩ := leibt_wt_finite (d := d) p₂
  obtain ⟨K₃, hK₃⟩ := leibt_wt_finite (d := d) r
  set K : ℕ := K₁ + K₂ + K₃ with hK
  have hw₁ : eLpNorm (leibt_wt d K) p₁ volume ≠ ⊤ := (hK₁ K (by omega)).ne
  have hw₂ : eLpNorm (leibt_wt d K) p₂ volume ≠ ⊤ := (hK₂ K (by omega)).ne
  have hw₃ : eLpNorm (leibt_wt d K) r volume ≠ ⊤ := (hK₃ K (by omega)).ne
  -- one function estimates
  obtain ⟨Sf, hSf, hfn⟩ := leibt_one_fn α hη hη1 (leibt_chi hd (e := 1) le_rfl)
    (leibt_chi_cs' hd le_rfl) K hf
  obtain ⟨Sg, hSg, hgn⟩ := leibt_one_fn α hη hη1 (leibt_chi hd (e := 1) le_rfl)
    (leibt_chi_cs' hd le_rfl) K hg
  obtain ⟨Sh, hSh, hhn⟩ := leibt_one_fn α hη hη1 (leibt_chi hd (e := 2) (by norm_num))
    (leibt_chi_cs' hd (by norm_num)) K hhS
  have hFf := leibt_F0_continuous hη hη1 α hf
  have hFg := leibt_F0_continuous hη hη1 α hg
  have hFh := leibt_F0_continuous hη hη1 α hhS
  have haeF : eLpNorm F p₁ volume = eLpNorm (leibt_F0 α η f) p₁ volume :=
    eLpNorm_congr_ae (leibt_bessel_ae hη hη1 α hf hFi hrF)
  have haeG : eLpNorm G p₂ volume = eLpNorm (leibt_F0 α η g) p₂ volume :=
    eLpNorm_congr_ae (leibt_bessel_ae hη hη1 α hg hGi hrG)
  have haeH : eLpNorm H r volume = eLpNorm (leibt_F0 α η h) r volume :=
    eLpNorm_congr_ae (leibt_bessel_ae hη hη1 α hhS hHi hrH)
  have hXg : eLpNorm g q₁ volume ≠ ⊤ :=
    (hgc.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)).eLpNorm_ne_top
  have hXf : eLpNorm f q₂ volume ≠ ⊤ :=
    (hfc.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)).eLpNorm_ne_top
  rw [haeF, haeG, haeH]
  set XF := eLpNorm (leibt_F0 α η f) p₁ volume with hXF
  set XG := eLpNorm (leibt_F0 α η g) p₂ volume with hXG
  set XH := eLpNorm (leibt_F0 α η h) r volume with hXH
  set Xg := eLpNorm g q₁ volume with hXg'
  set Xf := eLpNorm f q₂ volume with hXf'
  set w₁ := eLpNorm (leibt_wt d K) p₁ volume with hw₁'
  set w₂ := eLpNorm (leibt_wt d K) p₂ volume with hw₂'
  set w₃ := eLpNorm (leibt_wt d K) r volume with hw₃'
  have hκ1 := leibt_kappa_prod (d := d) r p₁ q₁ hp₁0 hq₁0 h1
  have hκ2 := leibt_kappa_prod (d := d) r p₂ q₂ hp₂0 hq₂0 h2
  set D : ℝ≥0∞ := Cl * (ENNReal.ofReal Sf * w₁ * leibt_kappa d q₁ * Xg +
      ENNReal.ofReal Sg * w₂ * leibt_kappa d q₂ * Xf) + ENNReal.ofReal Sh * w₃ with hD
  have hDtop : D ≠ ⊤ := by
    refine ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top hClTop (ENNReal.add_ne_top.2 ⟨?_, ?_⟩),
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top hw₃⟩
    · exact ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hw₁)
        (leibt_kappa_ne_top _)) hXg
    · exact ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hw₂)
        (leibt_kappa_ne_top _)) hXf
  have hmain : XH ≤ Cl * (leibt_kappa d p₁ * leibt_kappa d q₁ * (XF * Xg) +
      leibt_kappa d p₂ * leibt_kappa d q₂ * (XG * Xf)) := by
    refine leibt_limit hDtop fun δ hδ => ?_
    obtain ⟨M₀, hM₀⟩ := exists_nat_ge (1 / δ)
    set M : ℕ := max 1 M₀ with hMdef
    have hM1 : 1 ≤ M := le_max_left _ _
    have hMM : (M₀ : ℝ) ≤ M := by exact_mod_cast le_max_right 1 M₀
    set N : ℝ := ((M : ℝ) + 1 / 2) / η with hN
    set N' : ℝ := ((((2 * d * M + d : ℕ)) : ℝ) + 1 / 2) / η with hN'
    have hN1 : 1 ≤ N := by
      rw [hN, le_div_iff₀ hη]
      have : (1 : ℝ) ≤ M := by exact_mod_cast hM1
      nlinarith
    have hN0 : 0 < N := by linarith
    obtain ⟨Wf, hWf, hEf⟩ := hfn N hN1
    obtain ⟨Wg, hWg, hEg⟩ := hgn N hN1
    obtain ⟨Wh, hWh, hEh⟩ := hhn N hN1
    have hstep := leibt_step_M hd α hη hη1 r p₁ q₁ p₂ q₂ hr hr' hp₁ hq₁ hp₂ hq₂ h1 h2 Cl hCl M hM1
      hN hN' K hh hfc hgc hFf hFg hFh hSf hSg hSh Wf Wg Wh hWf hWg hWh hEf hEg hEh
    refine ⟨N⁻¹, inv_pos.2 hN0, ?_, ?_⟩
    · rw [hN, inv_div, div_le_iff₀ (by positivity)]
      have : 1 / δ ≤ (M : ℝ) := hM₀.trans hMM
      rw [div_le_iff₀ hδ] at this
      nlinarith
    · refine hstep.trans (le_of_eq ?_)
      rw [ENNReal.ofReal_mul hSf, ENNReal.ofReal_mul hSg, ENNReal.ofReal_mul hSh, hD]
      ring
  -- conclude
  have hκr : leibt_kappa d r ≤ ENNReal.ofReal ((2 * d + 1 : ℝ) ^ d) := by
    unfold leibt_kappa
    have hb : (1 : ℝ≥0∞) ≤ ENNReal.ofReal ((2 * d + 1 : ℝ) ^ d) := by
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal (one_le_pow₀ hc1)
    have he : (r⁻¹).toReal ≤ 1 := by
      have : r⁻¹ ≤ 1 := ENNReal.inv_le_one.2 hr.le
      simpa using ENNReal.toReal_mono ENNReal.one_ne_top this
    calc ENNReal.ofReal ((2 * d + 1 : ℝ) ^ d) ^ (r⁻¹).toReal
        ≤ ENNReal.ofReal ((2 * d + 1 : ℝ) ^ d) ^ (1 : ℝ) := ENNReal.rpow_le_rpow_of_exponent_le hb he
      _ = _ := ENNReal.rpow_one _
  have hCl' : Cl * leibt_kappa d r ≤ ENNReal.ofReal (Cl.toReal * (2 * d + 1 : ℝ) ^ d + 1) := by
    calc Cl * leibt_kappa d r ≤ ENNReal.ofReal Cl.toReal * ENNReal.ofReal ((2 * d + 1 : ℝ) ^ d) := by
          rw [ENNReal.ofReal_toReal hClTop]; gcongr
      _ = ENNReal.ofReal (Cl.toReal * (2 * d + 1 : ℝ) ^ d) := by
          rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg]
      _ ≤ _ := ENNReal.ofReal_le_ofReal (by linarith)
  rw [hκ1, hκ2] at hmain
  calc XH ≤ Cl * (leibt_kappa d r * (XF * Xg) + leibt_kappa d r * (XG * Xf)) := hmain
    _ = (Cl * leibt_kappa d r) * (XF * Xg + XG * Xf) := by ring
    _ ≤ _ := by gcongr

end HRS.Commutator.TorusNote
