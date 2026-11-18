import HRS.Commutator.Whole.INHOMAux13

/-!
# CMX-INHOM auxiliary 14: the `low_velocity` term for the high-frequency part `a₁`
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform ContDiff Convolution

namespace HRS.Commutator.Whole

open HRS HRS.Whole

variable {d : ℕ} {s : ℝ}

lemma inhom_Pleq_props : ∃ M : ℝ, 0 ≤ M ∧ ∀ (v : Euc d → Euc d) (L : ℝ≥0), LipschitzWith L v →
    Continuous (Pleq 1 v) ∧ (∀ x y, ‖Pleq 1 v x - Pleq 1 v y‖ ≤ (M * L) * ‖x - y‖) ∧
    Continuous (Pgt 1 v) ∧ (∀ x y, ‖Pgt 1 v x - Pgt 1 v y‖ ≤ ((1 + M) * L) * ‖x - y‖) := by
  obtain ⟨Mq, hMq0, hMq⟩ := inhom_Pleq_lipschitz (d := d)
  refine ⟨Mq, hMq0, fun v L hL => ?_⟩
  have hvc : Continuous v := hL.continuous
  have hV1c : Continuous (Pleq 1 v) := by
    refine continuous_iff_continuousAt.2 fun x => ?_
    refine Metric.continuousAt_iff.2 fun ε hε => ?_
    have hc : 0 < Mq * L + 1 := by positivity
    refine ⟨ε / (Mq * L + 1), by positivity, fun y hy => ?_⟩
    rw [dist_eq_norm] at hy ⊢
    calc ‖Pleq 1 v y - Pleq 1 v x‖ ≤ Mq * L * ‖y - x‖ := hMq v L hL y x
      _ ≤ (Mq * L + 1) * ‖y - x‖ := by gcongr; linarith
      _ < (Mq * L + 1) * (ε / (Mq * L + 1)) := by gcongr
      _ = ε := by field_simp
  have hV : ∀ x y, ‖v x - v y‖ ≤ L * ‖x - y‖ := fun x y => by
    simpa [dist_eq_norm] using hL.dist_le_mul x y
  have hV1 : ∀ x y, ‖Pleq 1 v x - Pleq 1 v y‖ ≤ (Mq * L) * ‖x - y‖ := fun x y => hMq v L hL x y
  refine ⟨hV1c, hV1, ?_, fun x y => ?_⟩
  · have : (Pgt 1 v : Euc d → Euc d) = fun x => v x - Pleq 1 v x := rfl
    rw [this]; exact hvc.sub hV1c
  · have : Pgt 1 v x - Pgt 1 v y = (v x - v y) - (Pleq 1 v x - Pleq 1 v y) := by
      simp only [Pgt]; abel
    rw [this]
    calc ‖(v x - v y) - (Pleq 1 v x - Pleq 1 v y)‖ ≤ ‖v x - v y‖ + ‖Pleq 1 v x - Pleq 1 v y‖ :=
          norm_sub_le _ _
      _ ≤ L * ‖x - y‖ + (Mq * L) * ‖x - y‖ := add_le_add (hV x y) (hV1 x y)
      _ = _ := by ring

lemma inhom_lowFreq_norm_le (F : Euc d → ℂ) (ξ : Euc d) : ‖lowFreq 4 F ξ‖ ≤ ‖F ξ‖ := by
  unfold lowFreq
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (cmxFB_chi_nonneg _)]
  calc chi ((4 : ℝ)⁻¹ • ξ) * ‖F ξ‖ ≤ 1 * ‖F ξ‖ := by
        gcongr; exact cmxFB_chi_le_one _
    _ = _ := one_mul _

theorem inhom_T_low (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (v : Euc d → Euc d) (K : ℝ), SubTransport d s v K →
      ∀ (φ ψ : SchwartzMap (Euc d) ℂ) (b : Euc d → ℝ), (∀ x, ψ x = ((b x : ℝ) : ℂ)) →
        (∀ ξ, 𝓕 (⇑ψ) ξ = (1 - cmxFB_gL d (1 / 16) ξ) * 𝓕 (⇑φ) ξ) →
        ENNReal.ofReal |CcommFun (gloForce s) (Pleq 1 v) b| ≤
          ENNReal.ofReal (C * K) * inhom_Sob (-alphaE d s) φ := by
  obtain ⟨Cl, hCl, hlow⟩ := inhom_low_velocity hd hs0 hsd
  obtain ⟨Mq, hMq0, hMq⟩ := inhom_Pleq_props (d := d)
  obtain ⟨hFcd, hF0, hFodd, hFder⟩ := gloForce_props hd hs0 hsd
  obtain ⟨B, hBd⟩ := hFder 0
  have hB : ∀ x, ‖gloForce s x‖ ≤ B := fun x => by simpa using hBd x
  have hα : 0 < alphaE d s := by
    unfold alphaE; have : (3 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  refine ⟨Cl * (1 + 64 / Real.pi ^ 2) ^ alphaE d s, by positivity, fun v K hv φ ψ b hψ hF => ?_⟩
  have hK0 := inhom_subTransport_nonneg hv
  obtain ⟨hac, hai, hM, ha1, ha2⟩ := inhom_schw_props hψ
  have hadm := inhom_ofDensity_admissible hψ
  have hmass : s = 0 → (SMeas.ofDensity b).mass = 0 := fun _ => by
    rw [inhom_ofDensity_mass hac.measurable ha1]; exact inhom_mass_zero hψ hF
  have h1 := hlow v K hv (SMeas.ofDensity b) hadm hmass
  obtain ⟨L, F, hF0, hL, -, hK⟩ := hv
  obtain ⟨hV1c, hV1, -, -⟩ := hMq v L hL
  have hbr := inhom_Ccomm_ofDensity (hFc := hFcd.continuous) hB hV1c hV1 (by positivity) hac hai
  rw [hbr] at h1
  have h2 : homSqE (-alphaE d s) (lowFreq 4 (SMeas.ofDensity b).fourier) ≤
      ENNReal.ofReal ((1 + 64 / Real.pi ^ 2) ^ alphaE d s) * inhom_Sob (-alphaE d s) φ := by
    refine inhom_hom_le hα _ (fun ξ => ?_)
    refine (inhom_lowFreq_norm_le _ ξ).trans ?_
    rw [inhom_ofDensity_fourier hac.measurable ha1 ξ]
    have : (fun x : Euc d => ((b x : ℝ) : ℂ)) = ⇑ψ := by funext x; rw [hψ x]
    rw [this, hF ξ, norm_mul]
  refine h1.trans ?_
  calc ENNReal.ofReal (Cl * K) * homSqE (-alphaE d s) (lowFreq 4 (SMeas.ofDensity b).fourier)
      ≤ ENNReal.ofReal (Cl * K) * (ENNReal.ofReal ((1 + 64 / Real.pi ^ 2) ^ alphaE d s) *
          inhom_Sob (-alphaE d s) φ) := by gcongr
    _ = ENNReal.ofReal (Cl * (1 + 64 / Real.pi ^ 2) ^ alphaE d s * K) * inhom_Sob (-alphaE d s) φ := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
        congr 2; ring

end HRS.Commutator.Whole
