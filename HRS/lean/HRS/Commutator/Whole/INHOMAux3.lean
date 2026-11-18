import HRS.Commutator.Whole.INHOMAux2

/-!
# CMX-INHOM auxiliary 3: the low/high frequency splitting `a = a₀ + a₁` of a real Schwartz function
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform ContDiff

namespace HRS.Commutator.Whole

open HRS HRS.Whole

variable {d : ℕ}

lemma inhom_psiL_bdd {L : ℝ} (hL : 0 < L) : ∃ M : ℝ, ∀ y : Euc d, |psiL L y| ≤ M := by
  obtain ⟨C, hC0, hC⟩ := cmxFB_decay (cmxFB_Om (d := d) L hL) 0
  refine ⟨C, fun y => ?_⟩
  have := hC y
  rw [lowv_norm_Om hL y] at this
  simpa using this

lemma inhom_Pleq_eq {L : ℝ} {a : Euc d → ℝ} (x : Euc d) :
    Pleq L a x = ∫ z, a z * psiL L (x - z) := by
  unfold Pleq
  have := integral_sub_left_eq_self (fun y => psiL L y • a (x - y)) volume x
  simp only [sub_sub_cancel, smul_eq_mul] at this
  simp only [smul_eq_mul]
  rw [← this]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  ring

/-- The splitting `a = a₀ + a₁` at the Fourier scale `1/16`. -/
theorem inhom_split {a : Euc d → ℝ} {φ : SchwartzMap (Euc d) ℂ}
    (hφ : ∀ x, φ x = ((a x : ℝ) : ℂ)) :
    ∃ (a₀ : Euc d → ℝ) (φ₀ φ₁ : SchwartzMap (Euc d) ℂ),
      (∀ x, a₀ x = Pleq (1 / 16) a x) ∧ (∀ x, φ₀ x = ((a₀ x : ℝ) : ℂ)) ∧
      (∀ x, φ₁ x = ((a x - a₀ x : ℝ) : ℂ)) ∧
      (∀ ξ, 𝓕 (⇑φ₀) ξ = cmxFB_gL d (1 / 16) ξ * 𝓕 (⇑φ) ξ) ∧
      (∀ ξ, 𝓕 (⇑φ₁) ξ = (1 - cmxFB_gL d (1 / 16) ξ) * 𝓕 (⇑φ) ξ) := by
  obtain ⟨hac, hai, ⟨M, hM⟩, ha1, ha2⟩ := inhom_schw_props hφ
  have hΛ : (0 : ℝ) < 1 / 16 := by norm_num
  have hadm := inhom_ofDensity_admissible hφ
  obtain ⟨φ₀, hφ₀x, hφ₀F⟩ := lowv_a_exists hΛ (SMeas.ofDensity a) hadm
  obtain ⟨Mψ, hMψ⟩ := inhom_psiL_bdd (d := d) hΛ
  have hint : ∀ x : Euc d, ((SMeas.ofDensity a).int fun z => psiL (1 / 16) (x - z)) =
      Pleq (1 / 16) a x := by
    intro x
    rw [inhom_Pleq_eq x, energyAux_int_ofDensity a _ hac.measurable]
    · have hc : Continuous fun z : Euc d => psiL (1 / 16) (x - z) :=
        (lowv_psiL_continuous hΛ).comp (continuous_const.sub continuous_id)
      refine (ha1.mul_bdd (c := Mψ) hc.aestronglyMeasurable (Eventually.of_forall fun z => ?_))
      simpa [Real.norm_eq_abs] using hMψ (x - z)
  refine ⟨fun x => Pleq (1 / 16) a x, φ₀, φ - φ₀, fun x => rfl, fun x => ?_, fun x => ?_, ?_, ?_⟩
  · rw [hφ₀x x, hint x]
  · simp only [sub_apply]
    rw [hφ x, hφ₀x x, hint x]
    push_cast; ring
  · intro ξ
    rw [hφ₀F ξ, inhom_ofDensity_fourier hac.measurable ha1 ξ]
    have : (fun x : Euc d => ((a x : ℝ) : ℂ)) = ⇑φ := by funext x; rw [hφ x]
    rw [this]
  · intro ξ
    have h1 : 𝓕 (⇑(φ - φ₀)) ξ = 𝓕 (⇑φ) ξ - 𝓕 (⇑φ₀) ξ := by
      have := map_sub (SchwartzMap.fourierTransformCLM ℂ) φ φ₀
      have h2 := congrArg (fun T : SchwartzMap (Euc d) ℂ => T ξ) this
      simpa [SchwartzMap.fourier_coe] using h2
    rw [h1, hφ₀F ξ, inhom_ofDensity_fourier hac.measurable ha1 ξ]
    have : (fun x : Euc d => ((a x : ℝ) : ℂ)) = ⇑φ := by funext x; rw [hφ x]
    rw [this]; ring

end HRS.Commutator.Whole
