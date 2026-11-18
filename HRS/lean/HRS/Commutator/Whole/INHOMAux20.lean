import HRS.Commutator.Whole.INHOMAux19

/-!
# CMX-INHOM auxiliary 20: the low-frequency transport does not see the high-frequency kernel
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform ContDiff Convolution

namespace HRS.Commutator.Whole

open HRS HRS.Whole

variable {d : ℕ} {s : ℝ}

lemma inhom_temperate_of_schwartz {φ₀ : SchwartzMap (Euc d) ℂ} {a₀ : Euc d → ℝ}
    (hφ₀ : ∀ x, φ₀ x = ((a₀ x : ℝ) : ℂ)) : Function.HasTemperateGrowth a₀ := by
  have h := Complex.reCLM.hasTemperateGrowth.comp φ₀.hasTemperateGrowth
  have e : a₀ = Complex.reCLM ∘ ⇑φ₀ := by
    funext x; simp [hφ₀ x]
  rw [e]; exact h

lemma inhom_fs_a0 {a a₀ : Euc d → ℝ} (hd : 1 ≤ d) (hac : Continuous a) {M : ℝ}
    (hM : ∀ x, |a x| ≤ M) (ha₀ : ∀ x, a₀ x = Pleq (1 / 16) a x) :
    FourierSuppIn (2 * (1 / 16)) a₀ := by
  have : a₀ = Pleq (1 / 16) a := funext ha₀
  rw [this]
  exact Pleq_fourierSupp hd (1 / 16) (by norm_num) a |M| (fun x => by
    calc |a x| ≤ |M| := (hM x).trans (le_abs_self M)
      _ ≤ |M| * (1 + ‖x‖) := by nlinarith [norm_nonneg x, abs_nonneg M]) hac.measurable

theorem inhom_cross_low (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2)
    {φ φ₀ φ₁ : SchwartzMap (Euc d) ℂ} {a a₀ a₁ : Euc d → ℝ}
    (hφ₀ : ∀ x, φ₀ x = ((a₀ x : ℝ) : ℂ)) (hφ₁ : ∀ x, φ₁ x = ((a₁ x : ℝ) : ℂ))
    (hφ : ∀ x, φ x = ((a x : ℝ) : ℂ)) (ha₀ : ∀ x, a₀ x = Pleq (1 / 16) a x)
    (f : Euc d → ℝ) (hfc : Continuous f) {Cf : ℝ} (hCf : ∀ x, |f x| ≤ Cf * (1 + ‖x‖)) (i : Fin d) :
    ∫ x, a₀ x * Pleq (1 / 16) f x * inhom_conv (ghiForce s) a₁ x i = 0 := by
  obtain ⟨hac, -, ⟨M, hM⟩, -, -⟩ := inhom_schw_props hφ
  obtain ⟨c, hc⟩ := inhom_conv_schwartz hd hs0 hsd (s := s)
  obtain ⟨Θ, hΘx, hΘF⟩ := hc i φ₁ a₁ hφ₁
  have hfsu : FourierSuppIn (2 * (1 / 16)) (Pleq (1 / 16) f) :=
    Pleq_fourierSupp (by omega) (1 / 16) (by norm_num) f Cf hCf hfc.measurable
  have hfs0 := inhom_fs_a0 (by omega) hac hM ha₀
  have hprod := lowv_prod_fsupp (R1 := 2 * (1 / 16)) (R2 := 2 * (1 / 16)) (by norm_num) (by norm_num)
    (inhom_temperate_of_schwartz hφ₀) hfsu hfs0
  have hz : ∀ ξ : Euc d, ‖ξ‖ < 1 → 𝓕 (⇑Θ) ξ = 0 := by
    intro ξ hξ
    rw [hΘF ξ]
    have : chi ξ = 1 := cmxFB_chi_one hξ.le
    unfold inhom_M
    rw [this]; simp
  have h0 := lowv_fs_apply hprod Θ (r := 1) (by norm_num) hz
  have h1 : ((∫ x, a₀ x * Pleq (1 / 16) f x * inhom_conv (ghiForce s) a₁ x i : ℝ) : ℂ) = 0 := by
    rw [← integral_complex_ofReal, ← h0]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    beta_reduce
    rw [← hΘx x]
    push_cast
    ring
  exact_mod_cast h1

end HRS.Commutator.Whole
