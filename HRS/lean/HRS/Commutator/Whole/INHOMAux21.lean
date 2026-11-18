import HRS.Commutator.Whole.INHOMAux20

/-!
# CMX-INHOM auxiliary 21: the cross term, one component at a time
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform ContDiff Convolution

namespace HRS.Commutator.Whole

open HRS HRS.Whole

variable {d : ℕ} {s : ℝ}

lemma inhom_holder12_lint {f g : Euc d → ℝ} (hf : AEStronglyMeasurable f volume)
    (hg : AEStronglyMeasurable g volume) :
    ∫⁻ x, ‖f x * g x‖ₑ ≤ eLpNorm f 2 volume * eLpNorm g 2 volume := by
  have h2 := eLpNorm_smul_le_mul_eLpNorm (p := 2) (q := 2) (r := 1) hf hg
  have hm : AEStronglyMeasurable (f • g) volume := hf.smul hg
  rw [eLpNorm_one_eq_lintegral_enorm hm] at h2
  exact h2

lemma inhom_h_props (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2)
    {φ₁ : SchwartzMap (Euc d) ℂ} {a₁ : Euc d → ℝ} (hφ₁ : ∀ x, φ₁ x = ((a₁ x : ℝ) : ℂ)) (i : Fin d) :
    Continuous (fun x => inhom_conv (ghiForce s) a₁ x i) ∧
      ∃ Mh : ℝ, ∀ x, |inhom_conv (ghiForce s) a₁ x i| ≤ Mh := by
  obtain ⟨c, hc⟩ := inhom_conv_schwartz hd hs0 hsd (s := s)
  obtain ⟨Θ, hΘx, -⟩ := hc i φ₁ a₁ hφ₁
  have hre : (fun x => inhom_conv (ghiForce s) a₁ x i) = fun x => (Θ x).re := by
    funext x; rw [← hΘx x]; simp
  obtain ⟨C0, hC00, hC0⟩ := cmxFB_decay Θ 0
  refine ⟨?_, C0, fun x => ?_⟩
  · rw [hre]; exact Complex.continuous_re.comp Θ.continuous
  · rw [← Real.norm_eq_abs, ← Complex.norm_real, hΘx x]
    simpa using hC0 x

lemma inhom_int_aqh {a₀ q h : Euc d → ℝ} (ha1 : Integrable (fun y : Euc d => (1 + ‖y‖) * |a₀ y|) volume)
    (hac : Continuous a₀) (hqc : Continuous q) {Cq : ℝ} (hq : ∀ x, |q x| ≤ Cq * (1 + ‖x‖))
    (hhc : Continuous h) {Mh : ℝ} (hh : ∀ x, |h x| ≤ Mh) :
    Integrable (fun x => a₀ x * q x * h x) volume := by
  have hCq : 0 ≤ Cq := by
    have := hq 0; simp at this; exact (abs_nonneg _).trans this
  have hMh : 0 ≤ Mh := (abs_nonneg _).trans (hh 0)
  refine (ha1.const_mul (Cq * Mh)).mono' ((hac.mul hqc).mul hhc).aestronglyMeasurable
    (Eventually.of_forall fun x => ?_)
  rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs]
  calc |a₀ x| * |q x| * |h x| ≤ |a₀ x| * (Cq * (1 + ‖x‖)) * Mh := by gcongr; exact hq x; exact hh x
    _ = (Cq * Mh) * ((1 + ‖x‖) * |a₀ x|) := by ring

end HRS.Commutator.Whole
