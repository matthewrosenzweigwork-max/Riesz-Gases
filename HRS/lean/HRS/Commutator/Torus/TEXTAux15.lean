import HRS.Commutator.Torus.TEXTAux14

/-!
# T-EXT-A helpers, part 15: the periodised reproducing kernel at scale `η`
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform

namespace HRS.Commutator.TorusNote

open HRS

variable {d : ℕ}

lemma text_psiL_props (R : ℝ) (hR : 0 < R) :
    Continuous (Whole.psiL (d := d) R) ∧ Integrable (Whole.psiL (d := d) R) ∧
      (∃ Bs : ℝ, 0 ≤ Bs ∧ ∀ z, |Whole.psiL (d := d) R z| ≤ Bs) ∧
      (∀ N : ℕ, ∃ A : ℝ, 0 ≤ A ∧ ∀ z : Euc d, z ≠ 0 → |Whole.psiL (d := d) R z| ≤ A * ‖z‖ ^ (-(N : ℝ))) ∧
      (∀ ξ : Euc d, 𝓕 (fun x : Euc d => ((Whole.psiL (d := d) R x : ℝ) : ℂ)) ξ =
        ((Whole.chi (R⁻¹ • ξ) : ℝ) : ℂ)) := by
  set Om := Whole.cmxFB_Om (d := d) R hR with hOm
  have hOmap : ∀ x, Om x = ((Whole.psiL (d := d) R x : ℝ) : ℂ) := fun x => Whole.cmxFB_Om_apply hR x
  have hnorm : ∀ x, ‖Om x‖ = |Whole.psiL (d := d) R x| := fun x => by
    rw [hOmap, Complex.norm_real, Real.norm_eq_abs]
  have hcont : Continuous (Whole.psiL (d := d) R) := by
    have : Continuous (fun x => (Om x).re) := Complex.continuous_re.comp Om.continuous
    refine this.congr fun x => ?_
    rw [hOmap]; simp
  refine ⟨hcont, ?_, ?_, ?_, ?_⟩
  · have hOmint : Integrable (⇑Om) (volume : Measure (Euc d)) := Om.integrable
    have h := hOmint.norm
    refine (integrable_norm_iff hcont.aestronglyMeasurable).1 ?_
    simpa [Real.norm_eq_abs, hnorm] using h
  · obtain ⟨_, hdec⟩ := Whole.cmxHLS_schwartz_dec Om
    obtain ⟨C, hC0, hC⟩ := hdec 0 0
    refine ⟨C, hC0, fun z => ?_⟩
    have := hC z
    simp only [pow_zero, one_mul, norm_iteratedFDeriv_zero] at this
    rw [← hnorm]; exact this
  · intro N
    obtain ⟨_, hdec⟩ := Whole.cmxHLS_schwartz_dec Om
    obtain ⟨C, hC0, hC⟩ := hdec 0 N
    refine ⟨C, hC0, fun z hz => ?_⟩
    have h1 := hC z
    simp only [norm_iteratedFDeriv_zero] at h1
    have hzpos : 0 < ‖z‖ := norm_pos_iff.2 hz
    have h2 : ‖z‖ ^ N ≤ (1 + ‖z‖) ^ N := pow_le_pow_left₀ hzpos.le (by linarith) N
    have h3 : ‖z‖ ^ N * |Whole.psiL (d := d) R z| ≤ C := by
      rw [← hnorm]
      exact (mul_le_mul_of_nonneg_right h2 (norm_nonneg _)).trans h1
    rw [Real.rpow_neg hzpos.le, Real.rpow_natCast, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
    linarith
  · intro ξ
    have h1 : 𝓕 (⇑Om) = ⇑(Whole.cmxFB_G (d := d) R hR) := by
      rw [← SchwartzMap.fourier_coe, hOm, Whole.cmxFB_fourier_Om]
    have h2 : (⇑Om) = fun x : Euc d => ((Whole.psiL (d := d) R x : ℝ) : ℂ) := funext hOmap
    rw [h2] at h1
    rw [h1, Whole.cmxFB_G_apply]
    rfl

end HRS.Commutator.TorusNote
