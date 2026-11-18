import HRS.Commutator.Whole.LocalAuxSAMP11
import HRS.Commutator.Whole.ExternalAuxMult4

/-!
# The kernel `K_α` and cube sampling for `v_{>1}` (packet CMX-SAMP, helper file 12)
-/

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal FourierTransform ContDiff Convolution

noncomputable section

namespace HRS.Commutator.Whole.SAMP1

open HRS HRS.Whole HRS.Commutator.Whole

variable {d : ℕ} {s : ℝ}

lemma exponents (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) :
    1 < alphaE d s ∧ alphaE d s < d ∧ 0 < alphaE d s ∧ 1 < p1E d s ∧
      (d : ℝ) < alphaE d s * p1E d s := by
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hq2 : 0 < (d : ℝ) - s - 2 := by linarith
  have h1 : 1 < alphaE d s := by unfold alphaE; linarith
  have h2 : alphaE d s < d := by unfold alphaE; linarith
  have h3 : 1 < p1E d s := by
    unfold p1E; rw [lt_div_iff₀ hq2]; linarith
  refine ⟨h1, h2, by linarith, h3, ?_⟩
  have : alphaE d s * p1E d s = d + 2 * d / ((d : ℝ) - s - 2) := by
    unfold alphaE p1E; field_simp; ring
  rw [this]
  have : 0 < 2 * (d : ℝ) / ((d : ℝ) - s - 2) := by positivity
  linarith

theorem kernel_data (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) :
    ∃ K : Euc d → ℝ, Integrable K ∧
      (∀ ξ : Euc d, 𝓕 (fun x : Euc d => ((K x : ℝ) : ℂ)) ξ =
        (((1 - chi ξ) * (2 * Real.pi * ‖ξ‖) ^ (-alphaE d s) : ℝ) : ℂ)) ∧
      MemLp (fun x : Euc d => K (-x)) (ENNReal.ofReal (p1E d s).conjExponent) volume ∧
      ∃ c : ℝ≥0∞, c ≠ ⊤ ∧ ∀ (W : Euc d → ℝ≥0∞), Measurable W → ∀ u : Euc d → ℝ≥0∞,
        (∀ x, u x ≤ ∫⁻ y, ‖K (-(x - y))‖ₑ * W y) →
        (∑' j : Fin d → ℤ, (⨆ x ∈ cubeS d j, u x) ^ (p1E d s)) ^ (1 / p1E d s) ≤
          c * (∫⁻ y, W y ^ (p1E d s)) ^ (1 / p1E d s) := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨hα1, hαd, hα0, hp1, hαp⟩ := exponents hd hs0 hsd
  obtain ⟨K, hK, hKF, ⟨C₁, hC₁, hnear⟩, hfar⟩ :=
    cmxMY_mult_kernel_bounds hd1 (alphaE d s) hα0 (by exact_mod_cast hαd)
  obtain ⟨C₂, hC₂, hfar'⟩ := hfar (d + 1)
  have hKm : AEStronglyMeasurable (fun x : Euc d => K (-x)) volume :=
    hK.1.comp_measurePreserving (Measure.measurePreserving_neg volume)
  have hK1 : ∀ x : Euc d, x ≠ 0 → ‖x‖ ≤ 1 → |K (-x)| ≤ C₁ * ‖x‖ ^ (alphaE d s - d) := by
    intro x hx hx1
    have := hnear (-x) (neg_ne_zero.2 hx) (by simpa using hx1)
    simpa using this
  have hK2 : ∀ x : Euc d, 1 ≤ ‖x‖ → |K (-x)| ≤ C₂ * ‖x‖ ^ (-((d : ℝ) + 1)) := by
    intro x hx
    have := hfar' (-x) (by simpa using hx)
    simpa [norm_neg] using this
  have hfin := kernel_Lq_lt_top hd1 hp1 hαp hKm hK1 hK2
  refine ⟨K, hK, hKF, ?_, ?_⟩
  · rw [memLp_iff, eLpNorm_eq_lintegral_rpow_enorm_toReal
      (ENNReal.ofReal_pos.2 (by have := (Real.HolderConjugate.conjExponent hp1).symm.pos; exact this)).ne'
      ENNReal.ofReal_ne_top hKm,
      ENNReal.toReal_ofReal (Real.HolderConjugate.conjExponent hp1).symm.pos.le]
    exact ENNReal.rpow_lt_top_of_nonneg (by
      have := (Real.HolderConjugate.conjExponent hp1).symm.pos
      positivity) hfin.ne
  · obtain ⟨c, hc, hcs⟩ := cube_sampling_abstract hd1 hp1 hαp hKm hK1 hK2
    exact ⟨c, hc, fun W hW u hu => hcs W hW u hu⟩

end HRS.Commutator.Whole.SAMP1
