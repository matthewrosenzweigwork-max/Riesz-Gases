import HRS.MS.R2InterpAux132
import HRS.MS.R2QtAux1
import HRS.MS.S113EndAux32

/-!
# S10.2 (worker S10S), part 133 (packet C1): the quench density bound for a general exponent, and for `b₀ = 0` in the logarithmic case

`s102_quench_gen`: the second half of `s92_quench_density` (S9.3) for arbitrary `p > 1`, `b₀` and normalizer bounds at `b`, `b₀`, `b' = b + p(b₀-b)`.
For the corner `γ = 0 = s` of `r2_path_interpolation` (`b₀ = 0`, so `b' = -(p-1) b < 0`), `s113x_X4_generic` (S11X, the log-gas normalizer at small negative
inverse temperature) supplies the bound at `b'`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open MeasureTheory ProbabilityTheory Function Set Filter
open scoped ENNReal NNReal Topology

noncomputable section

namespace HRS.MS.R2Interp

open HRS HRS.Whole HRS.MS.Wr HRS.MS.PrepStat HRS.MS.R2Mt

variable {d N : ℕ}

theorem s102_quench_gen {s b b₀ p C0 : ℝ} (hp1 : 1 < p) {μ : Measure (Euc d)} [IsProbabilityMeasure μ]
    (hWb : GibbsWellDefined (fun x y => rieszKernel d s (x - y)) N b μ)
    (hW0 : GibbsWellDefined (fun x y => rieszKernel d s (x - y)) N b₀ μ)
    (hW' : GibbsWellDefined (fun x y => rieszKernel d s (x - y)) N (b + p * (b₀ - b)) μ)
    (hlb : |Real.log (pairNormalizer (fun x y => rieszKernel d s (x - y)) N b μ)| ≤ C0)
    (hl0 : |Real.log (pairNormalizer (fun x y => rieszKernel d s (x - y)) N b₀ μ)| ≤ C0)
    (hl' : |Real.log (pairNormalizer (fun x y => rieszKernel d s (x - y)) N (b + p * (b₀ - b)) μ)| ≤ C0)
    (κ : Kernel (EucConfig d N) (EucConfig d N)) (hκ : IsMarkovKernel κ)
    (hinv : (HRS.Whole.modulatedGibbs (rieszKernel d s) N b μ).bind κ =
      HRS.Whole.modulatedGibbs (rieszKernel d s) N b μ) :
    HasR2ActualDensity s b p (Real.exp (2 * C0)) μ
      ((HRS.Whole.modulatedGibbs (rieszKernel d s) N b₀ μ).bind κ) := by
  set b' : ℝ := b + p * (b₀ - b) with hb'
  have hGm := wr9_rieszKernel_pair_meas (d := d) s
  have hQeq : ∀ β : ℝ, HRS.Whole.modulatedGibbs (rieszKernel d s) N β μ =
      pairGibbs (fun x y => rieszKernel d s (x - y)) N β μ := fun β => rfl
  unfold HasR2ActualDensity
  rw [hQeq b] at hinv ⊢
  rw [hQeq b₀]
  haveI hQprob : IsProbabilityMeasure (pairGibbs (fun x y => rieszKernel d s (x - y)) N b μ) := wr9_gibbs_prob hWb
  haveI hQ0prob : IsProbabilityMeasure (pairGibbs (fun x y => rieszKernel d s (x - y)) N b₀ μ) := wr9_gibbs_prob hW0
  have ht := s32_tilt (G := fun x y => rieszKernel d s (x - y)) (N := N) (μ := μ) (a := b₀) (b := b) hGm hW0 hWb
  set φ0 : EucConfig d N → ℝ≥0∞ := fun X => ENNReal.ofReal
    (pairNormalizer (fun x y => rieszKernel d s (x - y)) N b μ /
      pairNormalizer (fun x y => rieszKernel d s (x - y)) N b₀ μ *
      Real.exp ((-b₀ * N - -b * N) * pairEnergy (fun x y => rieszKernel d s (x - y)) X μ)) with hφ0
  have hφ0m : Measurable φ0 :=
    ENNReal.measurable_ofReal.comp (measurable_const.mul (Real.measurable_exp.comp
      (measurable_const.mul (wr9_measurable_pairEnergy hGm))))
  haveI hprobW : IsProbabilityMeasure ((pairGibbs (fun x y => rieszKernel d s (x - y)) N b μ).withDensity φ0) := by
    rw [ht]; exact hQ0prob
  obtain ⟨hac, hLp⟩ := s92_markov_Lp (pairGibbs (fun x y => rieszKernel d s (x - y)) N b μ) κ hinv hφ0m (hp1)
  rw [ht] at hac hLp
  have hpow := s92_tilt_power (N := N) hGm (b0 := b₀) (by linarith : 0 < p) hWb hW0 hW'
  have hconst := s92_power_const_le (K := pairNormalizer (fun x y => rieszKernel d s (x - y)) N b μ) hp1 hWb.normalizer_pos
    hW0.normalizer_pos hW'.normalizer_pos hlb hl0 hl' rfl
  have hint : ∫⁻ X, φ0 X ^ p ∂(pairGibbs (fun x y => rieszKernel d s (x - y)) N b μ) ≤
      ENNReal.ofReal (Real.exp (2 * p * C0)) := by
    refine (le_of_eq hpow).trans (ENNReal.ofReal_le_ofReal hconst)
  have hP : IsProbabilityMeasure
      ((pairGibbs (fun x y => rieszKernel d s (x - y)) N b₀ μ).bind κ) :=
    ⟨by rw [Measure.bind_apply MeasurableSet.univ κ.measurable.aemeasurable]; simp⟩
  refine ⟨hP, hac, ?_⟩
  have hψ : Measurable (((pairGibbs (fun x y => rieszKernel d s (x - y)) N b₀ μ).bind κ).rnDeriv
      (pairGibbs (fun x y => rieszKernel d s (x - y)) N b μ)) := Measure.measurable_rnDeriv _ _
  have hp0 : 0 < p := by linarith
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simpa using hp0) ENNReal.ofReal_ne_top
    (hψ.ennreal_toReal.aestronglyMeasurable), ENNReal.toReal_ofReal hp0.le]
  have h1 : ∫⁻ X, ‖(((pairGibbs (fun x y => rieszKernel d s (x - y)) N b₀ μ).bind κ).rnDeriv
      (pairGibbs (fun x y => rieszKernel d s (x - y)) N b μ) X).toReal‖ₑ ^ p
        ∂(pairGibbs (fun x y => rieszKernel d s (x - y)) N b μ) =
      ∫⁻ X, (((pairGibbs (fun x y => rieszKernel d s (x - y)) N b₀ μ).bind κ).rnDeriv
        (pairGibbs (fun x y => rieszKernel d s (x - y)) N b μ) X) ^ p
        ∂(pairGibbs (fun x y => rieszKernel d s (x - y)) N b μ) := by
    refine lintegral_congr_ae ?_
    filter_upwards [Measure.rnDeriv_lt_top ((pairGibbs (fun x y => rieszKernel d s (x - y)) N b₀ μ).bind κ)
      (pairGibbs (fun x y => rieszKernel d s (x - y)) N b μ)] with x hx
    rw [← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hx.ne]
  rw [h1]
  calc _ ≤ (ENNReal.ofReal (Real.exp (2 * p * C0))) ^ (1 / p) :=
        ENNReal.rpow_le_rpow (hLp.trans hint) (by positivity)
    _ = ENNReal.ofReal (Real.exp (2 * C0)) := by
        rw [ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le (by positivity), ← Real.exp_mul]
        congr 2; field_simp

end HRS.MS.R2Interp

end
