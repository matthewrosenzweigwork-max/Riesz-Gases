import HRS.MS.R2InterpAux112
import HRS.MS.R2InterpAux102

/-!
# S10.2 (worker S10R), part 113: `r2_path_interpolation` from the three open items `S102Rest` (and `γ > 0`)

The statement is the frozen `HRS.Whole.r2_path_interpolation` with the hypotheses `hγ : 0 ≤ γ`, `hγs` replaced by `0 < γ` (the corner `γ = 0 = s` is open, see `HANDOFF_S10R.md`)
and the extra hypothesis `hrest : S102Rest ...`.  When `hrest` is proved the tie `R2InterpTie` follows by `r2_path_interpolation_proof := r2_path_interpolation_of_rest ... hrest`.
-/

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.R2Interp

open HRS HRS.Whole HRS.MS.CovMeas

set_option maxSynthPendingDepth 3 in
set_option maxHeartbeats 1600000 in
theorem r2_path_interpolation_of_rest {d : ℕ} (hd : 2 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) (a β γ : ℝ)
    (ha : 0 < a) (hβ : 0 < β) (hγ : 0 < γ) (T : ℝ) (hT : 0 < T)
    (ρ : Euc d → ℝ) (hρ : HRS.Whole.IsThermalEquilibrium d s a β ρ)
    (horb : HRS.Whole.R2OrbitSummable ((HRS.Whole.quadraticGradientDyn d s a β).coeff (fun _ => ρ)) ((14 * d + 114 : ℕ) : ℝ) T
      (2 * d + 8))
    (γu : ℝ → Measure (OscPath d ((14 * d + 114 : ℕ) : ℝ) T))
    (hγG : ∀ u ∈ Set.Icc (0 : ℝ) T,
      IsR2FutureGaussian ((HRS.Whole.quadraticGradientDyn d s a β).coeff (fun _ => ρ)) ((14 * d + 114 : ℕ) : ℝ) T u (γu u))
    (N : ℕ) (hN : 2 ≤ N) (hinv : HRS.Whole.GibbsInvariant d s a β N)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X₀ : Ω → EucConfig d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → EucConfig d N)
    (hreal : IsR2Realization d s a β P X₀ W X)
    (hlaw : law P X₀ = HRS.Whole.modulatedGibbs (HRS.Whole.rieszKernel d s) N γ (HRS.Whole.withDensityReal ρ))
    (Φ : OscPath d ((14 * d + 114 : ℕ) : ℝ) T → ℝ) (hΦ : MemCb 5 Φ)
    (hrest : S102Rest ((HRS.Whole.quadraticGradientDyn d s a β).coeff (fun _ => ρ)) ((14 * d + 114 : ℕ) : ℝ) T
      (2 * d + 8) ((d : ℝ) + 2) s (HRS.Whole.withDensityReal ρ) hT P X) :
    ∃ A J : Ω → ℝ, Integrable A P ∧ Integrable J P ∧
      (∀ᵐ ζ ∂P, IsR2RS T (fun τ a' b' =>
        fderiv ℝ (r2HeatFn γu Φ τ)
          (r2Predicted ((HRS.Whole.quadraticGradientDyn d s a β).coeff (fun _ => ρ))
            (zetaPathW ((14 * d + 114 : ℕ) : ℝ) T 0 P X ζ)
            (fun u f => Real.sqrt N * (HRS.Whole.pair (HRS.Whole.empirical (X u.toNNReal ζ)) f - HRS.Whole.pair (HRS.Whole.meanEmpirical (P.map (X u.toNNReal))) f)) τ)
          (r2DriftInc ((HRS.Whole.quadraticGradientDyn d s a β).coeff (fun _ => ρ)) ((14 * d + 114 : ℕ) : ℝ) T
            (fun u => r2QuadField s (HRS.Whole.withDensityReal ρ) P X u ζ) a' b')) (A ζ)) ∧
      (∀ᵐ ζ ∂P, IsR2RS T (fun τ a' b' =>
        r2JPair ((HRS.Whole.quadraticGradientDyn d s a β).coeff (fun _ => ρ)) ((14 * d + 114 : ℕ) : ℝ) T
          (fun u f => Real.sqrt N * (HRS.Whole.pair (HRS.Whole.empirical (X u.toNNReal ζ)) f - HRS.Whole.pair (HRS.Whole.withDensityReal ρ) f))
          (Set.Ioc a' b')
          (iteratedFDeriv ℝ 2 (r2HeatFn γu Φ τ)
            (r2Predicted ((HRS.Whole.quadraticGradientDyn d s a β).coeff (fun _ => ρ))
              (zetaPathW ((14 * d + 114 : ℕ) : ℝ) T 0 P X ζ)
              (fun u f => Real.sqrt N * (HRS.Whole.pair (HRS.Whole.empirical (X u.toNNReal ζ)) f - HRS.Whole.pair (HRS.Whole.meanEmpirical (P.map (X u.toNNReal))) f)) τ))) (J ζ)) ∧
      ∫ ζ, Φ (zetaPathW ((14 * d + 114 : ℕ) : ℝ) T 0 P X ζ) ∂P =
        ∫ ζ, r2HeatFn γu Φ 0 (r2InitProp ((HRS.Whole.quadraticGradientDyn d s a β).coeff (fun _ => ρ))
            ((14 * d + 114 : ℕ) : ℝ) T
            (fun f => Real.sqrt N * (HRS.Whole.pair (HRS.Whole.empirical (X 0 ζ)) f - HRS.Whole.pair (HRS.Whole.meanEmpirical (P.map (X 0))) f))) ∂P -
          (Real.sqrt N)⁻¹ * ∫ ζ, A ζ ∂P + (1 / (2 * Real.sqrt N)) * ∫ ζ, J ζ ∂P := by
  classical
  have hd1 : 1 ≤ d := by omega
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  obtain ⟨c, hDc⟩ := s101_data_of_horb hd1 horb
  have hstd := s102_std_thermal hd hs0 hs ha hβ hρ ((14 * d + 114 : ℕ) : ℝ) T hT.le hDc
  have hlin := s102_lin_thermal hd hs0 hs ha hβ hρ ((14 * d + 114 : ℕ) : ℝ) T hT.le
  obtain ⟨M, L, c₁, hRD, hGU⟩ := HRS.MS.R2S11.s11_thermal_round2 hd hs0 hs ha hβ hρ
  obtain ⟨Mρ, hMi, hMle⟩ := s102_mom_conv hρ.2.1 hGU (a := 2 * (((d : ℝ)) + 2)) (by positivity)
  obtain ⟨ℱ, W', hF⟩ := hreal.filtered
  have hF' := s102_shift_filtered hF
  have hpartF := s102_part_of_rest hd s hs0 hs a β γ ha hβ hγ T hT ρ hρ horb ⟨γu, hγG⟩ N hN hinv P X₀ W X hreal hlaw hrest
    (s102_shift ℱ) W' hF' (fun t ht => s102_shift_neg ℱ ht)
  have hμ : ∀ u ∈ Set.Icc (0 : ℝ) T, ∀ g : Euc d → ℝ,
      HRS.Whole.pair (HRS.Whole.withDensityReal ρ) g =
        ∫ x, g x * ((HRS.Whole.quadraticGradientDyn d s a β).coeff (fun _ => ρ)).ρ u x := by
    intro u _ g
    rw [HRS.Whole.Q09A.pair_withDensityReal hρ.2.1 g]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [WholeDyn.coeff]
    ring
  have hr : (d : ℝ) / 2 + 1 < ((2 * d + 8 : ℕ) : ℝ) := by push_cast; linarith
  have hP : (d : ℝ) < 2 * ((d : ℝ) + 2) := by linarith
  exact s102_main_of_part hstd hd1 (by positivity) hr hP hlin hT s (HRS.Whole.withDensityReal ρ) hμ Mρ
    (fun u _ => ⟨hMi, hMle⟩) γu hγG (by omega) P X hpartF hΦ

end HRS.MS.R2Interp

end
