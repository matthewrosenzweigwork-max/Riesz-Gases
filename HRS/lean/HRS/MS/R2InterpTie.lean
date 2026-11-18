import HRS.MS.R2InterpAux113
import HRS.MS.R2InterpAux136

/-!
# S10.2 (worker S10S): the tie for `HRS.Whole.r2_path_interpolation` (Proposition 10.2)

`r2_path_interpolation_proof` is the frozen statement.  Proof: the `L^p` density of the time marginals (`s102_time_density` for `γ > 0`; for the corner `γ = 0`, which forces
`s = 0`, `s102_time_density_log` from the log-gas normalizer at small negative inverse temperature), then `S102Rest` (M1 `s102_M1` and continuity of the predicted path `s102_M3`,
`s102_rest_proof`), `S102Part` (`s102_part_of_rest_gen`) and the main assembly `s102_main_of_part`, as in `r2_path_interpolation_of_rest` (Aux113).
-/

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.R2Interp

open HRS HRS.Whole HRS.MS.CovMeas

set_option maxSynthPendingDepth 3 in
set_option maxHeartbeats 3200000 in
theorem r2_path_interpolation_proof {d : ℕ} (hd : 2 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) (a β γ : ℝ)
    (ha : 0 < a) (hβ : 0 < β) (hγ : 0 ≤ γ) (hγs : 0 < s → 0 < γ) (T : ℝ) (hT : 0 < T)
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
    (Φ : OscPath d ((14 * d + 114 : ℕ) : ℝ) T → ℝ) (hΦ : MemCb 5 Φ) :
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
  have hdenP : ∃ p K : ℝ, 1 < p ∧ ∀ t : ℝ≥0, (t : ℝ) ≤ T →
      HasR2ActualDensity s β p K (HRS.Whole.withDensityReal ρ) (P.map (X t)) := by
    by_cases hγpos : 0 < γ
    · exact s102_time_density hd hs0 hs ha hβ hγpos hρ hN hinv P X₀ W X hreal ℱ W' hF hlaw T
    · have hγ00 : γ = 0 := le_antisymm (not_lt.1 hγpos) hγ
      have hs00 : s = 0 := by
        rcases hs0.lt_or_eq with h | h
        · exact absurd hγ00 (hγs h).ne'
        · exact h.symm
      subst hs00
      subst hγ00
      exact s102_time_density_log hd ha hβ hρ hN hinv P X₀ W X hreal ℱ W' hF hlaw T
  have hrest := s102_rest_proof hd s hs0 hs a β ha hβ T hT ρ hρ horb N hN P X₀ W X hreal ℱ W' hF hdenP
  have hpartF := s102_part_of_rest_gen hd s hs0 hs a β ha hβ T hT ρ hρ horb ⟨γu, hγG⟩ N hN P X₀ W X hreal hdenP hrest
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

example := (@HRS.MS.R2Interp.r2_path_interpolation_proof : type_of% @HRS.Whole.r2_path_interpolation)

end
