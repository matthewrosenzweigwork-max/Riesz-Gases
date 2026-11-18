/-
# HRS.ME.FamV (packet V4b): upper bound of `critical_family_sharpness`

`rate_W2_pointwise_upper`: one constant `C` with `W₂(rateLaw, rateGaussian) ≤ C N^{-1/2}` for every `θ ∈ [0,R]`, every thermal density
`ρθ` of `V_θ` and every `N ≥ 2`.  Proof: for given `θ` choose a stationary Gibbs flow (`HRS.MD.EQLawFlow.eq_flow_exists_proof`) and a stationary
Gaussian field (`HRS.Main.stationaryField_exists`) on the window `[0,1]`; the path bound `rate_family_path_bound` (V2) bounds the `W₂` distance of their
path laws by `C₀ N^{-1/2}`; the evaluation map `rateEval` (V3a) has operator norm `K` independent of `θ`, carries the path laws to `rateLaw` (V3a) and
`rateGaussian` (V3b), and does not increase `W₂` by more than the factor `K` (`HRS.Main.wassersteinE_map_clm_le`).
`critical_family_sharpness_upper` integrates the pointwise bound over `[0,R]`.
-/
import HRS.ME.FamVB
import HRS.ME.FamVC
import HRS.ME.FamVD
import HRS.ME.RetProj
import HRS.ME.FamVFinal

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.ME.FamV

theorem rate_W2_pointwise_upper {d : ℕ} (hd : 2 ≤ d) (hs0 : 0 ≤ (d : ℝ) / 2) (hsd : (d : ℝ) / 2 < d)
    (β : ℝ) (hβ : 0 < β) (k : Lattice d) (R : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ θ ∈ Set.Icc (0 : ℝ) R, ∀ ρθ : Torus d → ℝ,
      IsThermalDensity (periodicRiesz d ((d : ℝ) / 2)) (rateV k β θ) β ρθ →
      ∀ N : ℕ, 2 ≤ N →
        wassersteinE 2 (Main.rateLaw d ((d : ℝ) / 2) k β N θ) (Main.rateGaussian d ((d : ℝ) / 2) k β ρθ) ≤
          ENNReal.ofReal (C * (N : ℝ) ^ (-(1 : ℝ) / 2)) := by
  set m : ℝ := 24 * (d : ℝ) + 240 with hmdef
  have hm : 24 * (d : ℝ) + 240 ≤ m := le_rfl
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hm2 : (d : ℝ) < 2 * m := by rw [hmdef]; nlinarith
  have hmmax : max ((d : ℝ) + 1) ((d : ℝ) / 2 + 2) < m := by
    rw [hmdef]; refine max_lt ?_ ?_ <;> nlinarith
  obtain ⟨C₀, hC₀, h⟩ := rate_family_path_bound hd hs0 hsd β hβ k R m hm 1 one_pos
  set L := rateEval d m 1 zero_le_one k with hL
  refine ⟨(‖L‖ + 1) * C₀, by positivity, fun θ hθ ρθ hρθ N hN => ?_⟩
  have hV : Torus.IsSmooth (rateV k β θ) := rateV_isSmooth k β θ
  obtain ⟨Ω, _, P, _, X₀, W, X, hX⟩ :=
    HRS.MD.EQLawFlow.eq_flow_exists_proof hd hs0 hsd (rateV k β θ) hV hβ hN (0 + 1) (by norm_num)
  obtain ⟨Ω', _, P', _, Z, hZ⟩ :=
    Main.stationaryField_exists hd hs0 hsd hβ (rateV k β θ) hV ρθ hρθ m hmmax
  have hX' : HRS.LZ.IsStationaryGibbsFlow P ((d : ℝ) / 2) hs0 hsd (rateV k β θ) β hβ 1 X₀ W X := by
    rwa [zero_add] at hX
  have hW := h θ hθ ρθ hρθ N hN P X₀ W X hX'.flow hX'.filtered hX'.init P' Z hZ
  have hz : AEMeasurable (Main.windowZeta m 1 0 P X) P :=
    HRS.MD.EQInterp.windowZeta_aemeasurable hd hs0 hsd (rateV k β θ) hV hβ hN le_rfl zero_le_one P hX hm2
  have hp : AEMeasurable (Main.windowPath m 1 0 Z) P' :=
    HRS.ME.Ret.aemeasurable_windowPath_Icc P' Z hZ.meas
      (by filter_upwards [hZ.cont] with ω hω using hω.mono Set.Icc_subset_Ici_self)
  haveI : IsProbabilityMeasure (law P (Main.windowZeta m 1 0 P X)) :=
    (Measure.isProbabilityMeasure_map_iff hz).2 inferInstance
  haveI : IsProbabilityMeasure (law P' (Main.windowPath m 1 0 Z)) :=
    (Measure.isProbabilityMeasure_map_iff hp).2 inferInstance
  have h1 := rate_zeta_law hd hs0 hsd hβ k θ hN hm2 zero_le_one P hX
  have h2 := rate_gauss_law hd hs0 hsd hβ k (rateV k β θ) ρθ hV hρθ zero_le_one P' Z hZ
  rw [← h1, ← h2]
  refine (Main.wassersteinE_map_clm_le L 2 (by norm_num) _ _).trans ?_
  calc ENNReal.ofReal ‖L‖ * wassersteinE 2 (law P (Main.windowZeta m 1 0 P X)) (law P' (Main.windowPath m 1 0 Z))
      ≤ ENNReal.ofReal ‖L‖ * ENNReal.ofReal (C₀ * (N : ℝ) ^ (-(1 : ℝ) / 2)) := by gcongr
    _ = ENNReal.ofReal (‖L‖ * (C₀ * (N : ℝ) ^ (-(1 : ℝ) / 2))) :=
        (ENNReal.ofReal_mul (norm_nonneg _)).symm
    _ ≤ ENNReal.ofReal ((‖L‖ + 1) * C₀ * (N : ℝ) ^ (-(1 : ℝ) / 2)) := by
        apply ENNReal.ofReal_le_ofReal
        have : 0 ≤ C₀ * (N : ℝ) ^ (-(1 : ℝ) / 2) := by positivity
        nlinarith [norm_nonneg L]

theorem critical_family_sharpness_upper {d : ℕ} (hd : 2 ≤ d) (hs0 : 0 ≤ (d : ℝ) / 2) (hsd : (d : ℝ) / 2 < d)
    (β : ℝ) (hβ : 0 < β) (k : Lattice d) :
    ∃ C : ℝ, 0 < C ∧ ∀ ρ : ℝ → Torus d → ℝ,
      (∀ θ, IsThermalDensity (periodicRiesz d ((d : ℝ) / 2)) (rateV k β θ) β (ρ θ)) →
      ∀ N : ℕ, 2 ≤ N →
        ∫⁻ θ in Set.Icc (0 : ℝ) (16 * (1 + β * rieszCoeff d ((d : ℝ) / 2) k)),
            wassersteinE 2 (Main.rateLaw d ((d : ℝ) / 2) k β N θ)
              (Main.rateGaussian d ((d : ℝ) / 2) k β (ρ θ)) ≤
          ENNReal.ofReal (C * (N : ℝ) ^ (-(1 : ℝ) / 2)) := by
  set R : ℝ := 16 * (1 + β * rieszCoeff d ((d : ℝ) / 2) k) with hR
  obtain ⟨C₀, hC₀, h⟩ := rate_W2_pointwise_upper hd hs0 hsd β hβ k R
  refine ⟨C₀ * (max R 0 + 1), by positivity, fun ρ hρ N hN => ?_⟩
  have hpt : ∀ θ ∈ Set.Icc (0 : ℝ) R, wassersteinE 2 (Main.rateLaw d ((d : ℝ) / 2) k β N θ)
      (Main.rateGaussian d ((d : ℝ) / 2) k β (ρ θ)) ≤ ENNReal.ofReal (C₀ * (N : ℝ) ^ (-(1 : ℝ) / 2)) :=
    fun θ hθ => h θ hθ (ρ θ) (hρ θ) N hN
  calc ∫⁻ θ in Set.Icc (0 : ℝ) R, wassersteinE 2 (Main.rateLaw d ((d : ℝ) / 2) k β N θ)
          (Main.rateGaussian d ((d : ℝ) / 2) k β (ρ θ))
      ≤ ∫⁻ θ in Set.Icc (0 : ℝ) R, ENNReal.ofReal (C₀ * (N : ℝ) ^ (-(1 : ℝ) / 2)) :=
        setLIntegral_mono' measurableSet_Icc hpt
    _ = ENNReal.ofReal (C₀ * (N : ℝ) ^ (-(1 : ℝ) / 2)) * volume (Set.Icc (0 : ℝ) R) := by
        rw [setLIntegral_const]
    _ ≤ ENNReal.ofReal (C₀ * (N : ℝ) ^ (-(1 : ℝ) / 2)) * ENNReal.ofReal (max R 0 + 1) := by
        gcongr
        rw [Real.volume_Icc]
        apply ENNReal.ofReal_le_ofReal
        linarith [le_max_left R 0, le_max_right R 0]
    _ = ENNReal.ofReal (C₀ * (N : ℝ) ^ (-(1 : ℝ) / 2) * (max R 0 + 1)) :=
        (ENNReal.ofReal_mul (by positivity)).symm
    _ = ENNReal.ofReal (C₀ * (max R 0 + 1) * (N : ℝ) ^ (-(1 : ℝ) / 2)) := by ring_nf

end HRS.ME.FamV
