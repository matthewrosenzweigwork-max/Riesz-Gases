import HRS.MH.MfclSpec
import HRS.MH.MfclA1A9
import HRS.MH.MfclA2A3
import HRS.MH.MfclA5A6
import HRS.MH.MfclA7
import HRS.MH.MfclA8
import HRS.MH.MfclA10A11

/-!
# Proof of `HRS.Main.mean_field_centering_lower_bound` (Mfcl A12, assembly)

First-moment lower bound.  With `ℓ` the time-zero pairing with `ρβ`, the Wasserstein distance of order one between the
window of the fluctuation path and the Gaussian window dominates `|E ℓ(window) - E ℓ(Gaussian window)| / (‖ℓ‖ + 1)`;
the first mean is `centerShift` (stationarity, packets A7 and A8), the second is `0` (A9), and `centerShift` is
bounded below by `c₁ √N δ_N` (A11).  The hypothesis `s < 2d/3` is not used.

The statement is `HRS.MH.Mfcl.mean_field_centering_lower_bound_core`, which is checked against the frozen
`HRS.Main.mean_field_centering_lower_bound` by the `type_of%` example in `HRS/MH/MfclSpec.lean`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MH.MfclP

open HRS HRS.Main HRS.LZ HRS.MD.EQ29

theorem mean_field_centering_lower_bound_core_proof :
    type_of% @HRS.MH.Mfcl.mean_field_centering_lower_bound_core := by
  intro d hd s hs0 hsd V hV hs1 hs2 β hβ ρβ hρβ hnc m hm T hT
  have hsm : Torus.IsSmooth ρβ := (Q41.q41_thermal_regular hd hs0 hsd hβ hV hρβ).2
  have hm2 : (d : ℝ) < 2 * m := by
    have h1 : (d : ℝ) + 1 < m := lt_of_le_of_lt (le_max_left _ _) hm
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  obtain ⟨ℓ, hℓ⟩ := exists_pathEval_proof m T hT.le ρβ hsm
  obtain ⟨c₁, hc₁, N₀, hN₀2, hN₀⟩ := centerShift_lower_proof hd hs1 hsd V hV hβ ρβ hρβ hnc
  have hDpos : 0 < ‖ℓ‖ + 1 := by positivity
  refine ⟨c₁ / (‖ℓ‖ + 1), div_pos hc₁ hDpos, N₀, ?_⟩
  intro N hN u hu Ω _ P _ X₀ W X hflow hfilt hinit Ω' _ P' _ Z hZ
  have hN2 : 2 ≤ N := hN₀2.trans hN
  have hX : IsStationaryGibbsFlow P s hs0 hsd V β hβ (u + T) X₀ W X := ⟨hflow, hfilt, hinit⟩
  have hW : AEMeasurable (windowFluc m T u (Real.sqrt N) X (fun _ => ρβ)) P :=
    windowFluc_aemeasurable_proof hd hs0 hsd V hV hβ hN2 hu hT.le P hX hm2 ρβ hρβ.1 (Real.sqrt N)
  obtain ⟨hW', hint', hmean'⟩ :=
    gauss_pathEval_proof hd hs0 hsd V hV hβ ρβ hρβ hsm hT.le P' Z hZ ℓ hℓ
  haveI : IsProbabilityMeasure (law P (windowFluc m T u (Real.sqrt N) X (fun _ => ρβ))) :=
    (Measure.isProbabilityMeasure_map_iff hW).2 inferInstance
  haveI : IsProbabilityMeasure (law P' (windowPath m T 0 Z)) :=
    (Measure.isProbabilityMeasure_map_iff hW').2 inferInstance
  have hlaw := law_pathEval_windowFluc_proof hd hs0 hsd V hV hβ hN2 hu hT.le P hX hm2 ρβ hρβ.1 hsm ℓ hℓ
  obtain ⟨hint, hmean⟩ := integral_linCoord_gibbs_proof hd hs0 hsd V hV hβ ρβ hρβ hsm hN2
  have hint1 : Integrable (fun x : ℝ => x)
      ((law P (windowFluc m T u (Real.sqrt N) X (fun _ => ρβ))).map ℓ) := by
    rw [hlaw]
    exact hint
  have h3 := wassersteinE_one_ge_clm_mean_diff_proof ℓ
    (law P (windowFluc m T u (Real.sqrt N) X (fun _ => ρβ))) (law P' (windowPath m T 0 Z)) hint1 hint'
  rw [hlaw, hmean, hmean', sub_zero] at h3
  refine le_trans (ENNReal.ofReal_le_ofReal ?_) h3
  have hδ : 0 ≤ deltaN d s N := HRS.MD.EQTransShift.et_deltaN_nonneg hs0 (by omega)
  have hnn : 0 ≤ c₁ * (Real.sqrt N * deltaN d s N) :=
    mul_nonneg hc₁.le (mul_nonneg (Real.sqrt_nonneg _) hδ)
  have hcs := hN₀ N hN
  rw [abs_of_nonneg (hnn.trans hcs)]
  calc c₁ / (‖ℓ‖ + 1) * (Real.sqrt N * deltaN d s N)
      = c₁ * (Real.sqrt N * deltaN d s N) / (‖ℓ‖ + 1) := by ring
    _ ≤ centerShift d s V β ρβ ρβ N / (‖ℓ‖ + 1) := by gcongr

/-- The frozen theorem `HRS.Main.mean_field_centering_lower_bound`. -/
theorem mean_field_centering_lower_bound_proof : type_of% @HRS.Main.mean_field_centering_lower_bound :=
  mean_field_centering_lower_bound_core_proof

end HRS.MH.MfclP
