import HRS.MC.E213R2
import HRS.MD.EQGaussWindow

/-!
# E214P2 (L2): the stationary Gaussian window is an a.e. measurable centred Gaussian random element of `𝒳_{m,T}`

Assembled from `eqgw_fidi` (a.e. measurability), `e213r_fdd_of_vec_law` (the vector laws of `IsStationaryGaussianField`
are Gaussian, hence `FddGaussian`) and `gaussian_window_of_fdd`.
-/

open MeasureTheory ProbabilityTheory
open HRS

noncomputable section

namespace HRS.MC.E214P

open HRS.MC.E213Q HRS.MC.E213R

theorem p2_stationary_window_gaussian {d : ℕ} (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d)
    (V : Torus d → ℝ) {β : ℝ} (hβ : 0 < β) (ρβ : Torus d → ℝ) (M T : ℝ) (hT : 0 < T)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → Ω → NegSobolev d M)
    (hZ : IsStationaryGaussianField P s β hs0 hsd hβ V ρβ M Z) :
    AEMeasurable (HRS.Main.windowPath M T 0 Z) P ∧
      IsCenteredGaussian (law P (HRS.Main.windowPath M T 0 Z)) := by
  have hfdd : FddGaussian P Z (Set.Icc 0 T) :=
    e213r_fdd_of_vec_law (T := T) P Z hZ.meas fun p ts φ hts hφ =>
      ⟨_, hZ.gaussian p ts φ (fun a => (hts a).1) hφ⟩
  have hfdd0 : FddGaussian P Z (Set.Icc 0 (0 + T)) := by rw [zero_add]; exact hfdd
  have hcont0 : ∀ᵐ ω ∂P, ContinuousOn (fun t => Z t ω) (Set.Icc 0 (0 + T)) := by
    filter_upwards [hZ.cont] with ω hω
    exact hω.mono (by rw [zero_add]; exact Set.Icc_subset_Ici_self)
  exact gaussian_window_of_fdd T hT P Z 0 le_rfl hZ.meas hcont0 hfdd0

end HRS.MC.E214P

end
