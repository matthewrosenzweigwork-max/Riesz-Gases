import HRS.Uniform.KotTransform
import HRS.MC.E213N3

/-!
# Packet e213r, part 1: the shifted Hilbert martingale `G^u(τ) = G(τ ∨ u) - G(u)` (on `[0,T]`)

For a Hilbert martingale `G` with covariation density `Σ_r` on `[0,T]` and `0 ≤ u ≤ T`, the process
`τ ↦ G(clampI u T τ) - G(u)` (which is `0` for `τ ≤ u` and `G τ - G u` on `[u,T]`) is a Hilbert martingale on `[0,T]`
(for the null-set augmentation of the filtration) with covariation density `1_{(u,T]} Σ_r`.  This is the step transform
`HRS.Uniform.Kot.isHMC_stepT` with one cell `(u,T]` and `A = id`.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

namespace HRS.MC.E213R

open HRS HRS.Uniform HRS.Uniform.Kot

theorem e213r_shift_hmc {Ω : Type} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : Filtration ℝ mΩ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H] {T u : ℝ} (hu : 0 ≤ u) (huT : u ≤ T)
    {G : ℝ → Ω → H} {Sg : ℝ → Ω → (H →L[ℝ] H →L[ℝ] ℝ)}
    (hG : IsHilbertMartingaleWithCovariation P ℱ T G Sg) :
    IsHilbertMartingaleWithCovariation P (augFiltration P ℱ) T (fun τ ω => G (clampI u T τ) ω - G u ω)
      (fun r ω => (Ioc u T).indicator (fun r => Sg r ω) r) := by
  classical
  set s : ℕ → ℝ := fun l => if l = 0 then u else T with hs
  have hmono : Monotone s := by
    intro a b hab
    simp only [hs]
    by_cases ha : a = 0
    · by_cases hb : b = 0
      · simp [ha, hb]
      · simp [ha, hb, huT]
    · have hb : b ≠ 0 := by omega
      simp [ha, hb]
  have h0 : 0 ≤ s 0 := by simp [hs, hu]
  have hsn : s 1 ≤ T := by simp [hs]
  have hH := isHMC_stepT (augFiltration_isComplete (P := P) ℱ) (isHMC_aug hG) hmono h0 hsn
    (fun _ => ContinuousLinearMap.id ℝ H) (n := 1) (cA := 1) (fun l _ => ContinuousLinearMap.norm_id_le)
  have e1 : stepT G s 1 (fun _ => ContinuousLinearMap.id ℝ H) =
      fun τ ω => G (clampI u T τ) ω - G u ω := by
    funext τ ω
    simp [stepT, hs]
  have e2 : stepSg Sg s 1 (fun _ => ContinuousLinearMap.id ℝ H) =
      fun r ω => (Ioc u T).indicator (fun r => Sg r ω) r := by
    funext r ω
    ext x y
    rw [stepSg_apply']
    by_cases h : u < r ∧ r ≤ T
    · simp [hs, Set.indicator_apply, h, ContinuousLinearMap.adjoint_id]
    · simp [hs, Set.indicator_apply, h]
  rw [e1, e2] at hH
  exact hH

end HRS.MC.E213R
