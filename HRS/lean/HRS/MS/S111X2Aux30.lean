import HRS.MS.S111X2Aux29

/-!
# S11.1 X2, packet E07 (part 5): the generator orbit bridge

For a classical solution `f` (terminal datum `φ ∈ C_b²`) and the classical solution `h` with terminal datum `G φ`:
`f r = φ + ∫_r^H h` and `G f r = h r`; in forward time `F t = f (H - t)`, `G_t = h (H - t)`: `F t = φ + ∫_0^t G_r`,
`∂_t F = G_t = G F_t`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxSynthPendingDepth 3
noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S111X2

open HRS (Euc)
open HRS.Whole HRS.Whole.Q34

variable {d : ℕ}

theorem s111x2_orbit_bridge (hd : 2 ≤ d) {s a β H : ℝ} (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2)
    (ha : 0 < a) (hβ : 0 < β) (hH : 0 < H) {ρ : Euc d → ℝ} (hρ : IsThermalEquilibrium d s a β ρ)
    {φ : Euc d → ℝ} (hφ : MemCb 2 φ) {f h : ℝ → Euc d → ℝ}
    (hf : IsClassicalAdjointW ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) H φ f)
    (hh : IsClassicalAdjointW ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) H
      (generatorW ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) 0 φ) h) :
    (∀ r ∈ Icc (0 : ℝ) H, f r = s111x2_Ftil φ (fun u => h (s111x2_clamp H u)) H r) ∧
      (∀ r ∈ Icc (0 : ℝ) H, ∀ x, f r x = φ x + ∫ u in r..H, h u x) ∧
      (∀ r ∈ Icc (0 : ℝ) H, generatorW ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) 0 (f r) = h r) := by
  obtain ⟨M, T⟩ := s111x2_td_of_thermal hd hs0 hs ha hβ hρ
  have hcl := s111x2_ftil_classical T hH hφ hh
  have hu := HRS.MS.S111X1.uniq_of_thermal hd hs0 hs ha hβ hρ H hH.le φ f _ hf hcl
  obtain ⟨A0, A1, A2, hA0, hA0', hφC⟩ := s111x2_cb2_bounds hφ
  obtain ⟨B0, B1, B2, hB0, hB1, hB2, hfam, hB0'⟩ := s111x2_clamp_fam hH.le hh
  refine ⟨hu, fun r hr x => ?_, fun r hr => ?_⟩
  · rw [hu r hr]
    unfold s111x2_Ftil
    congr 1
    refine intervalIntegral.integral_congr fun u hu' => ?_
    rw [uIcc_of_le hr.2] at hu'
    simp only
    rw [s111x2_clamp_id ⟨hr.1.trans hu'.1, hu'.2⟩]
  · rw [hu r hr]
    funext x
    exact s111x2_ftil_gen T hφC hh hfam hr x

end HRS.MS.S111X2
