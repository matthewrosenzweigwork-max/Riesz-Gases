import HRS.Main.T25MWAux1
import HRS.Sections.AdjKGlue

/-!
# T25MW, part 2: Lemma 3.27 along an `IsSmoothPositiveTrajectory` with the repaired `MaxWindows`

`t25mw_evolution_along_trajectory` is `HRS.AdjK.adjk_evolution_along_trajectory` with the last conjunct replaced by
`HRS.Uniform.MaxWindows` (which includes measurability of the competitor convolution).  The window estimate comes from
quasi-contractivity (`Q48e.winmax_of_quasi`) and the bridge `t25mw_maxWindows_of_winMaxU`.
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.T25MW

open HRS.Uniform HRS.AdjK

theorem t25mw_evolution_along_trajectory {d : ℕ} {s β : ℝ} {V ρ₀ : Torus d → ℝ} {ρ : ℝ → Torus d → ℝ}
    (hd : 2 ≤ d) (htr : IsSmoothPositiveTrajectory d s β V ρ₀ ρ)
    (r : ℝ) :
    ∃ Cr cr : ℝ, 0 < Cr ∧ 0 < cr ∧
      ∃ Vev : ℝ → ℝ → NegSobolev d r →L[ℝ] NegSobolev d r,
        IsDualEvolution htr.dyn ρ r Vev ∧
        (∀ T : ℝ, 0 ≤ T → IsPlainEvolution Vev T) ∧
        (∀ u t : ℝ, 0 ≤ u → u ≤ t → ‖Vev t u‖ ≤ Cr * Real.exp (-cr * (t - u))) ∧
        ∀ T : ℝ, 0 < T → ∃ CrT : ℝ, 0 ≤ CrT ∧ HRS.Uniform.MaxWindows.{0, 0} Vev T CrT := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨K₀, hK₀⟩ := Q54.exists_levelInput hd1 s htr.hs0 htr.hsd r
  set K : ℕ := max K₀ (⌊(d : ℝ) / 2 + 6⌋₊ + 1) with hK
  have hKgt : (d : ℝ) / 2 + 6 < K := by
    have h1 : (d : ℝ) / 2 + 6 < ((⌊(d : ℝ) / 2 + 6⌋₊ + 1 : ℕ) : ℝ) := by
      push_cast; exact Nat.lt_floor_add_one _
    exact h1.trans_le (by exact_mod_cast le_max_right _ _)
  have H := Q40b.q40b_finiteRegHyp htr hKgt
  obtain ⟨ρc, hρc, hρ⟩ := htr.global K hKgt
  obtain ⟨Vev, hdual, hplain, ⟨c, hc⟩, Cr, cr, hCr, hcr, hdec⟩ :=
    hK₀ K (le_max_left _ _) β htr.hβ V ρ₀ H ρc hρc
  refine ⟨Cr, cr, hCr, hcr, Vev, ?_, hplain, hdec, ?_⟩
  · intro u t hu hut z φ hφ
    rw [hdual u t hu hut z φ hφ]
    congr 1
    funext x
    have := Q40b.q40b_propagator_congr (D := htr.dyn) (ρ := PDE.mfPath ρc) (ρ' := ρ) (t := t)
      (fun r hr => hρ r hr.1) u φ
    exact congrFun this x
  · intro T hT
    have hq : ∀ u t : ℝ, 0 ≤ u → u ≤ t → ‖Vev t u‖ ≤ Real.exp ((2 * c) * (t - u) / 2) := by
      intro u t hu hut
      have := hc u t hu hut
      rwa [show (2 * c) * (t - u) / 2 = c * (t - u) by ring]
    have hW := Q48e.winmax_of_quasi.{0} hplain (K := 2 * c) hq hT.le
    exact ⟨Kot.CD 2 (2 * c) T, Kot.CD_nonneg _ _ _, t25mw_maxWindows_of_winMaxU hW⟩

end HRS.T25MW
