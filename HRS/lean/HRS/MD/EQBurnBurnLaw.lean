import HRS.MD.EQBurnBurnBase
import HRS.MD.EQInterpWin
import HRS.MD.EQGaussWindow
import HRS.Main.T25Aux6

/-!
# EQ-BURN P4, part 5: transport of the laws

* `eqb_law_windowZeta`: the law of `windowZeta m T a P X` under `P` is the law of the window of the process
  `ζ^t = zetaE m (P₁.map (X_t ∘ π)) (X_t ∘ π)` on the enlarged space `P₁` (`π` measure preserving);
* `eqb_gauss_window`: the Gaussian side, `law P' (windowPath m T a Z) = law P' (windowPath m T 0 Z)`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MD.EQBurnBurn

open HRS HRS.LZ HRS.Uniform

variable {d : ℕ} {N : ℕ}

theorem eqb_windowPath_eq {Ω₁ : Type*} [MeasurableSpace Ω₁] (P₁ : Measure Ω₁) (m T a : ℝ)
    (Y : ℝ≥0 → Ω₁ → Config d N) (ω : Ω₁) :
    (Uniform.windowPath a T (fun t ω' => zetaE m (P₁.map (Y t.toNNReal)) (Y t.toNNReal ω')) ω :
        PathSp T (NegSobolev d m)) = Main.windowZeta m T a P₁ Y ω := by
  unfold Uniform.windowPath Main.windowZeta
  rfl

theorem eqb_law_windowZeta (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (V : Torus d → ℝ)
    (hV : Torus.IsSmooth V) {β : ℝ} (hβ : 0 < β) (hN : 2 ≤ N) {a T : ℝ} (ha : 0 ≤ a) (hT : 0 ≤ T)
    {Ω Ω₁ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω₁] (P : Measure Ω) [IsProbabilityMeasure P]
    (P₁ : Measure Ω₁) {π : Ω₁ → Ω} (hπ : MeasurePreserving π P₁ P)
    {X₀ : Ω → Config d N} {W : ℝ≥0 → Ω → (Fin N → Euc d)} {X : ℝ≥0 → Ω → Config d N}
    (hX : IsStationaryGibbsFlow P s hs0 hsd V β hβ (a + T) X₀ W X) {m : ℝ}
    (hm : (d : ℝ) < 2 * m) :
    law P₁ (Uniform.windowPath a T (fun t ω' => zetaE m (P₁.map (fun ω'' => X t.toNNReal (π ω'')))
        (X t.toNNReal (π ω'))) : Ω₁ → PathSp T (NegSobolev d m)) =
      law P (Main.windowZeta m T a P X) := by
  obtain ⟨ℱ, W', hF⟩ := hX.filtered
  have hXm : ∀ t : ℝ≥0, Measurable (X t) := fun t => (hF.adapted t).mono (ℱ.le t) le_rfl
  have hmap : ∀ t : ℝ≥0, P₁.map (fun ω'' => X t (π ω'')) = P.map (X t) := by
    intro t
    rw [← hπ.map_eq, Measure.map_map (hXm t) hπ.measurable]
    rfl
  have hfun : (Uniform.windowPath a T (fun t ω' => zetaE m (P₁.map (fun ω'' => X t.toNNReal (π ω'')))
        (X t.toNNReal (π ω'))) : Ω₁ → PathSp T (NegSobolev d m)) =
      fun ω' => Main.windowZeta m T a P X (π ω') := by
    funext ω'
    have := eqb_windowPath_eq P₁ m T a (fun t ω'' => X t (π ω'')) ω'
    refine this.trans ?_
    show EQLawPath.eqlaw_pathOf d m T (fun τ : Set.Icc (0 : ℝ) T =>
        zetaE m (P₁.map (fun ω'' => X (Real.toNNReal (a + τ)) (π ω'')))
          (X (Real.toNNReal (a + τ)) (π ω'))) =
      EQLawPath.eqlaw_pathOf d m T (fun τ : Set.Icc (0 : ℝ) T =>
        zetaE m (P.map (X (Real.toNNReal (a + τ)))) (X (Real.toNNReal (a + τ)) (π ω')))
    congr 1
    funext τ
    rw [hmap]
  rw [hfun]
  have hae := EQInterp.windowZeta_aemeasurable hd hs0 hsd V hV hβ hN ha hT P hX hm
  unfold law
  have hae' : AEMeasurable (Main.windowZeta m T a P X) (P₁.map π) := by rw [hπ.map_eq]; exact hae
  have := AEMeasurable.map_map_of_aemeasurable hae' hπ.measurable.aemeasurable
  rw [hπ.map_eq] at this
  exact this.symm

theorem eqb_gauss_window (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (V : Torus d → ℝ)
    {β : ℝ} (hβ : 0 < β) (ρβ : Torus d → ℝ) (m T : ℝ) (hT : 0 ≤ T)
    {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (Z : ℝ → Ω' → NegSobolev d m) (hZ : IsStationaryGaussianField P' s β hs0 hsd hβ V ρβ m Z)
    {a : ℝ} (ha : 0 ≤ a) :
    law P' (Main.windowPath m T a Z) = law P' (Main.windowPath m T 0 Z) :=
  MD.EQGaussWindow.eq_gauss_window_law_proof hd hs0 hsd V hβ ρβ m T hT P' P' Z Z hZ hZ a 0 ha le_rfl

end HRS.MD.EQBurnBurn

end
