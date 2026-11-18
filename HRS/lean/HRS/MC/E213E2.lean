import HRS.MC.E213E1
import HRS.Sections.Sec7Setting
import HRS.Main.Headline

/-!
# Packet E213E, L2 and L3: realisations from a selected flow, and the window functional

* `e213e_prepared_of_selected` (L2): if `X` is a `SelectedFlow` on `[0,H]` (flow disjunct, `d ≥ 2`) with initial law `Q₀`, then there is a
  `PreparedRealization` `Xc` (global strong solution on every horizon, filtered) on the SAME space with the SAME `X₀`, `W`, and
  `X = Xc` a.s. on `[0,H]` (pathwise uniqueness).
* `e213e_windowZeta_congr` (L3): the window `windowZeta m T a P X` depends on `X` only through the values `X s`, `s ≤ a + T`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MC.E213E

open HRS HRS.Sec7

variable {d N : ℕ}

theorem e213e_prepared_of_selected (D : DynData d) (hd : 2 ≤ d) (hM : Torus.SymNonpos D.M)
    (hV : Torus.IsCk 2 D.V)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (H : ℝ)
    (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N)
    (hSel : SelectedFlow P D H X₀ W X) (Q₀ : Measure (Config d N)) (hlaw : P.map X₀ = Q₀) :
    ∃ Xc : ℝ≥0 → Ω → Config d N, PreparedRealization D P Q₀ X₀ W Xc ∧
      ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ) ≤ H → X t ω = Xc t ω := by
  rcases hSel.flow with ⟨hX, hPU⟩ | ⟨hd1, -⟩
  · obtain ⟨Xc, hXc, ℱ, W', hF⟩ := e213e_exists_global_filtered P D hd hM hV X₀ hSel.init_meas
      hSel.init_distinct W hSel.brownian hSel.indep
    exact ⟨Xc, ⟨hlaw, hSel.brownian, hSel.indep, hXc, ℱ, W', hF⟩, hPU X Xc hX (hXc H)⟩
  · omega

open Classical in
private theorem e213e_dite_congr {X E : Type*} [TopologicalSpace X] [NormedAddCommGroup E]
    (f g : X → E) (hfg : f = g) :
    (if h : Continuous f then (⟨f, h⟩ : C(X, E)) else 0) = (if h : Continuous g then ⟨g, h⟩ else 0) := by
  subst hfg
  rfl

theorem e213e_windowZeta_congr (m T a : ℝ) (ha : 0 ≤ a) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X Xc : ℝ≥0 → Ω → Config d N)
    (h : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ) ≤ a + T → X t ω = Xc t ω) :
    (∀ᵐ ω ∂P, Main.windowZeta m T a P X ω = Main.windowZeta m T a P Xc ω) ∧
    P.map (Main.windowZeta m T a P X) = P.map (Main.windowZeta m T a P Xc) := by
  have hmap : ∀ s : ℝ≥0, (s : ℝ) ≤ a + T → P.map (X s) = P.map (Xc s) := by
    intro s hs
    exact Measure.map_congr (by filter_upwards [h] with ω hω using hω s hs)
  have key : ∀ᵐ ω ∂P, Main.windowZeta m T a P X ω = Main.windowZeta m T a P Xc ω := by
    filter_upwards [h] with ω hω
    unfold Main.windowZeta
    refine e213e_dite_congr _ _ ?_
    funext t
    have ht0 : 0 ≤ (t : ℝ) := t.2.1
    have ht1 : (t : ℝ) ≤ T := t.2.2
    have hle : ((Real.toNNReal (a + t) : ℝ≥0) : ℝ) ≤ a + T := by
      rw [Real.coe_toNNReal _ (by linarith)]; linarith
    rw [hmap _ hle, hω _ hle]
  exact ⟨key, Measure.map_congr key⟩

end HRS.MC.E213E
