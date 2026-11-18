import HRS.MC.S7FCF5Defs
import HRS.MC.S7FCF5GE1
import HRS.MC.S7FCF5EA

/-!
# Packet fcf5i, E2: the windows are `AEMeasurable` (proof of `fcf5_E2_window_aemeasurable`)

Statement copied verbatim from `HRS/MC/S7FCF5Plan.lean` (checked in `HRS/MC/S7FCF5ITie.lean`).

* `zetaWin` part: `S7FCF5E_aemeasurable_zetaWin` (`S7FCF5EA.lean`), with `hadapt`/`hcont` from `hreal.solution 0`.
* `windowFluc` part: the window `t ↦ η_N^{a+t}` (with `σ = √N`) is the `Uniform.windowPath 0 T` of the process
  `t ↦ etaE r (X_{a+t}) μ^{a+t}`.  Measurability of each section comes from `measurable_ofMeasureDiff_empirical`
  (`Energy/Modulated.lean`) composed with the adaptedness of `X`; a.s. continuity on `[0,T]` comes from the E1
  proof `fcf5_E1_window_cont_proof` (`S7FCF5GE1.lean`).  Then `aemeasurable_windowPath'` (`Q45Ten1.lean`).

Namespace `HRS.MC.Sec7.S7FCF5I`, prefix `S7FCF5I_` for helpers, `_proof` for the theorem.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7FCF5I

open HRS HRS.Sec7 HRS.MC.Sec7 HRS.MC.SEdge HRS.MC.QRSpec HRS.MC.Sec7.FCPlan HRS.MC.Sec7.FCF5Plan

variable {d : ℕ}

open Classical in
/-- The `dite` defining `flucPath`/`windowPath` only depends on the underlying function (as
`dite_continuousMap_congr`, `HRS/Main/GFSpec1.lean`, copied so that the import closure stays sorry-free). -/
theorem S7FCF5I_dite_congr {X E : Type*} [TopologicalSpace X] [NormedAddCommGroup E]
    (f g : X → E) (hfg : f = g) :
    (if h : Continuous f then (⟨f, h⟩ : C(X, E)) else 0) = (if h : Continuous g then ⟨g, h⟩ else 0) := by
  subst hfg
  rfl

/-- **E2 (the windows are `AEMeasurable` into `PathSpace`)**, proof. -/
theorem fcf5_E2_window_aemeasurable_proof (R : Regime d) (r : ℝ) (hr : r = 2 * (d : ℝ) + 6) (T : ℝ) (hT : 0 < T)
    {N : ℕ} (hN : 1 ≤ N) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N)
    (hreal : FCPrepared R P X₀ W X) (a : ℝ) (ha : 0 ≤ a) :
    AEMeasurable (HRS.Main.windowFluc r T a (Real.sqrt N) X R.ρ) P ∧ AEMeasurable (zetaWin r T a P X) P := by
  have hd : (d : ℝ) < 2 * r := by
    rw [hr]
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  have hN0 : 0 < N := by omega
  have hS := hreal.solution 0
  refine ⟨?_, HRS.MC.Sec7.S7FCF5E.S7FCF5E_aemeasurable_zetaWin r T a hT hd P X hS.adapted hS.cont hN0⟩
  -- measurability of each section `ω ↦ η_N^{s}` (for `s ≥ 0`)
  have hdens : ∀ s : ℝ, 0 ≤ s → IsProbDensity (R.ρ s) := fun s hs =>
    (R.mf (s + 1) (by linarith)).density s ⟨hs, by linarith⟩
  have hmeas : ∀ s : ℝ, 0 ≤ s → Measurable fun ω => etaE r (X s.toNNReal ω) (withDensityReal (R.ρ s)) := by
    intro s hs
    haveI := isProb_withDensityReal (hdens s hs)
    exact ((measurable_ofMeasureDiff_empirical hd (withDensityReal (R.ρ s)) hN).comp
      (hS.adapted s.toNNReal)).const_smul (Real.sqrt N)
  -- a.s. continuity of the window (E1)
  have hc : ∀ᵐ ω ∂P, ContinuousOn
      (fun t : ℝ => etaE r (X (a + t).toNNReal ω) (withDensityReal (R.ρ (a + t)))) (Set.Icc 0 T) := by
    filter_upwards [(HRS.MC.Sec7.S7FCF5G.fcf5_E1_window_cont_proof R r hr T hN P X₀ W X hreal a ha).1] with ω hω
    exact continuousOn_iff_continuous_restrict.2 hω
  -- the window is the `windowPath` of the process `η^{a+·}`
  have hW : ∀ ω, HRS.Main.windowFluc r T a (Real.sqrt N) X R.ρ ω =
      HRS.Uniform.windowPath 0 T (fun t ω => etaE r (X (a + t).toNNReal ω) (withDensityReal (R.ρ (a + t)))) ω := by
    intro ω
    unfold HRS.Main.windowFluc HRS.flucPath HRS.Uniform.windowPath
    refine S7FCF5I_dite_congr _ _ ?_
    funext t
    have ht : (0 : ℝ) ≤ (t : ℝ) := t.2.1
    simp only [etaE, flucE, zero_add, Real.toNNReal_add ha ht]
  have hW' : HRS.Main.windowFluc r T a (Real.sqrt N) X R.ρ =
      HRS.Uniform.windowPath 0 T (fun t ω => etaE r (X (a + t).toNNReal ω) (withDensityReal (R.ρ (a + t)))) :=
    funext hW
  rw [hW']
  exact HRS.Uniform.Q45.aemeasurable_windowPath' P hT
    (fun t ω => etaE r (X (a + t).toNNReal ω) (withDensityReal (R.ρ (a + t))))
    (fun t ht => (hmeas (a + t) (add_nonneg ha ht.1)).aemeasurable) hc

end HRS.MC.Sec7.S7FCF5I

end
