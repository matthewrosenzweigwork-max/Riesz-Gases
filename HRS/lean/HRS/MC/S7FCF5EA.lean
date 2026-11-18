import HRS.MC.S7FCW12B

/-!
# FC-E start-`a` packet, part A: the particle zeta window for every start `a` (prefix `S7FCF5E_`)

* `S7FCF5E_aemeasurable_zetaWin`: `zetaWin m T a P X` is `AEMeasurable` for every window start `a : ℝ`
  (the case `a = 0` is `HRS.MC.Sec7.S7FCW12.s7fcw12_aemeasurable_zetaWin`).  The a.s. continuity of the window
  `t ↦ ζ_N^{a+t}` on `[0,T]` comes from `s7fcw12_zetaAt_continuousOn` on `[a, a+T]`, and the window path is the
  `windowPath` of `HRS.Uniform.Q45.aemeasurable_windowPath'` with the shifted process `t ↦ ζ_N^{a+t}`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace HRS.MC.Sec7.S7FCF5E

open HRS HRS.Sec7

variable {d : ℕ}

/-- `zetaWin m T a P X` is `AEMeasurable` for every window start `a` (not only `a = 0`). -/
theorem S7FCF5E_aemeasurable_zetaWin (m T a : ℝ) (hT : 0 < T) (hm : (d : ℝ) < 2 * m) {Ω : Type}
    [MeasurableSpace Ω] {N : ℕ} (P : Measure Ω) [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → Config d N)
    (hadapt : ∀ t : ℝ≥0, Measurable (X t)) (hcont : ∀ᵐ ω ∂P, ∀ i, Continuous fun t : ℝ≥0 => X t ω i)
    (hN : 0 < N) : AEMeasurable (zetaWin m T a P X) P := by
  have hcR : ∀ᵐ ω ∂P, ∀ j, Continuous fun t : ℝ => X t.toNNReal ω j :=
    hcont.mono fun ω hω j => (hω j).comp continuous_real_toNNReal
  have hY : ∀ t ∈ Set.Icc (0 : ℝ) T, AEMeasurable (fun ω => zetaAt m P X (a + t) ω) P := fun t _ =>
    (HRS.MC.Sec7.S7FCW12.s7fcw12_zetaAt_measurable m P X hadapt hN (a + t)).aemeasurable
  have hf : ContinuousOn (fun t : ℝ => a + t) (Set.Icc 0 T) :=
    (by fun_prop : Continuous fun t : ℝ => a + t).continuousOn
  have hc : ∀ᵐ ω ∂P, ContinuousOn (fun t => zetaAt m P X (a + t) ω) (Set.Icc 0 T) :=
    hcR.mono fun ω hω => by
      have h := HRS.MC.Sec7.S7FCW12.s7fcw12_zetaAt_continuousOn m hm P X hadapt hcont hN ω hω
        (Set.Icc a (a + T))
      exact h.comp hf fun t ht =>
        Set.mem_Icc.2 ⟨by linarith [(Set.mem_Icc.1 ht).1], by linarith [(Set.mem_Icc.1 ht).2]⟩
  have hfun : (fun t ω => zetaAt m P X (a + t) ω) = (fun t ω => zetaAt m P X (a + (0 + t)) ω) := by
    funext t ω
    rw [zero_add]
  have hW : zetaWin m T a P X = HRS.Uniform.windowPath 0 T (fun t ω => zetaAt m P X (a + t) ω) := by
    funext ω
    exact congrArg (fun Z : ℝ → Ω → NegSobolev d m => HRS.toPath m T Z ω) hfun
  rw [hW]
  exact HRS.Uniform.Q45.aemeasurable_windowPath' P hT (fun t ω => zetaAt m P X (a + t) ω) hY hc

end HRS.MC.Sec7.S7FCF5E

end
