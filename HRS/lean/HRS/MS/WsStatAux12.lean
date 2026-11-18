import HRS.MS.WsStatAux11
import HRS.MS.GenPathTie

/-!
# S21 packet J: the two `AEMeasurable` conjuncts of S2.1 (i)

* `s21_Z_aemeas`: for any `IsLinearGaussianEvolutionW P' C m q T C0 Z` (`T >= 0`), `processWindow m T 0 Z` is a.e. measurable
  (measurability of each `Z t`, a.s. continuity on `[0,T]`: `gfb4_aemeasurable_windowPath`).
* `s21_zeta_aemeas`: for a collision-free strong solution `X` with `law P (X t) = nu` for all `t <= T` (stationarity,
  `nu` a probability law on configurations, e.g. `canonicalGibbs`) and `m > d`, the exactly centred path
  `zetaPathW m T 0 P X` is a.e. measurable.  The centring `HRS.Whole.meanEmpirical (P.map (X t))` is the constant probability measure
  `HRS.Whole.meanEmpirical nu` on `[0,T]`, so the path is `t |-> sqrt N . ofMeasureDiff m (HRS.Whole.empirical (X_t)) (HRS.Whole.meanEmpirical nu)`, continuous
  in the configuration (`s56_xi_cont_config`) and measurable.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

namespace HRS.MS.S21

open HRS.Whole
open HRS (Euc)

variable {d : ℕ}

theorem s21_Z_aemeas {Ω' : Type*} [MeasurableSpace Ω'] (P' : Measure Ω') {C : WholeCoeff d} {m q T : ℝ}
    {C₀ : (Euc d → ℝ) → (Euc d → ℝ) → ℝ} {Z : ℝ → Ω' → OscDual d m}
    (hZ : IsLinearGaussianEvolutionW P' C m q T C₀ Z) (hT : 0 ≤ T) :
    AEMeasurable (processWindow m T 0 Z) P' := by
  have h := HRS.GF.gfb4_aemeasurable_windowPath P' hT Z (fun t _ => hZ.meas t) hZ.cont
  rw [← HRS.MS.GenPath.s56_wpo_eq_windowPath] at h
  exact h

theorem s21_zeta_aemeas (hd : 2 ≤ d) {N : ℕ} (hN : 1 ≤ N) {m T : ℝ} (hm : (d : ℝ) < m) (hT : 0 ≤ T)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] {D : WholeDyn d}
    {X₀ : Ω → EucConfig d N} {W : ℝ≥0 → Ω → (Fin N → Euc d)} {X : ℝ≥0 → Ω → EucConfig d N}
    (hX : IsWholeStrongSolution P D T X₀ W X) (ν : Measure (EucConfig d N)) [IsProbabilityMeasure ν]
    (hlaw : ∀ t : ℝ≥0, (t : ℝ) ≤ T → P.map (X t) = ν) :
    AEMeasurable (zetaPathW m T 0 P X) P := by
  have hd1 : 1 ≤ d := by omega
  haveI : IsProbabilityMeasure (HRS.Whole.meanEmpirical ν) := HRS.Whole.meanEmpirical_isProbabilityMeasure ν hN
  set Y : ℝ → Ω → OscDual d m := fun t ζ =>
    Real.sqrt N • OscDual.ofMeasureDiff m (HRS.Whole.empirical (X (Real.toNNReal t) ζ)) (HRS.Whole.meanEmpirical ν) with hY
  have hcongr : ∀ ζ, zetaPathW m T 0 P X ζ = windowPathOf m T 0 (fun t => Y t ζ) := by
    intro ζ
    unfold zetaPathW
    refine HRS.MS.GenPath.s56_wpo_congr fun t ht => ?_
    have h1 : P.map (X (Real.toNNReal t)) = ν :=
      hlaw _ (by rw [Real.coe_toNNReal _ ht.1]; exact ht.2)
    simp only [zetaB, hY, h1]
  have hmeas : ∀ t ∈ Icc (0 : ℝ) T, Measurable (Y t) := by
    intro t ht
    have hc : Continuous fun x : EucConfig d N =>
        Real.sqrt N • OscDual.ofMeasureDiff m (HRS.Whole.empirical x) (HRS.Whole.meanEmpirical ν) :=
      HRS.MS.GenPath.s56_xi_cont_config hd1 hm (Real.sqrt N) (by omega) (HRS.Whole.meanEmpirical ν)
    exact hc.measurable.comp (hX.adapted _)
  have hcont : ∀ᵐ ζ ∂P, ContinuousOn (fun t => Y t ζ) (Icc 0 T) := by
    filter_upwards [hX.cont] with ζ hζ
    have hc : Continuous fun x : EucConfig d N =>
        Real.sqrt N • OscDual.ofMeasureDiff m (HRS.Whole.empirical x) (HRS.Whole.meanEmpirical ν) :=
      HRS.MS.GenPath.s56_xi_cont_config hd1 hm (Real.sqrt N) (by omega) (HRS.Whole.meanEmpirical ν)
    have hpath : Continuous fun t : ℝ => (X (Real.toNNReal t) ζ : EucConfig d N) :=
      continuous_pi fun i => (hζ i).comp continuous_real_toNNReal
    exact (hc.comp hpath).continuousOn
  have h := HRS.GF.gfb4_aemeasurable_windowPath P hT Y hmeas hcont
  rw [← HRS.MS.GenPath.s56_wpo_eq_windowPath] at h
  have e : zetaPathW m T 0 P X = fun ζ => windowPathOf m T 0 (fun t => Y t ζ) := funext hcongr
  rw [e]
  exact h

end HRS.MS.S21
