import HRS.MC.S7PIL1
import HRS.MC.S7PIDefs
import HRS.MC.S7PIS3Law
import HRS.MC.S7PIS2Obs
import HRS.MC.S7PIS2Proj
import HRS.MC.S7PIB5

/-!
# Packet piL, part 2: the projected derivative of the heat function is a finite-dimensional heat value

For grid data `P = Λ ∘ obsVec` and `w : Fin j → X`:
`projHeatD γ Φ P j u y w = gaussHeat obsCov ψ_w u 0` with `ψ_w(c) = D^jΦ(P y + Λ c)[w]`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7PIL

open HRS HRS.Sec7 HRS.MC.Sec7 HRS.MC.Sec7.PI

variable {d : ℕ}

local instance S7PIL_pathSC {m T : ℝ} : SecondCountableTopology (PathSpace d m T) :=
  inferInstanceAs (SecondCountableTopology C(Set.Icc (0 : ℝ) T, NegSobolev d m))

/-- The grid functions are smooth. -/
theorem S7PIL_grid_smooth {m T : ℝ} (hT : 0 ≤ T) {L q : ℕ} {t : Fin q → ℝ} {φ : Fin q → Torus d → ℝ}
    {Λ : EuclideanSpace ℝ (Fin q) →L[ℝ] PathSpace d m T} (hg : IsGridData m T hT L q t φ Λ) :
    ∀ i, Torus.IsSmooth (φ i) := by
  intro i
  obtain ⟨k, hk⟩ := hg.2.1 i
  rw [hk]
  exact HRS.FieldSingAux.isSmooth_realMode k

theorem S7PIL_projHeatD_apply (R : Regime d) (m : ℝ) (T : ℝ) (hT : 0 < T)
    (γ : ℝ → Measure (PathSpace d m T)) (hγ : ∀ u ∈ Set.Icc (0 : ℝ) T, IsFutureGaussian R.D R.ρ m T u (γ u))
    {L q : ℕ} {t : Fin q → ℝ} {φ : Fin q → Torus d → ℝ}
    {Λ : EuclideanSpace ℝ (Fin q) →L[ℝ] PathSpace d m T} (hg : IsGridData m T hT.le L q t φ Λ)
    (P : PathSpace d m T →L[ℝ] PathSpace d m T) (hP : ∀ w, P w = Λ (obsVec m T t φ w))
    {Φ : PathSpace d m T → ℝ} (hΦ : MemCb 5 Φ) {j : ℕ} (hj : j ≤ 3) {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) T)
    (y : PathSpace d m T) (w : Fin j → PathSpace d m T) :
    projHeatD γ Φ P j u y w =
      gaussHeat (obsCov R.D R.ρ t φ) (S7PIL_psi (iteratedFDeriv ℝ j Φ) (P y) Λ w) u 0 := by
  have hφ := S7PIL_grid_smooth hT.le hg
  obtain ⟨O0, hO0⟩ := HRS.MC.Sec7.S7PIS2.s7_PIS_obs_clm_proof m T t φ hg.1 hφ
  have law := (HRS.MC.Sec7.S7PIS3.s7_PIS_obs_law_proof R m T hT γ hγ t φ hg.1 hφ) u hu
  have hmeas : Measurable (obsVec m T t φ) := by
    have : obsVec m T t φ = fun w => O0 w := funext fun w => (hO0 w).symm
    rw [this]; exact O0.continuous.measurable
  have hadd : ∀ y z, obsVec m T t φ (y + z) = obsVec m T t φ y + obsVec m T t φ z := by
    intro y z; rw [← hO0, ← hO0, ← hO0, map_add]
  have : IsProbabilityMeasure (γ u) := by
    refine ⟨?_⟩
    have h1 := congrArg (fun μ : Measure (EuclideanSpace ℝ (Fin q)) => μ Set.univ) law.2
    simp only [Measure.map_apply hmeas MeasurableSet.univ, Set.preimage_univ] at h1
    rw [h1]; exact measure_univ
  have hPy : ∀ z, P (y + z) = P y + Λ (obsVec m T t φ z) := by
    intro z; rw [hP, hadd, map_add, hP]
  have hΦ5 : ContDiff ℝ 5 Φ := hΦ.1
  have hcont : Continuous (iteratedFDeriv ℝ j Φ) := hΦ5.continuous_iteratedFDeriv (by
    exact_mod_cast (by omega : j ≤ 5))
  have hint : Integrable (fun z => iteratedFDeriv ℝ j Φ (P (y + z))) (γ u) := by
    refine Integrable.of_bound (C := cbNorm 5 Φ) ?_ ?_
    · exact (hcont.comp (P.continuous.comp (continuous_const.add continuous_id))).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun z => S7PIL_le_cbNorm hΦ (by omega) _
  unfold projHeatD
  have h1 := ContinuousLinearMap.integral_comp_comm (S7PIL_ev w) hint
  rw [← S7PIL_ev_apply, ← h1]
  simp only [S7PIL_ev_apply]
  have hψ := S7PIL_psi_memCb hΦ hj (P y) Λ w
  have hψc : Continuous (S7PIL_psi (iteratedFDeriv ℝ j Φ) (P y) Λ w) := hψ.1.continuous
  unfold gaussHeat
  simp only [zero_add]
  rw [← law.2]
  rw [integral_map hmeas.aemeasurable hψc.aestronglyMeasurable]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  simp only [zero_add, S7PIL_psi]
  rw [hPy z]

end HRS.MC.Sec7.S7PIL

end
