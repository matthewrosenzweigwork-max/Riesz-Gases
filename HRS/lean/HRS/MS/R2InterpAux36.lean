import HRS.MS.R2InterpAux35
import HRS.MC.S7PIL1

/-!
# S10.2 (worker S102), part 36 (packet B2, step A): the projected derivative of the heat function is a finite-dimensional heat value

`s102_projHeatD γ Φ P_L j u y w = ∫ ψ_w dN(0, obsCov u)` with `ψ_w(c) = D^jΦ(P_L y + Λ_L c)[w]`.
-/

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.R2Interp

open HRS HRS.Whole HRS.MC.Sec7.S7PIL

variable {d : ℕ} {C : WholeCoeff d} {m T : ℝ}

theorem s102_projHeatD_apply (hT : 0 < T) (L : ℕ) (γ : ℝ → Measure (OscPath d m T))
    (hγp : ∀ u, IsProbabilityMeasure (γ u))
    (hγ : ∀ u ∈ Icc (0 : ℝ) T, IsR2FutureGaussian C m T u (γ u))
    {Φ : OscPath d m T → ℝ} (hΦ : MemCb 5 Φ) {j : ℕ} (hj : j ≤ 3) {u : ℝ} (hu : u ∈ Icc (0 : ℝ) T)
    (y : OscPath d m T) (w : Fin j → OscPath d m T) :
    s102_projHeatD γ Φ (s102_Pj T hT L) j u y w =
      ∫ x, S7PIL_psi (iteratedFDeriv ℝ j Φ) (s102_Pj T hT L y) (s102_Lam T L) w x
        ∂(multivariateGaussian 0 (s102_obsCov C m (s102_tauk hT L) (s102_alk L) u)) := by
  haveI := hγp u
  set P := s102_Pj T hT L with hPdef
  set obs := s102_obs (s102_tauk hT L) (s102_alk L) (m := m) with hobs
  have hcont : Continuous (iteratedFDeriv ℝ j Φ) :=
    hΦ.1.continuous_iteratedFDeriv (m := j) (by exact_mod_cast (by omega : j ≤ 5))
  obtain ⟨Cb, hCb⟩ := s102_bound_of_memCb hΦ (by omega : j ≤ 5)
  have hint : Integrable (fun z => iteratedFDeriv ℝ j Φ (P (y + z))) (γ u) :=
    s102_integrable_of_bdd (hcont.comp (P.continuous.comp (by fun_prop))) (fun z => hCb _)
  unfold s102_projHeatD
  have h1 : (∫ z, iteratedFDeriv ℝ j Φ (P (y + z)) ∂(γ u)) w =
      ∫ z, iteratedFDeriv ℝ j Φ (P (y + z)) w ∂(γ u) := by
    have := (S7PIL_ev w).integral_comp_comm hint
    simpa [S7PIL_ev_apply] using this.symm
  rw [h1]
  have h2 : ∀ z, iteratedFDeriv ℝ j Φ (P (y + z)) w =
      S7PIL_psi (iteratedFDeriv ℝ j Φ) (P y) (s102_Lam T L) w (obs z) := by
    intro z
    simp only [S7PIL_psi, hPdef, hobs, map_add]
    rw [s102_Pj_eq_Lam hT L z]
  simp_rw [h2]
  have hl := (s102_obs_law C (hγ u hu) (s102_tauk hT L) (s102_alk L)).2
  rw [← hl, integral_map (obs.continuous.aemeasurable)]
  have hψ := S7PIL_psi_memCb hΦ (by omega : j ≤ 3) (P y) (s102_Lam T L) w
  exact hψ.1.continuous.aestronglyMeasurable

end HRS.MS.R2Interp

end
