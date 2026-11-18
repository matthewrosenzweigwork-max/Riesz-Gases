import HRS.MS.R2InterpAux39

/-!
# S10.2 (worker S102), part 40 (packet B2, conclusion): the uniform time-Lipschitz bound `S102LipProj` for the projection family `P_L`
-/

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.R2Interp

open HRS HRS.Whole HRS.MS.CovMeas

variable {d : ℕ} {C : WholeCoeff d} {m T : ℝ} {r : ℕ} {c : MultiIndex d → ℝ} {Pw : ℝ}

/-- Packet B2: the projected heat derivatives are Lipschitz in time, uniformly in `L`, for the whole-space projection family. -/
theorem s102_lipProj (hd : 1 ≤ d) (hP0 : 0 ≤ Pw) (hr : (d : ℝ) / 2 + 1 < r) (hP : (d : ℝ) < 2 * Pw)
    (hD : S101Data C m T r c) (hlin : S102Lin C m T) (hT : 0 < T) (hν : 0 ≤ C.ν)
    (Mρ : ℝ) (hρint : ∀ u ∈ Icc (0 : ℝ) T, Integrable (C.ρ u))
    (hρnn : ∀ u ∈ Icc (0 : ℝ) T, ∀ x, 0 ≤ C.ρ u x)
    (hρmom : ∀ u ∈ Icc (0 : ℝ) T, Integrable (fun x => C.ρ u x * jbracket x ^ (2 * Pw)) ∧
      ∫ x, C.ρ u x * jbracket x ^ (2 * Pw) ≤ Mρ)
    (hG : ∀ L : ℕ, S102GramInt C m hT L)
    (γ : ℝ → Measure (OscPath d m T)) (hγp : ∀ u, IsProbabilityMeasure (γ u))
    (hγ : ∀ u ∈ Icc (0 : ℝ) T, IsR2FutureGaussian C m T u (γ u)) :
    S102LipProj γ (fun L => s102_Pj T hT L) := by
  obtain ⟨Cb, hCb0, hCb⟩ := s102_rate_bound hd hP0 hr hP hD hlin hT Mρ hρint hρnn hρmom
  refine ⟨Cb / 2, fun L Φ hΦ u hu v hv j hj y => ?_⟩
  have hCbL : ∀ {ρ : ℝ}, ρ ∈ Icc (0 : ℝ) T → ∀ N : OscPath d m T [×2]→L[ℝ] ℝ,
      |∑ k, ∑ k', s102_rateM C m hT L ρ k k' *
        N ![s102_Lam T L (EuclideanSpace.single k (1 : ℝ)), s102_Lam T L (EuclideanSpace.single k' (1 : ℝ))]| ≤
          Cb * ‖N‖ := fun {ρ} hρ N => hCb L hρ N
  rcases le_total v u with h | h
  · rw [abs_of_nonneg (sub_nonneg.2 h)]
    exact s102_projHeatD_incr hT L γ hγp hγ (hG L) hCb0 hCbL hD hρint hρnn hν hΦ hj hv.1 h hu.2 y
  · rw [norm_sub_rev, abs_of_nonpos (sub_nonpos.2 h), neg_sub]
    exact s102_projHeatD_incr hT L γ hγp hγ (hG L) hCb0 hCbL hD hρint hρnn hν hΦ hj hu.1 h hv.2 y

end HRS.MS.R2Interp

end
