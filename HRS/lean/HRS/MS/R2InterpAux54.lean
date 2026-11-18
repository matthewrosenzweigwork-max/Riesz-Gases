import HRS.MS.R2InterpAux53

/-!
# S10.2 (worker S102), part 54 (packet F6, regularity): the standing hypotheses and the integrability of the cut-off Gram integrands
-/

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.R2Interp

open HRS HRS.Whole HRS.MS.CovMeas

variable {d : ℕ} {C : WholeCoeff d} {m T : ℝ} {r : ℕ} {c : MultiIndex d → ℝ}

/-- The standing assumptions on the (stationary) coefficient: orbit data, `ν ≥ 0`, an integrable nonnegative stationary density, and the existence
of classical adjoint solutions for the oscillator tests. -/
structure S102Std (C : WholeCoeff d) (m T : ℝ) (r : ℕ) (c : MultiIndex d → ℝ) : Prop where
  hD : S101Data C m T r c
  hν : 0 ≤ C.ν
  hstat : ∀ v, C.ρ v = C.ρ 0
  hint : Integrable (C.ρ 0)
  hnn : ∀ x, 0 ≤ C.ρ 0 x
  hcls : ∀ (α : MultiIndex d) (t : ℝ), t ∈ Icc (0 : ℝ) T → ∃ f, IsClassicalAdjointW C t (oscTestFun m α) f

theorem s102_gramInt (hs : S102Std C m T r c) (hT : 0 < T) (L : ℕ) : S102GramInt C m hT L := by
  intro k k'
  have hμT : min (s102_tk hT L k) (s102_tk hT L k') ≤ T := (min_le_left _ _).trans (s102_tauk hT L k).2.2
  have hcont := s102_gram_cont hT L hs.hcls (C.ρ 0) hs.hint hs.hstat k k'
  have hI : IntegrableOn (fun v => s102_gram C m hT L v k k') (Icc 0 (min (s102_tk hT L k) (s102_tk hT L k'))) :=
    hcont.integrableOn_Icc
  have : (fun v => if v ≤ min (s102_tk hT L k) (s102_tk hT L k') then s102_gram C m hT L v k k' else 0) =
      (Iic (min (s102_tk hT L k) (s102_tk hT L k'))).indicator (fun v => s102_gram C m hT L v k k') := by
    funext v; simp [indicator]
  rw [this, IntegrableOn, integrable_indicator_iff measurableSet_Iic, IntegrableOn,
    Measure.restrict_restrict measurableSet_Iic]
  refine hI.mono_set ?_
  intro v hv
  exact ⟨hv.2.1, hv.1⟩

end HRS.MS.R2Interp

end
