import HRS.MS.Fp81S21RespRecon17

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory Filter Topology Set
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.S21

/-- Synthesis of the response vector reconstructs the actual response path
at every spatial point. -/
theorem fp81s21_respRecon_path (p : Parameters) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ, 0 < p.γ →
        ∀ a : ℝ, 0 ≤ a → ∀ x : Euc p.d,
          s21gPhi (r26t3_feature_enum p.d) p.hT ((wholeSpaceIndex p.d : ℕ) : ℝ)
            (fp81s21_initial_ellv R (r26t3_qwin R a) x) = responseWindow R a x := by
  obtain ⟨δv, hv, hvhalf, hvec⟩ := fp81s21_respRecon_vector p
  obtain ⟨δo, ho, hohalf, hobs⟩ := fp81s21_respRecon_obs p
  refine ⟨min δv δo, lt_min hv ho, (min_le_left _ _).trans hvhalf,
    fun δ hδ hδle R hγ a ha x => ?_⟩
  obtain ⟨C, hC, hvector⟩ := hvec δ hδ (hδle.trans (min_le_left _ _)) R hγ
  apply fp81s21_respRecon_obs_injective p
  funext j
  rw [fp81s21_cosRecon_obs26_synthesis, (hvector a ha x).2.1 j,
    hobs δ hδ (hδle.trans (min_le_right _ _)) R hγ a ha x j]

#print axioms fp81s21_respRecon_path

end HRS.Fp81.S21
end
