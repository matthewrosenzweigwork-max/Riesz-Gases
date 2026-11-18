import HRS.MD.EQAsmTrans
import HRS.MD.EQBurnCltFinal
import HRS.MD.EQTransShift
import HRS.Main.EqBiasFinal

/-!
# Row 2.9, clause `centering_transition`: the frozen statement

The relocated proof of the frozen statement `HRS.Main.centering_transition`.  It is the assembly
`eq_trans_assembly_proof` (which reduces the frozen statement to the static CLT and to the shift limit)
applied to the proved static CLT `HRS.MD.EQBurnClt.eq_static_clt_proof` and the proved shift limit
`HRS.MD.EQTransShift.eq_shift_limit_proof`.  The statement is the type of the frozen theorem, taken by
`type_of%`, so the tie to the frozen statement holds by construction.
-/

namespace HRS.MD.EQFrozen29Trans

theorem centering_transition_proof {d : ℕ} : type_of% (@HRS.Main.centering_transition d) :=
  fun hd => HRS.MD.EQAsmTrans.eq_trans_assembly_proof hd
    (fun hd' => HRS.MD.EQBurnClt.eq_static_clt_proof hd')
    (HRS.MD.EQTransShift.eq_shift_limit_proof) hd

/-- The density instance of the centering transition: the frozen glue proof of `centering_transition_density`, with the proved
`centering_transition_proof` and `supercriticalBias_pos_proof` (`HRS/Main/EqBiasFinal.lean`) in place of the two frozen `sorry` statements. -/
theorem centering_transition_density_proof {d : ℕ} : type_of% (@HRS.Main.centering_transition_density d) := by
  intro hd s hs0 hsd V hV β hβ ρβ hρβ hρs
  obtain ⟨h1, h2, h3, h4⟩ := centering_transition_proof hd hs0 hsd V hV β hβ ρβ hρβ ρβ hρs
  refine ⟨h1, h2, fun hs hnc => ?_⟩
  have hd2 : (d : ℝ) / 2 < s := by
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  have hpos := HRS.Main.supercriticalBias_pos_proof hd hd2 hsd V hV β hβ ρβ hρβ hnc
  exact ⟨h3 hs hpos.ne', h4 hs hpos⟩

end HRS.MD.EQFrozen29Trans
