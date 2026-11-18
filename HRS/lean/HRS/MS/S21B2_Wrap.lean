import HRS.MS.S21A_Metric
import HRS.MS.S21U_Tilt
import HRS.MS.S103dTie
import HRS.MS.S105rReg2
import HRS.MS.S105rTie
import HRS.MS.S104bOrb1
import HRS.MS.MovEntFinal
import HRS.MS.TransOpTie

/-!
# S21B2: closing wrapper of S2.1 (ii) and the conditional tie of S6.11 prepared form

`S21aInputs` has five fields.  Four are proved in the repository and are discharged here:
* `h103`  := `HRS.MS.R2WinOrbNL.s103d_r2_window_orbits_proof` (S10.3, unconditional);
* `hreg`  := `HRS.MS.S105r.s105r_hReg` with the quantifier prefix reordered (`d, s` before `a β c₁ C₁`; the proof uses `εn = 1`);
* `hDiss` := `sb1_superDiss_of_movEnt` with `sb1_superMovEnt` (S.B.1, as in `MovEntFinal`);
* `htilt` := `s21u_tiltClass` at `J = 4d+42` (`d/2 + 2 < 4d+42`).

The remaining field is `hNL`, exactly the field of `S21aInputs`: `S104nAllOrb d s a β εstar c₁ C₁` for `εstar ≤ εn`.
`s21b2_whole_space_prepared_of_termReg` takes instead `S105rTermReg` (`S104bTermRegGen` along every thermal equilibrium for small `εstar`), the
form S104E/S104G produce; `s21b2_hNL_of_termReg` is the implication `S104bTermRegGen ⇒ S104nAllOrb` (`s104b_allOrb_of_termRegGen`).
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

noncomputable section

namespace HRS.MS.S21B2

open HRS.MS.S21A

/-- The exact statement of the field `hNL` of `S21aInputs`. -/
def S21b2NL : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ (s : ℝ), 0 ≤ s → s < d → ∀ (a β c₁ C₁ : ℝ), 0 < a → 0 < β →
    ∃ εn : ℝ, 0 < εn ∧ ∀ εstar : ℝ, εstar ≤ εn → HRS.MS.R2WinErr.S104nAllOrb d s a β εstar c₁ C₁

/-- `S104bTermRegGen` for small `ε_*` (in the form `S105rTermReg`) implies the field `hNL` of `S21aInputs`. -/
theorem s21b2_hNL_of_termReg (hTR : HRS.MS.S105r.S105rTermReg) : S21b2NL :=
  fun d hd s hs0 hsd a β c₁ C₁ ha hβ => by
    obtain ⟨εn, hεn, h⟩ := hTR hd s a β c₁ C₁ hs0 hsd ha hβ
    exact ⟨εn, hεn, fun εstar hε => HRS.MS.R2WinErr.s104b_allOrb_of_termRegGen (h εstar hε)⟩

/-- All fields of `S21aInputs` other than `hNL` are proved. -/
theorem s21b2_inputs (hNL : S21b2NL) : S21aInputs where
  h103 := HRS.MS.R2WinOrbNL.s103d_r2_window_orbits_proof
  hNL := hNL
  hreg := fun d hd s hs0 hsd a β c₁ C₁ ha hβ => HRS.MS.S105r.s105r_hReg hd s a β c₁ C₁ hs0 hsd ha hβ
  hDiss := fun d hd s hs0 hsd =>
    HRS.MS.MfeConf.sb1_superDiss_of_movEnt (by omega) hd hs0 hsd (HRS.MS.MfeConf.sb1_superMovEnt (by omega) hs0 hsd)
  htilt := fun d hd s hs0 hsd a β β₀ ha hβ hβ₀ εstar hε =>
    HRS.MS.S21.s21u_tiltClass hd hs0 hsd ha hβ hβ₀ (J := 4 * d + 42)
      (by
        have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
        have h4 : ((4 * d + 42 : ℕ) : ℝ) = 4 * (d : ℝ) + 42 := by push_cast; ring
        rw [h4]; linarith) hε

/-- **S2.1 (ii)** (`HRS.Whole.whole_space_prepared`), conditional only on the terminal-time regularity of the adjoint orbits
(`hNL`, the field of `S21aInputs`). -/
theorem s21b2_whole_space_prepared (hNL : S21b2NL) : HRS.Whole.WholeSpacePreparedStatement :=
  s21a_whole_space_prepared (s21b2_inputs hNL)

/-- Same, with `hNL` replaced by `S104bTermRegGen` for small `ε_*` (`S105rTermReg`). -/
theorem s21b2_whole_space_prepared_of_termReg (hTR : HRS.MS.S105r.S105rTermReg) :
    HRS.Whole.WholeSpacePreparedStatement :=
  s21b2_whole_space_prepared (s21b2_hNL_of_termReg hTR)

/-- **S6.11 prepared form** (`HRS.Whole.mov_translated_prepared`) conditional only on `hNL`. -/
theorem s21b2_mov_translated_prepared (hNL : S21b2NL) : type_of% @HRS.Whole.mov_translated_prepared :=
  HRS.MS.TransOp.mov_translated_prepared_of_S21ii (s21b2_whole_space_prepared hNL)

/-- **S6.11 prepared form** conditional only on `S104bTermRegGen` for small `ε_*`. -/
theorem s21b2_mov_translated_prepared_of_termReg (hTR : HRS.MS.S105r.S105rTermReg) :
    type_of% @HRS.Whole.mov_translated_prepared :=
  s21b2_mov_translated_prepared (s21b2_hNL_of_termReg hTR)

end HRS.MS.S21B2

end
