import HRS.MS.S104eC5G
import HRS.MS.S104J_Assembly

/-!
# S104E: unconditional existence `s104e_hex` and the final ties of the four frozen consumers

`s104e_hex`: `S104eHex d s a β ρβ ε* c₁ C₁` for every `ε*, c₁, C₁` (route C: C1 OU theory, C2 perturbation, C3 Volterra, C4 classical clauses, C5 assembly).
`s104e_hexSmall : S104jHexSmall`, hence the four frozen statements `r2_window_general_initial` (S10.5), `r2_window_errors` (S10.4), `whole_space_prepared` (S2.1(ii)),
`mov_translated_prepared` (S6.11 prepared form) with NO remaining hypothesis (`s104e_final_*`).
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

noncomputable section

namespace HRS.MS.S104e

open HRS HRS.Whole

variable {d : ℕ}

theorem s104e_hex (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {a β : ℝ} (ha : 0 < a) (hβ : 0 < β)
    (εstar c₁ C₁ : ℝ) {ρβ : Euc d → ℝ} (hρβ : IsThermalEquilibrium d s a β ρβ) :
    S104eHex d s a β ρβ εstar c₁ C₁ :=
  HRS.MS.S104e.C.c5_hex_final hd hs0 hsd ha hβ εstar c₁ C₁ hρβ

theorem s104e_hexSmall : HRS.MS.S104j.S104jHexSmall :=
  fun {_} hd s a β c₁ C₁ hs0 hsd ha hβ =>
    ⟨1, one_pos, fun εstar _ _ ρβ hρβ => s104e_hex hd hs0 hsd ha hβ εstar c₁ C₁ hρβ⟩

theorem s104e_final_general_initial : type_of% @HRS.Whole.r2_window_general_initial :=
  HRS.MS.S104j.s104j_general_initial s104e_hexSmall

theorem s104e_final_errors : type_of% @HRS.Whole.r2_window_errors :=
  HRS.MS.S104j.s104j_errors s104e_hexSmall

theorem s104e_final_whole_space_prepared : HRS.Whole.WholeSpacePreparedStatement :=
  HRS.MS.S104j.s104j_whole_space_prepared s104e_hexSmall

theorem s104e_final_mov_translated_prepared : type_of% @HRS.Whole.mov_translated_prepared :=
  HRS.MS.S104j.s104j_mov_translated_prepared s104e_hexSmall

end HRS.MS.S104e

end
