import HRS.MS.MfeConfAux173
import HRS.MS.MfeConfAux129

/-!
# S.B.1 (SB5): the closing assembly, unconditional

* `sb1_superMovEnt`, `sb1_subMovEnt`: `SuperMovEnt d s` (`1 ≤ d`, `0 ≤ s < d`) and `SubMovEnt d s a` (`3 ≤ d`) with `Sb1HBAll d` proved
  (`sb1_hB_all`, Aux129).
* `sb1_sub_tie`: the exact frozen statement `HRS.Whole.mfe_confined_rd_gradient_sub` (every `d`: `0 ≤ s < d - 2` forces `d ≥ 3`).
* `sb1_super_tie_d2`: the exact frozen statement `HRS.Whole.mfe_confined_rd_gradient_super` for `d ≥ 2`; the case `d = 1` of the
  super row still needs the dimension-free coercive entropy split (`sb1_diss_of_parts` uses `sb1_relEntropy_split`, `d ≥ 2`).
-/

noncomputable section

open MeasureTheory Filter Topology
open HRS HRS.Whole
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MfeConf

variable {d : ℕ}

theorem sb1_superMovEnt (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) : SuperMovEnt d s :=
  sb1_superMovEnt_of_hB hd hs0 hsd (sb1_hB_all d)

theorem sb1_subMovEnt (hd : 3 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) (a : ℝ) : SubMovEnt d s a :=
  sb1_subMovEnt_of_hB hd hs0 hsd a (sb1_hB_all d)

theorem sb1_sub_tie {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) (a : ℝ)
    (ha : (d : ℝ) < a ∧ a < (d : ℝ) + 2) :
    type_of% (@HRS.Whole.mfe_confined_rd_gradient_sub d s hs0 hsd a ha) := by
  have hd3 : 3 ≤ d := by
    have h : (2 : ℝ) < d := by linarith
    have : 2 < d := by exact_mod_cast h
    omega
  exact sb1_sub_of_hB hd3 hs0 hsd a ha (sb1_hB_all d)

theorem sb1_super_tie_d2 (hd2 : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (hsc : (d : ℝ) - 2 ≤ s) :
    type_of% (@HRS.Whole.mfe_confined_rd_gradient_super d (by omega) s hs0 hsd hsc) :=
  sb1_super_of_hB hd2 hs0 hsd hsc (sb1_hB_all d)

example := (@sb1_sub_tie : type_of% @HRS.Whole.mfe_confined_rd_gradient_sub)

end HRS.MS.MfeConf
