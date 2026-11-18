import HRS.ME.RetGlue
import HRS.ME.RetProj
import HRS.ME.RetBurnShift
import HRS.ME.RetBurnInit
import HRS.ME.RetQual

/-!
# Proposition 5.10 (comparison and qualitative clauses): the frozen statements

`ui_comparison_proof` and `ui_qualitative_proof` have exactly the types of the frozen statements `HRS.ui_comparison`,
`HRS.ui_qualitative` (taken by `type_of%`).  Chain:

* `ret_burn_shift_proof`, `ret_burn_init_proof`: the `h`-weighted burn-in estimate with the stationary Gaussian field, and the `h`-weighted
  estimate with retained initial field, in `C([0,T];E_m)` (`HRS/ME/RetBurnShift*.lean`, `HRS/ME/RetBurnInit*.lean`; the weighted engine
  `HRS/ME/RetEngine.lean` and the transfer of the martingale hypotheses `HRS/ME/RetWeight.lean`);
* `ret_shift_of_burn_proof`, `ret_initial_of_burn_proof`: projection to the finite vector (`HRS/ME/RetProj.lean`);
* `ui_comparison_of_ret_proof`: truncation of the density and the transfer of the path law from the stationary flow (`ret_path_law_proof`,
  `HRS/ME/RetPathLaw.lean`; `HRS/ME/RetGlue*.lean`);
* `ui_qualitative_of_comparison_proof` (`HRS/ME/RetQual.lean`).
-/

namespace HRS.ME.Ret

theorem ui_comparison_proof {d : ℕ} : type_of% (@HRS.ui_comparison d) :=
  ui_comparison_of_ret_proof d (ret_initial_of_burn_proof d (ret_burn_init_proof d))
    (ret_shift_of_burn_proof d (ret_burn_shift_proof d))

theorem ui_qualitative_proof {d : ℕ} : type_of% (@HRS.ui_qualitative d) :=
  ui_qualitative_of_comparison_proof d ui_comparison_proof

end HRS.ME.Ret
