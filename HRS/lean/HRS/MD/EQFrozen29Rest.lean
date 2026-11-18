import HRS.MD.EQAsmDirect
import HRS.MD.EQAsmInit
import HRS.MD.EQInterpMain
import HRS.MD.EQStrongFinal
import HRS.MD.EQGaussLift
import HRS.MD.EQLawFlow
import HRS.MD.EQLawPath
import HRS.MD.EQBurnWire

/-!
# Row 2.9, the direct, initial and interpolation clauses: the frozen statements

The relocated proofs of the frozen statements `HRS.Main.equilibrium_paths_direct`, `HRS.Main.equilibrium_initial_law` and
`HRS.Main.equilibrium_paths_interpolation`.  Each is the corresponding assembly applied to the proved ingredients:
* direct: `eq_direct_assembly_proof` with `eq_burnin_proof` (P8), `eq_path_stationary_proof`, `eq_flow_exists_proof`;
* initial law: `eq_init_assembly_proof` with the direct clause, `eq_flow_exists_proof`, `equilibrium_marginal_L2_proof`;
* interpolation: `eq_interp_assembly_proof` with the direct clause, `eq_strong_moment_proof`, `eq_gauss_lift_proof`,
  `eq_flow_exists_proof`.
The statements are the `type_of%` of the frozen theorems, so the tie holds by construction.
-/

namespace HRS.MD.EQFrozen29Rest

theorem equilibrium_paths_direct_proof {d : ℕ} : type_of% (@HRS.Main.equilibrium_paths_direct d) :=
  fun hd => HRS.MD.EQAsmDirect.eq_direct_assembly_proof hd (@HRS.MD.EQBurnWire.eq_burnin_proof d)
    (@HRS.MD.EQLawPath.eq_path_stationary_proof d) (@HRS.MD.EQLawFlow.eq_flow_exists_proof d) hd

theorem equilibrium_initial_law_proof {d : ℕ} : type_of% (@HRS.Main.equilibrium_initial_law d) :=
  fun hd => HRS.MD.EQAsmInit.eq_init_assembly_proof hd (@equilibrium_paths_direct_proof d)
    (@HRS.MD.EQLawFlow.eq_flow_exists_proof d) (@HRS.Main.equilibrium_marginal_L2_proof d) hd

theorem equilibrium_paths_interpolation_proof {d : ℕ} :
    type_of% (@HRS.Main.equilibrium_paths_interpolation d) :=
  fun hd => HRS.MD.EQInterp.eq_interp_assembly_proof hd (@equilibrium_paths_direct_proof d)
    (@HRS.MD.EQStrong.eq_strong_moment_proof d) (@HRS.MD.EQGaussLift.eq_gauss_lift_proof d)
    (@HRS.MD.EQLawFlow.eq_flow_exists_proof d) hd

end HRS.MD.EQFrozen29Rest
