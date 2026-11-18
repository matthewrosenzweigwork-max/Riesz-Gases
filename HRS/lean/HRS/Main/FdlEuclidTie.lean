import HRS.MC.D3EAsm
import HRS.Appendix.FDL

/-! Tie: `HRS.MC.D3EAsm.fdl_kernel_euclid_proof` has the type of the frozen statement `HRS.fdl_kernel_euclid`
(`HRS/Appendix/FDL.lean`, repaired by FDL-E1: item (i), third bullet, `(s = 0 → ‖z‖ ≤ 1)`). -/

example := (@HRS.MC.D3EAsm.fdl_kernel_euclid_proof : type_of% @HRS.fdl_kernel_euclid)
