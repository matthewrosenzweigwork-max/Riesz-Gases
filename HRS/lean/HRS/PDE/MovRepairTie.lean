import HRS.PDE.MovAFinal
import HRS.PDE.MovCFinal
import HRS.PDE.MovEFinal

/-!
# SPEC-GF3: ties of the three repaired MOV statements (`0 < T`; ISSUES MOVA, MOVC, MOVD/MOVE, repaired 2026-10-17)
-/

noncomputable section

namespace HRS

variable {d N : ℕ}

theorem movT_srcReg_decomp_proof : type_of% @HRS.movT_srcReg_decomp := @movT_srcReg_decomp_proof_pos

example := (@movT_srcReg_decomp_proof : type_of% @HRS.movT_srcReg_decomp)

theorem movT_srcReg_tendsto_proof : type_of% @HRS.movT_srcReg_tendsto := @movT_srcReg_tendsto_proof_pos

example := (@movT_srcReg_tendsto_proof : type_of% @HRS.movT_srcReg_tendsto)

theorem movT_source_exp_scaled_uniform_proof : type_of% @HRS.movT_source_exp_scaled_uniform :=
  @movT_source_exp_scaled_uniform_proof_pos

example := (@movT_source_exp_scaled_uniform_proof : type_of% @HRS.movT_source_exp_scaled_uniform)

end HRS
