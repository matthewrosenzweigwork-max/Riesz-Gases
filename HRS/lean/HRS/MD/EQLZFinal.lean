import HRS.MD.EQLZAsm4
import HRS.MD.EQLZSm5
import HRS.MD.EQLZLevel
import HRS.MD.EQLZSgSmooth
import HRS.MD.EQLZSgSemigroup
import HRS.MD.EQLZSgSymm
import HRS.MD.EQLZSgInvariant
import HRS.MD.EQLZSgEnergy
import HRS.MD.EQLZMkMarkov
import HRS.MD.EQLZMkFdd
import HRS.MD.EQLZStat
import HRS.MD.EQLZRev
import HRS.MD.EQLZCmp
import HRS.MD.EQLZDl
import HRS.MD.EQLZMarg
import HRS.MD.EQLZCap10
import HRS.Stochastic.LyonsZhengSpec

/-! # Lyons-Zheng maximal inequality `HRS.LZ.lyonsZheng_maximal_family`: final assembly from the proved
packets (sorry-free chain; `eqlz_assembly_proof` applied to the `_proof` theorems of SG, MK, STAT, REV, CMP, DL, LN,
MARG, SM, CAP).  The frozen statement stays in `HRS/Stochastic/LyonsZhengSpec.lean`. -/

noncomputable section
namespace HRS.MD.EQLZFinal

theorem lyonsZheng_maximal_family_proof : type_of% @HRS.LZ.lyonsZheng_maximal_family :=
  HRS.MD.EQLZ.Asm.eqlz_assembly_proof
    (HRS.MD.EQLZSm.eqlz_smooth_proof
      (HRS.MD.EQLZLevel.eqlz_level_proof
        @HRS.MD.EQLZSgSmooth.eqlz_sg_smooth_proof @HRS.MD.EQLZSgSemigroup.eqlz_sg_semigroup_proof
        @HRS.MD.EQLZSgSymm.eqlz_sg_symm_proof @HRS.MD.EQLZSgInvariant.eqlz_sg_invariant_proof
        @HRS.MD.EQLZSgEnergy.eqlz_sg_energy_proof @HRS.MD.EQLZMk.eqlz_mk_markov_proof
        @HRS.MD.EQLZMk.eqlz_mk_fdd_proof @HRS.MD.EQLZStat.eqlz_stat_proof @HRS.MD.EQLZRev.eqlz_rev_proof
        @HRS.MD.EQLZCmp.eqlz_cmp_proof @HRS.MD.EQLZDl.eqlz_dl_proof)
      @HRS.MD.EQLZMarg.eqlz_marg_proof)
    @HRS.MD.EQLZ.Cap.eqlz_cap_proof @HRS.MD.EQLZMarg.eqlz_marg_proof

example := (@lyonsZheng_maximal_family_proof : type_of% @HRS.LZ.lyonsZheng_maximal_family)

end HRS.MD.EQLZFinal
end
