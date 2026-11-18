import HRS.MS.R2ChaosAux51

/-!
# HRS.MS.R2ChaosTie -- S9.4 `round2_integrated_chaos`

Packet S94.  The frozen statement `HRS.Whole.round2_integrated_chaos` (Proposition 9.4) is proved by the chain
`R2ChaosAux1 .. R2ChaosAux51`:

* `s94_R1` (time-dependent finite-rank approximants, S9.1 + measurable selection),
* `s94_exists_F_full` (the jointly measurable Wick-chaos version `F`; ONB existence `s94_exists_onb`, Cauchy property `s94_flim_cauchy`,
  basis independence `s94_wick_clause`),
* `s94_part_i`, `s94_part_ii`, `s94_part_iii` (convergence in law, integrated process, `r`-Wasserstein).
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open MeasureTheory ProbabilityTheory Function Set Filter
open scoped ENNReal NNReal Topology

noncomputable section

namespace HRS.MS.R2Chaos

open HRS.Whole

theorem round2_integrated_chaos_proof : type_of% @HRS.Whole.round2_integrated_chaos := by
  intro d hd s hs0 hs M L b p K B T hb hp hT ρ hρ Ω _ P _ X Ω' _ P' _ ξ hset h hmeas hker
  obtain ⟨C₁, n, u, Cm, hu, hCm, hCb, hCs, hA⟩ := s94_R1 hd hs0 hs hρ hT hmeas hker
  obtain ⟨F, hFm, hF2, hWick, ηF, hηF0, hηF, hFη⟩ :=
    s94_exists_F_full hd hs0 hs hρ hset hT hker hu hCm hCs hA
  refine ⟨F, hFm, hF2, hWick, ?_⟩
  intro k aa haa
  have hi := s94_part_i hd hs0 hs hb hp hρ hset hT hmeas hker hu hCm hCb hCs hA hFm hF2 hηF0 hηF hFη haa
  exact ⟨hi, s94_part_ii hT hF2 (fun N => s94_quad_ae_memLp_all hd hs0 hs hb hp hρ hset hT hmeas hker N) hi,
    s94_part_iii hd hs0 hs hb hp hρ hset hT hmeas hker hu hCm hCb hCs hA hFm hF2 hηF0 hηF hFη haa⟩

end HRS.MS.R2Chaos
