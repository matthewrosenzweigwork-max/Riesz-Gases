import HRS.MS.S116C02
import HRS.MS.S116C03
import HRS.MS.S116N06
import HRS.MS.S116P07
import HRS.MS.R2IidTie
import HRS.MS.R2MtAux1
import HRS.MS.S104J_Assembly
import HRS.MS.S104eFinal

/-!
# S11.6 packet A01 (`R26-T8B.A01`): the frozen `r2_log_path` (Proposition 11.6, logarithmic preparation)

Prefix `s116_`, namespace `HRS.MS.S116`.

`s116_log_path_of_termReg`: `type_of% @HRS.Whole.r2_log_path` from `S105rTermReg`.  The class constants are chosen first by `s116_class_with_reg` (C01, C03: class existence and
`S104bTermRegGen` for every thermal reference), the initial data (round-2 class and Gaussian envelope) by `s116_initial_data` (C02), then `a_*, B` by `s116_log_normalizers` (N05) with the
positive endpoint `β₊`, and `p₁` by `s116_iid_power` (N06).  The static Edgeworth clause is the native iid row `r2_static_edgeworth_iid_proof`; the path clause is `s116_iid_path` (P07).
`s116_log_path_proof`: the same with NO remaining hypothesis (`S105rTermReg` from `s104j_termReg s104e_hexSmall`).
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

noncomputable section

namespace HRS.MS.S116

open HRS HRS.Whole

theorem s116_log_path_of_termReg (hTR : HRS.MS.S105r.S105rTermReg) :
    type_of% @HRS.Whole.r2_log_path := by
  intro d hd a β ha hβ T hT βplus hβplus
  obtain ⟨εstar, c₁, C₁, hε, hc, hC, hcl, hreg⟩ := s116_class_with_reg hTR hd a β ha hβ
  obtain ⟨M, L, Cg, cg, hCg, hcg, hdata⟩ := s116_initial_data hd a β εstar c₁ C₁ ha hβ
  obtain ⟨astar, B, hastar, hB, hnorm⟩ := s116_log_normalizers hd M L Cg cg βplus hcg hβplus
  obtain ⟨p₁, hp₁, hpow⟩ := s116_iid_power hd M L Cg cg β hcg hβ
  refine ⟨εstar, c₁, C₁, hε, hc, hC, hcl, astar, hastar, fun ρβ hρβ ρ htraj => ?_⟩
  obtain ⟨hr2, hG⟩ := hdata ρβ hρβ ρ htraj
  refine ⟨⟨B, fun N hN θ hθ => hnorm (ρ 0) hr2 hG N hN θ hθ⟩,
    ⟨p₁, hp₁, fun p hp1 hp2 => ?_⟩, fun m hm => ?_, fun k m hk hm hex hmem hsum => ?_⟩
  · obtain ⟨Bp, hBp⟩ := hpow p hp1 hp2
    exact ⟨Bp, fun N hN => hBp (ρ 0) hr2 hG N hN⟩
  · exact HRS.MS.R2Iid.r2_static_edgeworth_iid_proof hd m hm (ρ 0) hr2.prob.measurable hr2.prob.nonneg
      hr2.prob.integral_one
  · exact s116_iid_path hd a β T ha hβ hT εstar c₁ C₁ ρβ hρβ (hreg ρβ hρβ) ρ htraj hr2.prob k m hk hm
      hex hmem hsum

theorem s116_log_path_proof : type_of% @HRS.Whole.r2_log_path :=
  s116_log_path_of_termReg (HRS.MS.S104j.s104j_termReg HRS.MS.S104e.s104e_hexSmall)

example := (@s116_log_path_proof : type_of% @HRS.Whole.r2_log_path)

end HRS.MS.S116

end
