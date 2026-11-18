import HRS.MH.NoLowerBound1
import HRS.Main.Headline

/-!
# `HRS.Main.general_fluctuation_noLowerBound` (remark after Theorem 2.1, TeX M L627-630)

The three estimates of Theorem 2.1 for gradient dynamics with `s + 2 - d ≤ 1`, without a positive lower density bound.
Proof: `gff_core` (`HRS/Main/GFFinal3.lean`) with the extra hypothesis `S.s + 2 - d ≤ 1` and the evolution provider
`gf_ev_grad_noLB` (adjoint regime `R1` or `R2c`) in place of `gf_ev_grad_proof`; this is the proof of
`general_fluctuation_proof` (`HRS/Main/GFFinal5.lean`) with the hypothesis changed.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MH.NoLB

open HRS HRS.GF

variable {d : ℕ}

theorem general_fluctuation_noLowerBound_proof : type_of% @HRS.Main.general_fluctuation_noLowerBound := by
  intro d b
  obtain ⟨K, hK0, hev⟩ := gf_ev_grad_noLB b
  obtain ⟨C₀min, hcore⟩ := gff_core b (-1) (fun S => S.s + 2 - (d : ℝ) ≤ 1) (fun S => (S.γ : ℝ))
    (fun S => le_rfl) (fun S x => x) K
    (fun S hS hMF hPos N => by
      obtain ⟨EV, hEV⟩ := hev S hS hMF hPos N
      exact ⟨EV, hEV, fun x => by rw [hEV.j_eq, embed_self]⟩)
  refine ⟨C₀min, fun C₀ hC₀ => ?_⟩
  obtain ⟨C, hC, h⟩ := hcore C₀ hC₀
  refine ⟨C, hC, ?_⟩
  intro S hS hMF hPos N hN Ω _ P _ X₀ W hW X hX hF hE η₀ hη hind hfin Y hY
  exact h S hS hMF hPos N hN P X₀ W X hX hF hE η₀ hη hind hfin Y hY

end HRS.MH.NoLB
