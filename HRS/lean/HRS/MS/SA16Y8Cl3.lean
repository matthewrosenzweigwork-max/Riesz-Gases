import HRS.MS.SA16Y8Cl2
import HRS.MS.SA12CompB5
import HRS.Whole.AppendixAAdjoint

/-!
# S.A.16 (SA16Y8) Cl3: `adjoint_lp_classical`

`sa16y8_adjoint_lp_classical : type_of% @HRS.Whole.AppendixA.adjoint_lp_classical`.  For `m > 2 + d/p`, the weakly continuous `W^{m,p}`
path `F` has `C²` representatives `u τ` with uniform bounds and uniformly Hölder `D²`, jointly continuous in `(τ,x)` with their
derivatives of order `≤ 2` (Cl1, Cl2); `classical_of_regular_representative` (S.A.12 B5) then shows `f r := u (t - r)` is a classical
adjoint solution, and `f r =ᵐ F (t - r)`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16Q
open HRS HRS.Whole HRS.Whole.AppendixA

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 3200000 in
theorem sa16y8_adjoint_lp_classical : type_of% @HRS.Whole.AppendixA.adjoint_lp_classical := by
  intro d hd s hs0 hsd m p _ hmp κc MB Λ ΛV G₀ νbar T χ D μ hA hκ t ht φ hφ F hF
  have hp0 : (0 : ℝ) < p := by have := (Fact.out : 2 ≤ p); linarith
  have hdp : (0 : ℝ) ≤ (d : ℝ) / p := div_nonneg (Nat.cast_nonneg d) hp0.le
  have hm : 1 ≤ m := by
    have : (1 : ℝ) ≤ m := by linarith
    exact_mod_cast this
  obtain ⟨B, hB⟩ := hF.bounded
  obtain ⟨u, K, α, hK, hα, hae, hc2, hbd, hhol, h0, h1, h2⟩ :=
    sa16y8_family d m hd p hmp t F B hB hF.wcont.2
  obtain ⟨hb, hcont⟩ := sa16y8_cont_assembly t u K α hK hα hc2 hbd hhol h0 h1 h2
  have hcl := HRS.MH.AdjointRd.Phase2SA12Companions.classical_of_regular_representative hd s hs0 hsd m hm MB Λ ΛV
    G₀ νbar T D μ hA t ht φ hφ F u hF.sol hae hc2 hb hcont
  refine ⟨fun r => u (t - r), hcl, fun r hr => ?_⟩
  exact hae (t - r) ⟨by linarith [hr.2], by linarith [hr.1]⟩

end HRS.Whole.AppendixA.Phase2SA16Q
