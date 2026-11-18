import HRS.MS.CritWholeDensBound
import HRS.MS.CritWholeResponse
import HRS.MS.WrStatic
import HRS.Whole.Critical

/-!
# S8.1 XS (S81d): the written assembly of the frozen static endpoint `critical_whole_marginal`

`s81d_critical_whole_marginal : type_of% @HRS.Whole.critical_whole_marginal` (tie to the frozen statement).  Inputs: CR12
(`s81d_critical_density_bound`), the actual `euc_static_proof` (Gibbs well-definedness), `wr13d_theta` (the native full marginal
density), and `s81bd_critical_response` (strict positivity and `L²` membership of the critical bias).
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators
open HRS HRS.Whole

namespace HRS.Whole.S81b

/-- The frozen static endpoint, assembled from CR12 (exact type tie). -/
theorem s81d_critical_whole_marginal : type_of% @HRS.Whole.critical_whole_marginal := by
  intro d hd ρ hρ hbdd hlip βm βp hβm hβ
  obtain ⟨M, hM⟩ := hbdd
  obtain ⟨Λ, hΛ⟩ := hlip
  have hd1 : 1 ≤ d := by omega
  have hs0 : 0 < (d : ℝ) / 2 := s81c_hs0 hd1
  have hsd : (d : ℝ) / 2 < d := s81c_hsd hd1
  obtain ⟨C, hC0, hC⟩ := s81d_critical_density_bound hd M Λ βm βp hβm hβ
  obtain ⟨Cstat, hstat⟩ := HRS.MS.Wr.euc_static_proof hd hs0 hsd βm βp M hβm hβ
  refine ⟨?_, C, ?_⟩
  · intro β hβ0
    exact (HRS.Whole.BreakdownS81.s81bd_critical_response hd ρ hρ ⟨M, hM⟩ hΛ.continuous β hβ0).2
  · intro β hβmem N hN
    let D : Data d M βm βp := ⟨ρ, hρ, hM, β, hβmem⟩
    have hβ0 : 0 < β := hβm.trans_le hβmem.1
    have hEst := hC D hΛ N hN
    have hBias := (HRS.Whole.BreakdownS81.s81bd_critical_response hd ρ hρ
      ⟨M, hM⟩ hΛ.continuous β hβ0).1.1
    obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
    have hn : 1 ≤ n := by omega
    refine ⟨(hstat ρ hρ hM β hβmem (n + 1) hN).1, hBias, theta D (n + 1), ?_, ?_, ?_, hEst.1, ?_⟩
    · exact HRS.MS.Wr.wr13d_theta_meas hd hs0 hsd hρ hM hβ0.le n
    · intro x
      exact (HRS.MS.Wr.wr13d_theta_pos hd hs0 hsd hρ hM hβ0.le hn x).le
    · exact HRS.MS.Wr.wr13d_firstMarginal_eq hd hs0 hsd hρ hM hβ0.le n
    · simpa only [rate, mul_div_assoc] using hEst.2

end HRS.Whole.S81b
