import HRS.MS.R26T8AL3h
import HRS.MS.R26T8AF06
import HRS.MS.R26T8AF05b
import HRS.MS.R26T8AF05d

/-!
# S8.2 observed-time layer, packet T8A.F07 (helper 07e): the thermal drift term on `SobSmooth` functions

For thermal `ρ` (critical), `⟪forceMean ρ x, ∇u x⟫ = ∑_j forceMean_j(x) ∂_j u(x)`, and
`sobolevNormE r (⟪F, ∇u⟫) ≤ C · sobolevNormE (r+1) u` with `C` independent of the `SobSmooth` function `u`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators ContDiff FourierTransform ComplexConjugate
namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.PDE.ToolboxRd HRS.PDE.ToolboxRd.FourierAux HRS.MS.Phase2S82

variable {d : ℕ}

theorem r26t8a_f07e_inner (F g : Euc d) : inner ℝ F g = ∑ j : Fin d, F j * g j := by
  simp [PiLp.inner_apply, mul_comm]

theorem r26t8a_f07e (d : ℕ) (hd : 2 ≤ d) (a beta : ℝ) (ha : 0 < a) (hbeta : 0 < beta)
    (rho : Euc d → ℝ) (hrho : IsThermalEquilibrium d (criticalS d) a beta rho) (r : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : Euc d → ℝ, r26t8a_SobSmooth u →
      sobolevNormE (r : ℝ) (fun x => inner ℝ (forceMean rho x) (gradient u x)) ≤
        ENNReal.ofReal C * sobolevNormE ((r : ℝ) + 1) u := by
  obtain ⟨-, hF⟩ := r26t8a_f06_force_comp d hd a beta ha hbeta rho hrho
  have hc : ∀ j : Fin d, ContDiff ℝ ∞ (fun x => forceMean rho x j) := fun j =>
    contDiff_infty.2 fun N => (hF j N).1
  have hcb : ∀ j : Fin d, ∀ n : ℕ, ∃ B : ℝ, ∀ x, ‖iteratedFDeriv ℝ n (fun x => forceMean rho x j) x‖ ≤ B :=
    fun j n => by
      obtain ⟨B, hB⟩ := (hF j n).2 n le_rfl
      exact ⟨B, fun x => hB ⟨x, rfl⟩⟩
  choose Cj hCj0 hCj using fun j : Fin d => r26t8a_l3_unif _ (hc j) (hcb j) r
  refine ⟨∑ j : Fin d, Cj j, Finset.sum_nonneg fun j _ => hCj0 j, fun u hu => ?_⟩
  have e : (fun x => inner ℝ (forceMean rho x) (gradient u x)) =
      fun x => ∑ j : Fin d, (fun x => forceMean rho x j) x * r26t8a_l3_D j u x := by
    funext x
    rw [r26t8a_f07e_inner]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only
    rw [r26t8a_f05b_grad_comp u x j]
    rfl
  rw [e]
  refine le_trans (r26t8a_f05c_sob_sum (r : ℝ) Finset.univ
    (fun j x => (fun x => forceMean rho x j) x * r26t8a_l3_D j u x)) ?_
  refine le_trans (r26t8a_f05d_sum_comb Finset.univ (fun j => Cj j) (fun j => hCj0 j) _
    (sobolevNormE ((r : ℝ) + 1) u) (fun j _ => ?_)) le_rfl
  refine (hCj j _ (r26t8a_l3_sob_D u hu j)).trans ?_
  exact r26t8a_f05d_mulL (r26t8a_l2 hu j r) _

end HRS.MS.R26T8A

end
