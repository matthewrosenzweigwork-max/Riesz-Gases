import HRS.MS.R26T8AF13a

/-!
# S8.2 observed-time layer, packet T8A.F13 (helper 13b): pointwise derivative bounds from a gradient cbNorm bound

If `cbNormVecE K (∇g) ≤ ofReal X` then `‖∂^k g x‖ ≤ X` for `1 ≤ k ≤ K+1` and every `x`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators ContDiff FourierTransform ComplexConjugate
namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.PDE.ToolboxRd HRS.PDE.ToolboxRd.FourierAux

variable {d : ℕ}

theorem r26t8a_f13b_bound (g : Euc d → ℝ) (hg : ContDiff ℝ ∞ g) (K : ℕ) (X : ℝ) (hX : 0 ≤ X)
    (h : cbNormVecE K (fun y => gradient g y) ≤ ENNReal.ofReal X) (k : ℕ) (hk1 : 1 ≤ k)
    (hkK : k ≤ K + 1) (x : Euc d) :
    ‖iteratedFDeriv ℝ k g x‖ ≤ X := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  have hk' : k' ≤ K := by omega
  have h1 := r26t8a_f13a_succ_le g hg k' x
  have hterm : ENNReal.ofReal ‖iteratedFDeriv ℝ k' (fun y => gradient g y) x‖ ≤
      cbNormVecE K (fun y => gradient g y) := by
    unfold cbNormVecE
    refine le_trans ?_ (Finset.single_le_sum (f := fun j => ⨆ x, ENNReal.ofReal
      ‖iteratedFDeriv ℝ j (fun y => gradient g y) x‖) (fun j _ => zero_le')
      (Finset.mem_range.2 (show k' < K + 1 by omega)))
    exact le_iSup (fun x => ENNReal.ofReal ‖iteratedFDeriv ℝ k' (fun y => gradient g y) x‖) x
  have h2 : ENNReal.ofReal ‖iteratedFDeriv ℝ k' (fun y => gradient g y) x‖ ≤ ENNReal.ofReal X :=
    hterm.trans h
  exact h1.trans ((ENNReal.ofReal_le_ofReal_iff hX).1 h2)

end HRS.MS.R26T8A

end
