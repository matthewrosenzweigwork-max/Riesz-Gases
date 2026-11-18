import HRS.MS.R26T8AP06d3
import HRS.MS.R26T8AP00b

/-!
# S8.2 T8A P11f (part 1): nested jets are bounded by joint jets
`r26t8a_nest_le_joint`: for `Phi` of class `C^(p+q)` on `E x E`, `|nest p q Phi X z| <= |D^(p+q) Phi (X,z)|`
(the nested norm is the operator norm of the iterated directional derivative; `inl`, `inr` are norm-one).
-/

set_option autoImplicit false
noncomputable section
open Filter Topology
open scoped ContDiff

namespace HRS.MS.R26T8A

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem r26t8a_nest_le_joint {Φ : E × E → V} (p q : ℕ)
    (hΦ : ContDiff ℝ ((p + q : ℕ) : WithTop ℕ∞) Φ) (X z : E) :
    ‖r26t8a_nest p q Φ X z‖ ≤ ‖iteratedFDeriv ℝ (p + q) Φ (X, z)‖ := by
  refine ContinuousMultilinearMap.opNorm_le_bound (norm_nonneg _) fun u => ?_
  refine ContinuousMultilinearMap.opNorm_le_bound (by positivity) fun v => ?_
  rw [r26t8a_nest_eq_joint p q hΦ X z u v]
  refine (ContinuousMultilinearMap.le_opNorm _ _).trans ?_
  set l : List (E × E) := (List.ofFn u).map (ContinuousLinearMap.inl ℝ E E) ++
    (List.ofFn v).map (ContinuousLinearMap.inr ℝ E E) with hl
  have hlen : l.length = p + q := by simp [hl]
  have hprod : ∏ i : Fin (p + q), ‖l.getD i 0‖ = (∏ i : Fin p, ‖u i‖) * ∏ j : Fin q, ‖v j‖ := by
    rw [← List.prod_ofFn]
    have : List.ofFn (fun i : Fin (p + q) => ‖l.getD i 0‖) = l.map (fun e => ‖e‖) := by
      have := r26t8a_ofFn_getD l (p + q) hlen
      conv_rhs => rw [← this]
      rw [List.map_ofFn]; rfl
    rw [this, hl, List.map_append, List.prod_append]
    simp [List.map_map, Function.comp_def, List.prod_ofFn]
  rw [hprod]
  have h0 : 0 ≤ ‖iteratedFDeriv ℝ (p + q) Φ (X, z)‖ := norm_nonneg _
  calc ‖iteratedFDeriv ℝ (p + q) Φ (X, z)‖ * ((∏ i : Fin p, ‖u i‖) * ∏ j : Fin q, ‖v j‖)
      = ‖iteratedFDeriv ℝ (p + q) Φ (X, z)‖ * (∏ i : Fin p, ‖u i‖) * ∏ j : Fin q, ‖v j‖ := by ring
    _ ≤ _ := le_rfl

end HRS.MS.R26T8A
