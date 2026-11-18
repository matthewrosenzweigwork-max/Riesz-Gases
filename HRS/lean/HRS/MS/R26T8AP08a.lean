import HRS.MS.R26T8AP06d3
import HRS.MS.R26T8AMix

/-!
# S8.2 T8A P08 (part a): the nested jet of `Ψ(Y,-w)` at `z` is bounded by the nested jet of `Ψ` at `-z`
-/

set_option autoImplicit false
noncomputable section
open Filter Topology
open scoped ContDiff

namespace HRS.MS.R26T8A

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem r26t8a_f24_nest_negw {Ψ : E × E → ℝ} (p q : ℕ) (hΨ : ContDiff ℝ ((p + q : ℕ) : WithTop ℕ∞) Ψ) (X z : E) :
    ‖r26t8a_nest p q (fun Yw : E × E => Ψ (Yw.1, -Yw.2)) X z‖ ≤ ‖r26t8a_nest p q Ψ X (-z)‖ := by
  set N : (E × E) →L[ℝ] (E × E) :=
    (ContinuousLinearMap.fst ℝ E E).prod (-(ContinuousLinearMap.snd ℝ E E)) with hN
  have hNw : ∀ w : E × E, N w = (w.1, -w.2) := fun w => by simp [hN]
  have hΦ : ContDiff ℝ ((p + q : ℕ) : WithTop ℕ∞) (fun Yw : E × E => Ψ (Yw.1, -Yw.2)) :=
    hΨ.comp (contDiff_fst.prodMk contDiff_snd.neg)
  refine ContinuousMultilinearMap.opNorm_le_bound (norm_nonneg _) fun u => ?_
  refine ContinuousMultilinearMap.opNorm_le_bound (by positivity) fun v => ?_
  rw [r26t8a_nest_eq_joint p q hΦ X z u v]
  have hfun : (fun Yw : E × E => Ψ (Yw.1, -Yw.2)) = Ψ ∘ N := by funext w; simp [hNw]
  rw [hfun, N.iteratedFDeriv_comp_right hΨ (X, z) le_rfl, ContinuousMultilinearMap.compContinuousLinearMap_apply]
  have hargs : (fun i : Fin (p + q) => N (((List.ofFn u).map (ContinuousLinearMap.inl ℝ E E) ++
      (List.ofFn v).map (ContinuousLinearMap.inr ℝ E E)).getD i 0)) =
      fun i : Fin (p + q) => (((List.ofFn u).map (ContinuousLinearMap.inl ℝ E E) ++
      (List.ofFn (fun j => -v j)).map (ContinuousLinearMap.inr ℝ E E)).getD i 0) := by
    funext i
    have h1 : N (((List.ofFn u).map (ContinuousLinearMap.inl ℝ E E) ++
        (List.ofFn v).map (ContinuousLinearMap.inr ℝ E E)).getD i 0) =
        (((List.ofFn u).map (ContinuousLinearMap.inl ℝ E E) ++
        (List.ofFn v).map (ContinuousLinearMap.inr ℝ E E)).map N).getD i 0 := by
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
      cases ((List.ofFn u).map (ContinuousLinearMap.inl ℝ E E) ++
        (List.ofFn v).map (ContinuousLinearMap.inr ℝ E E))[(i : ℕ)]? <;> simp [hNw]
    rw [h1, List.map_append, List.map_map, List.map_map]
    have e1 : (N ∘ ContinuousLinearMap.inl ℝ E E) = ContinuousLinearMap.inl ℝ E E := by
      funext a; ext <;> simp [hNw]
    have e2 : (N ∘ ContinuousLinearMap.inr ℝ E E) =
        (ContinuousLinearMap.inr ℝ E E) ∘ (fun b : E => -b) := by
      funext b; ext <;> simp [hNw]
    have e3 : (List.ofFn v).map (fun b : E => -b) = List.ofFn (fun j => -v j) := by
      rw [List.map_ofFn]; rfl
    rw [e1, e2, ← List.map_map, e3]
  rw [hargs, hNw]
  have hn := r26t8a_nest_eq_joint p q hΨ X (-z) u (fun j => -v j)
  simp only [] at hn ⊢
  rw [← hn]
  have h1 := (r26t8a_nest p q Ψ X (-z) u).le_opNorm (fun j => -v j)
  have h2 := (r26t8a_nest p q Ψ X (-z)).le_opNorm u
  have h3 : ∏ j : Fin q, ‖(fun j => -v j) j‖ = ∏ j : Fin q, ‖v j‖ := by simp
  rw [h3] at h1
  have h4 : 0 ≤ ∏ j : Fin q, ‖v j‖ := Finset.prod_nonneg fun _ _ => norm_nonneg _
  calc ‖r26t8a_nest p q Ψ X (-z) u (fun j => -v j)‖ ≤ ‖r26t8a_nest p q Ψ X (-z) u‖ * ∏ j : Fin q, ‖v j‖ := h1
    _ ≤ (‖r26t8a_nest p q Ψ X (-z)‖ * ∏ i : Fin p, ‖u i‖) * ∏ j : Fin q, ‖v j‖ :=
        mul_le_mul_of_nonneg_right h2 h4

end HRS.MS.R26T8A
