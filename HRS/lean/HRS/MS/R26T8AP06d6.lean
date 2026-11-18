import HRS.MS.R26T8AP06d4
import HRS.MS.R26T8AP06d5
import HRS.MS.R26T8AP03a
import HRS.MS.R26T8AP01
import HRS.MS.R26T8AP21g

/-!
# S8.2 local Newton layer, packet T8A.P06d (part 6): helper lemmas for the nested extension
`r26t8a_iterDir_nhds` (germ dependence) and `r26t8a_p06d_nest_continuous` (joint continuity of a nested jet of a globally smooth function).
-/

set_option autoImplicit false
noncomputable section
open Filter Topology
open scoped ContDiff

namespace HRS.MS.R26T8A

section H

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem r26t8a_iterDir_nhds {f g : E → V} {x : E} (h : f =ᶠ[𝓝 x] g) :
    ∀ l : List E, r26t8a_iterDir l f =ᶠ[𝓝 x] r26t8a_iterDir l g
  | [] => h
  | m :: ms => by
    have ih := (r26t8a_iterDir_nhds h ms).eventuallyEq_nhds
    filter_upwards [ih] with y hy
    exact congrArg (fun T : E →L[ℝ] V => T m) (hy.fderiv_eq (𝕜 := ℝ))

theorem r26t8a_p06d_nest_continuous {d : ℕ} {Ψ : Euc d × Euc d → V} (p q : ℕ) (hΨ : ContDiff ℝ ((p + q : ℕ) : WithTop ℕ∞) Ψ) :
    Continuous (fun w : Euc d × Euc d => r26t8a_nest p q Ψ w.1 w.2) := by
  have hq : ContDiff ℝ (q : WithTop ℕ∞) Ψ := hΨ.of_le (by exact_mod_cast Nat.le_add_left q p)
  set G : Euc d × Euc d → ContinuousMultilinearMap ℝ (fun _ : Fin q => Euc d) V := fun Yw =>
    (iteratedFDeriv ℝ q Ψ Yw).compContinuousLinearMap (fun _ => ContinuousLinearMap.inr ℝ (Euc d) (Euc d)) with hG
  have hGd : ContDiff ℝ (p : WithTop ℕ∞) G :=
    (ContinuousMultilinearMap.compContinuousLinearMapL (fun _ : Fin q => ContinuousLinearMap.inr ℝ (Euc d) (Euc d)) :
      ContinuousMultilinearMap ℝ (fun _ : Fin q => Euc d × Euc d) V →L[ℝ]
        ContinuousMultilinearMap ℝ (fun _ : Fin q => Euc d) V).contDiff.comp
      (hΨ.iteratedFDeriv_right (m := (p : WithTop ℕ∞)) (by exact_mod_cast le_refl (p + q)))
  have e : ∀ X z : Euc d, r26t8a_nest p q Ψ X z =
      (iteratedFDeriv ℝ p G (X, z)).compContinuousLinearMap (fun _ => ContinuousLinearMap.inl ℝ (Euc d) (Euc d)) := by
    intro X z
    unfold r26t8a_nest
    have h1 : (fun Y => iteratedFDeriv ℝ q (fun w => Ψ (Y, w)) z) = fun Y => G (Y, z) := by
      funext Y; exact r26t8a_slice_jet_inr' hq Y z
    rw [h1]
    exact r26t8a_slice_jet hGd X z
  have : (fun w : Euc d × Euc d => r26t8a_nest p q Ψ w.1 w.2) = fun w =>
      (iteratedFDeriv ℝ p G w).compContinuousLinearMap (fun _ => ContinuousLinearMap.inl ℝ (Euc d) (Euc d)) :=
    funext fun w => e w.1 w.2
  rw [this]
  exact (ContinuousMultilinearMap.compContinuousLinearMapL (fun _ : Fin p => ContinuousLinearMap.inl ℝ (Euc d) (Euc d)) :
    ContinuousMultilinearMap ℝ (fun _ : Fin p => Euc d × Euc d) (ContinuousMultilinearMap ℝ (fun _ : Fin q => Euc d) V) →L[ℝ]
      ContinuousMultilinearMap ℝ (fun _ : Fin p => Euc d) (ContinuousMultilinearMap ℝ (fun _ : Fin q => Euc d) V)).continuous.comp (hGd.continuous_iteratedFDeriv le_rfl)

end H

end HRS.MS.R26T8A
