import HRS.PDE.MovFAux5
import HRS.PDE.MovAAux19
import HRS.PDE.TorusFPExistAux15

/-!
# MOVF Aux6: the `C^{1,2}` regularity core
`IsC12Test` from a weak solution whose densities are `C²` in `x` with `C²`-jets jointly continuous in `(r,x)`.

* `movf_cont_*`: copies of the joint-continuity lemmas of `MovAAux16` / `TorusFPExistAux15` using only the
  field `cont_c2` (not the whole `IsC12Test`).
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS

variable {d N : ℕ}

section Lite

variable {T : ℝ} {ρ : ℝ → Torus d → ℝ}

theorem movf_cont_lift_f (hcc : ∀ j ≤ 2, Continuous fun p : Set.Icc (0 : ℝ) T × Euc d =>
    iteratedFDeriv ℝ j (Torus.lift (ρ p.1)) p.2) :
    Continuous fun p : Set.Icc (0 : ℝ) T × Euc d => ρ p.1 (Torus.mk p.2) := by
  have h0 := (continuousMultilinearCurryFin0 ℝ (Euc d) ℝ).continuous.comp (hcc 0 (by norm_num))
  refine h0.congr fun p => ?_
  simp [iteratedFDeriv_zero_eq_comp, Torus.lift]

theorem movf_cont_rho (hcc : ∀ j ≤ 2, Continuous fun p : Set.Icc (0 : ℝ) T × Euc d =>
    iteratedFDeriv ℝ j (Torus.lift (ρ p.1)) p.2) :
    Continuous fun p : Set.Icc (0 : ℝ) T × Torus d => ρ p.1 p.2 :=
  d1_continuous_prod_of_lift (h := fun p : Set.Icc (0 : ℝ) T × Torus d => ρ p.1 p.2)
    (movf_cont_lift_f hcc)

theorem movf_cont_gradient_lift (hcc : ∀ j ≤ 2, Continuous fun p : Set.Icc (0 : ℝ) T × Euc d =>
    iteratedFDeriv ℝ j (Torus.lift (ρ p.1)) p.2) :
    Continuous fun p : Set.Icc (0 : ℝ) T × Euc d => gradient (Torus.lift (ρ p.1)) p.2 := by
  have h1 := (continuousMultilinearCurryFin1 ℝ (Euc d) ℝ).continuous.comp (hcc 1 (by norm_num))
  have h2 := (InnerProductSpace.toDual ℝ (Euc d)).symm.continuous.comp h1
  refine h2.congr fun p => ?_
  simp only [Function.comp_apply]
  unfold gradient
  rw [fderiv_eq_curry]

theorem movf_cont_laplacian_lift (hcc : ∀ j ≤ 2, Continuous fun p : Set.Icc (0 : ℝ) T × Euc d =>
    iteratedFDeriv ℝ j (Torus.lift (ρ p.1)) p.2) :
    Continuous fun p : Set.Icc (0 : ℝ) T × Euc d => Laplacian.laplacian (Torus.lift (ρ p.1)) p.2 := by
  have h1 := (continuous_curry2 d).comp (hcc 2 le_rfl)
  have e : (fun p : Set.Icc (0 : ℝ) T × Euc d => Laplacian.laplacian (Torus.lift (ρ p.1)) p.2) =
      fun p => ∑ i : Fin d, (curry2 d (iteratedFDeriv ℝ 2 (Torus.lift (ρ p.1)) p.2))
        (EuclideanSpace.basisFun (Fin d) ℝ i) (EuclideanSpace.basisFun (Fin d) ℝ i) := by
    funext p
    rw [d1_laplacian_eq_sum]
    simp only [← fderiv_fderiv_eq_curry2]
  rw [e]
  exact continuous_finset_sum _ fun i _ => (h1.clm_apply continuous_const).clm_apply continuous_const

theorem movf_cont_dρ (hcc : ∀ j ≤ 2, Continuous fun p : Set.Icc (0 : ℝ) T × Euc d =>
    iteratedFDeriv ℝ j (Torus.lift (ρ p.1)) p.2) (j : Fin d) :
    Continuous fun p : Set.Icc (0 : ℝ) T × Torus d => Torus.partialDeriv j (ρ p.1) p.2 := by
  refine d1_continuous_prod_of_lift (h := fun p : Set.Icc (0 : ℝ) T × Torus d =>
    Torus.partialDeriv j (ρ p.1) p.2) ?_
  have h1 := (EuclideanSpace.proj j : Euc d →L[ℝ] ℝ).continuous.comp (movf_cont_gradient_lift hcc)
  refine h1.congr fun p => ?_
  simp only [Function.comp_apply]
  rw [← mova_grad_apply, grad_mk]
  rfl

theorem movf_cont_lapρ (hcc : ∀ j ≤ 2, Continuous fun p : Set.Icc (0 : ℝ) T × Euc d =>
    iteratedFDeriv ℝ j (Torus.lift (ρ p.1)) p.2) :
    Continuous fun p : Set.Icc (0 : ℝ) T × Torus d => Torus.laplacian (ρ p.1) p.2 := by
  refine d1_continuous_prod_of_lift (h := fun p : Set.Icc (0 : ℝ) T × Torus d =>
    Torus.laplacian (ρ p.1) p.2) ?_
  refine (movf_cont_laplacian_lift hcc).congr fun p => ?_
  simp only
  rw [laplacian_mk]

theorem movf_cont_F (D : DynData d) (hck : ∀ r ∈ Set.Icc (0 : ℝ) T, Torus.IsCk 2 (ρ r))
    (hcc : ∀ j ≤ 2, Continuous fun p : Set.Icc (0 : ℝ) T × Euc d =>
      iteratedFDeriv ℝ j (Torus.lift (ρ p.1)) p.2) (j : Fin d) :
    Continuous fun p : Set.Icc (0 : ℝ) T × Torus d => mova_F D (ρ p.1) j p.2 := by
  have hgi := mova_integrable_periodicRiesz (b15_one_le_d D) D.hs0 D.hsd
  have h := mova_continuous_convFun_param (P := Set.Icc (0 : ℝ) T)
    (f := fun r y => Torus.partialDeriv j (ρ r.1) y) hgi (movf_cont_dρ hcc j)
  refine h.congr fun p => ?_
  rw [mova_F_eq D (mova_isCk_one_of_two (hck p.1.1 p.1.2)) j]

theorem movf_cont_convLap (D : DynData d)
    (hcc : ∀ j ≤ 2, Continuous fun p : Set.Icc (0 : ℝ) T × Euc d =>
      iteratedFDeriv ℝ j (Torus.lift (ρ p.1)) p.2) :
    Continuous fun p : Set.Icc (0 : ℝ) T × Torus d =>
      convFun (periodicRiesz d D.s) (Torus.laplacian (ρ p.1)) p.2 := by
  have hgi := mova_integrable_periodicRiesz (b15_one_le_d D) D.hs0 D.hsd
  exact mova_continuous_convFun_param (P := Set.Icc (0 : ℝ) T)
    (f := fun r y => Torus.laplacian (ρ r.1) y) hgi (movf_cont_lapρ hcc)

theorem movf_cont_pde (D : DynData d) (hV : Torus.IsCk 2 D.V)
    (hck : ∀ r ∈ Set.Icc (0 : ℝ) T, Torus.IsCk 2 (ρ r))
    (hcc : ∀ j ≤ 2, Continuous fun p : Set.Icc (0 : ℝ) T × Euc d =>
      iteratedFDeriv ℝ j (Torus.lift (ρ p.1)) p.2) :
    Continuous fun p : Set.Icc (0 : ℝ) T × Torus d => mova_pdeRHS D (ρ p.1) p.2 := by
  have hV1 := mova_isCk_one_of_two hV
  have cdV : ∀ j, Continuous (Torus.partialDeriv j D.V) := fun j => mova_continuous_partialDeriv hV1 j
  have cLV := mova_continuous_laplacian hV
  have e : (fun p : Set.Icc (0 : ℝ) T × Torus d => mova_pdeRHS D (ρ p.1) p.2) = fun p =>
      D.invβ * Torus.laplacian (ρ p.1) p.2 +
        ∑ j, Torus.partialDeriv j (ρ p.1) p.2 * (Torus.partialDeriv j D.V p.2 + mova_F D (ρ p.1) j p.2) +
        ρ p.1 p.2 * (Torus.laplacian D.V p.2 + convFun (periodicRiesz d D.s) (Torus.laplacian (ρ p.1)) p.2) :=
    funext fun p => mova_pdeRHS_formula D (hck p.1.1 p.1.2) hV p.2
  rw [e]
  exact ((continuous_const.mul (movf_cont_lapρ hcc)).add (continuous_finsetSum _ fun j _ =>
    (movf_cont_dρ hcc j).mul (((cdV j).comp continuous_snd).add (movf_cont_F D hck hcc j)))).add
    ((movf_cont_rho hcc).mul ((cLV.comp continuous_snd).add (movf_cont_convLap D hcc)))

end Lite

end HRS

end
