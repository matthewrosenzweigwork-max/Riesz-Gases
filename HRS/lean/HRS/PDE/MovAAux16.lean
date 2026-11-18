import HRS.PDE.MovAAux15

/-!
# MOVA Aux16: expanded form of `pdeRHS` and its joint continuity in `(r, x)`.
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS

variable {d N : ℕ}

theorem mova_pdeRHS_formula (D : DynData d) {ρ : Torus d → ℝ} (hρ : Torus.IsCk 2 ρ)
    (hV : Torus.IsCk 2 D.V) (x : Torus d) :
    mova_pdeRHS D ρ x = D.invβ * Torus.laplacian ρ x +
      ∑ j, Torus.partialDeriv j ρ x * (Torus.partialDeriv j D.V x + mova_F D ρ j x) +
      ρ x * (Torus.laplacian D.V x + convFun (periodicRiesz d D.s) (Torus.laplacian ρ) x) := by
  have hd := b15_one_le_d D
  have hρ1 := mova_isCk_one_of_two hρ
  have hgi := mova_integrable_periodicRiesz hd D.hs0 D.hsd
  have hdρ : ∀ j, Torus.IsCk 1 (Torus.partialDeriv j ρ) := fun j => mova_isCk_partialDeriv hρ j
  have hdV : ∀ j, Torus.IsCk 1 (Torus.partialDeriv j D.V) := fun j => mova_isCk_partialDeriv hV j
  have hFj : ∀ j, Torus.IsCk 1 (mova_F D ρ j) := fun j => by
    rw [mova_F_eq D hρ1]; exact mova_isCk_one_convFun hgi (hdρ j)
  have hterm : ∀ j : Fin d, Torus.partialDeriv j (mova_fj D ρ j) x =
      D.invβ * Torus.partialDeriv j (Torus.partialDeriv j ρ) x +
        (Torus.partialDeriv j ρ x * (Torus.partialDeriv j D.V x + mova_F D ρ j x) +
          ρ x * (Torus.partialDeriv j (Torus.partialDeriv j D.V) x +
            convFun (periodicRiesz d D.s) (Torus.partialDeriv j (Torus.partialDeriv j ρ)) x)) := by
    intro j
    unfold mova_fj
    rw [mova_partialDeriv_add j (mova_isCk_const_mul _ (hdρ j))
      (mova_isCk_mul hρ1 (mova_isCk_add (hdV j) (hFj j))),
      mova_partialDeriv_const_mul j (hdρ j),
      mova_partialDeriv_mul j hρ1 (mova_isCk_add (hdV j) (hFj j)),
      mova_partialDeriv_add j (hdV j) (hFj j)]
    have : Torus.partialDeriv j (mova_F D ρ j) x =
        convFun (periodicRiesz d D.s) (Torus.partialDeriv j (Torus.partialDeriv j ρ)) x := by
      rw [mova_F_eq D hρ1]
      exact mova_partialDeriv_convFun hgi (hdρ j) j x
    rw [this]
  rw [mova_pdeRHS_eq]
  simp_rw [hterm]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    Finset.sum_add_distrib, ← mova_laplacian_eq_sum hρ, ← mova_laplacian_eq_sum hV]
  have : convFun (periodicRiesz d D.s) (Torus.laplacian ρ) x =
      ∑ j, convFun (periodicRiesz d D.s) (Torus.partialDeriv j (Torus.partialDeriv j ρ)) x := by
    have e : Torus.laplacian ρ = fun y => ∑ j, Torus.partialDeriv j (Torus.partialDeriv j ρ) y :=
      funext fun y => mova_laplacian_eq_sum hρ y
    rw [e]
    exact mova_convFun_sum_right Finset.univ hgi (fun j _ => mova_continuous_partialDeriv
      (mova_isCk_partialDeriv hρ j) j) x
  rw [this]
  ring

theorem mova_continuous_laplacian {f : Torus d → ℝ} (hf : Torus.IsCk 2 f) :
    Continuous (Torus.laplacian f) := by
  have e : Torus.laplacian f = fun y => ∑ j, Torus.partialDeriv j (Torus.partialDeriv j f) y :=
    funext fun y => mova_laplacian_eq_sum hf y
  rw [e]
  exact continuous_finsetSum _ fun j _ => mova_continuous_partialDeriv (mova_isCk_partialDeriv hf j) j

section JointContinuity

variable {T : ℝ} {ρ ρt : ℝ → Torus d → ℝ}

theorem mova_cont_rho (hρt : IsC12Test T ρ ρt) :
    Continuous fun p : Set.Icc (0 : ℝ) T × Torus d => ρ p.1 p.2 := hρt.continuous_f

theorem mova_cont_dρ (hρt : IsC12Test T ρ ρt) (j : Fin d) :
    Continuous fun p : Set.Icc (0 : ℝ) T × Torus d => Torus.partialDeriv j (ρ p.1) p.2 := by
  refine d1_continuous_prod_of_lift (h := fun p : Set.Icc (0 : ℝ) T × Torus d =>
    Torus.partialDeriv j (ρ p.1) p.2) ?_
  have h1 := (EuclideanSpace.proj j : Euc d →L[ℝ] ℝ).continuous.comp hρt.continuous_gradient_lift
  refine h1.congr fun p => ?_
  simp only [Function.comp_apply]
  rw [← mova_grad_apply, grad_mk]
  rfl

theorem mova_cont_lapρ (hρt : IsC12Test T ρ ρt) :
    Continuous fun p : Set.Icc (0 : ℝ) T × Torus d => Torus.laplacian (ρ p.1) p.2 := by
  refine d1_continuous_prod_of_lift (h := fun p : Set.Icc (0 : ℝ) T × Torus d =>
    Torus.laplacian (ρ p.1) p.2) ?_
  refine hρt.continuous_laplacian_lift.congr fun p => ?_
  simp only
  rw [laplacian_mk]

theorem mova_cont_F (D : DynData d) (hρt : IsC12Test T ρ ρt) (j : Fin d) :
    Continuous fun p : Set.Icc (0 : ℝ) T × Torus d => mova_F D (ρ p.1) j p.2 := by
  have hgi := mova_integrable_periodicRiesz (b15_one_le_d D) D.hs0 D.hsd
  have h := mova_continuous_convFun_param (P := Set.Icc (0 : ℝ) T)
    (f := fun r y => Torus.partialDeriv j (ρ r.1) y) hgi (mova_cont_dρ hρt j)
  refine h.congr fun p => ?_
  rw [mova_F_eq D (mova_isCk_one_of_two (hρt.c2 p.1.1 p.1.2)) j]

theorem mova_cont_convLap (D : DynData d) (hρt : IsC12Test T ρ ρt) :
    Continuous fun p : Set.Icc (0 : ℝ) T × Torus d =>
      convFun (periodicRiesz d D.s) (Torus.laplacian (ρ p.1)) p.2 := by
  have hgi := mova_integrable_periodicRiesz (b15_one_le_d D) D.hs0 D.hsd
  exact mova_continuous_convFun_param (P := Set.Icc (0 : ℝ) T)
    (f := fun r y => Torus.laplacian (ρ r.1) y) hgi (mova_cont_lapρ hρt)

theorem mova_cont_pde (D : DynData d) (hρt : IsC12Test T ρ ρt) (hV : Torus.IsCk 2 D.V) :
    Continuous fun p : Set.Icc (0 : ℝ) T × Torus d => mova_pdeRHS D (ρ p.1) p.2 := by
  have hV1 := mova_isCk_one_of_two hV
  have cdV : ∀ j, Continuous (Torus.partialDeriv j D.V) := fun j => mova_continuous_partialDeriv hV1 j
  have cLV := mova_continuous_laplacian hV
  have e : (fun p : Set.Icc (0 : ℝ) T × Torus d => mova_pdeRHS D (ρ p.1) p.2) = fun p =>
      D.invβ * Torus.laplacian (ρ p.1) p.2 +
        ∑ j, Torus.partialDeriv j (ρ p.1) p.2 * (Torus.partialDeriv j D.V p.2 + mova_F D (ρ p.1) j p.2) +
        ρ p.1 p.2 * (Torus.laplacian D.V p.2 + convFun (periodicRiesz d D.s) (Torus.laplacian (ρ p.1)) p.2) :=
    funext fun p => mova_pdeRHS_formula D (hρt.c2 p.1.1 p.1.2) hV p.2
  rw [e]
  exact ((continuous_const.mul (mova_cont_lapρ hρt)).add (continuous_finsetSum _ fun j _ =>
    (mova_cont_dρ hρt j).mul (((cdV j).comp continuous_snd).add (mova_cont_F D hρt j)))).add
    ((mova_cont_rho hρt).mul ((cLV.comp continuous_snd).add (mova_cont_convLap D hρt)))

end JointContinuity

end HRS
