import HRS.PDE.TorusFPExistAux14

/-!
# D1 existence, helper 15: joint continuity for `C^{1,2}` tests
-/

noncomputable section

open MeasureTheory Filter Topology

namespace HRS

variable {n : ℕ}

theorem IsC12Test.continuous_lift_f {τ : ℝ} {f ft : ℝ → Torus n → ℝ} (hf : IsC12Test τ f ft) :
    Continuous fun p : Set.Icc (0 : ℝ) τ × Euc n => f p.1 (Torus.mk p.2) := by
  have h0 := (continuousMultilinearCurryFin0 ℝ (Euc n) ℝ).continuous.comp (hf.cont_c2 0 (by norm_num))
  refine h0.congr fun p => ?_
  simp [iteratedFDeriv_zero_eq_comp, Torus.lift]

theorem IsC12Test.continuous_f {τ : ℝ} {f ft : ℝ → Torus n → ℝ} (hf : IsC12Test τ f ft) :
    Continuous fun p : Set.Icc (0 : ℝ) τ × Torus n => f p.1 p.2 :=
  d1_continuous_prod_of_lift (h := fun p : Set.Icc (0 : ℝ) τ × Torus n => f p.1 p.2) hf.continuous_lift_f

theorem IsC12Test.continuous_gradient_lift {τ : ℝ} {f ft : ℝ → Torus n → ℝ} (hf : IsC12Test τ f ft) :
    Continuous fun p : Set.Icc (0 : ℝ) τ × Euc n => gradient (Torus.lift (f p.1)) p.2 := by
  have h1 := (continuousMultilinearCurryFin1 ℝ (Euc n) ℝ).continuous.comp (hf.cont_c2 1 (by norm_num))
  have h2 := (InnerProductSpace.toDual ℝ (Euc n)).symm.continuous.comp h1
  refine h2.congr fun p => ?_
  simp only [Function.comp_apply]
  unfold gradient
  rw [fderiv_eq_curry]

theorem IsC12Test.continuous_laplacian_lift {τ : ℝ} {f ft : ℝ → Torus n → ℝ} (hf : IsC12Test τ f ft) :
    Continuous fun p : Set.Icc (0 : ℝ) τ × Euc n => Laplacian.laplacian (Torus.lift (f p.1)) p.2 := by
  have h1 := (continuous_curry2 n).comp (hf.cont_c2 2 le_rfl)
  have e : (fun p : Set.Icc (0 : ℝ) τ × Euc n => Laplacian.laplacian (Torus.lift (f p.1)) p.2) =
      fun p => ∑ i : Fin n, (curry2 n (iteratedFDeriv ℝ 2 (Torus.lift (f p.1)) p.2))
        (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ i) := by
    funext p
    rw [d1_laplacian_eq_sum]
    simp only [← fderiv_fderiv_eq_curry2]
  rw [e]
  exact continuous_finset_sum _ fun i _ => (h1.clm_apply continuous_const).clm_apply continuous_const

theorem IsC12Test.continuous_gen {τ : ℝ} {f ft : ℝ → Torus n → ℝ} (hf : IsC12Test τ f ft)
    {κ : ℝ} {b : Torus n → Euc n} (hb : Continuous b) :
    Continuous fun p : Set.Icc (0 : ℝ) τ × Torus n => d1_gen κ b (f p.1) p.2 := by
  apply d1_continuous_prod_of_lift (h := fun p : Set.Icc (0 : ℝ) τ × Torus n => d1_gen κ b (f p.1) p.2)
  have e : (fun p : Set.Icc (0 : ℝ) τ × Euc n => d1_gen κ b (f p.1) (Torus.mk p.2)) = fun p =>
      κ * Laplacian.laplacian (Torus.lift (f p.1)) p.2 +
        inner ℝ (b (Torus.mk p.2)) (gradient (Torus.lift (f p.1)) p.2) := by
    funext p
    simp only [d1_gen, laplacian_mk, grad_mk]
  rw [e]
  exact (continuous_const.mul hf.continuous_laplacian_lift).add
    ((hb.comp (Torus.continuous_mk.comp continuous_snd)).inner hf.continuous_gradient_lift)

end HRS
