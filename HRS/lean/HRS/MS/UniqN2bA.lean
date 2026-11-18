import HRS.MS.UniqT3
import HRS.MS.UniqM1
import HRS.MS.UniqNDefs

/-!
# N2b of `UniqPlan.md`, part (a): the antisymmetric cancellation in `nMain`

For `ψ ∈ C²_c`, `ρ' ∈ C¹` with decay, `f` with uniform local `L²` mass and a matrix `M` with
`M j i + M i j = 0`:
`nMain D ρ' f ψ = ∑_{ij} M_{ji} ∫ f · (∂_jρ' · H_i)`, `H_i = g * ∂_iψ` (`kernelConvDeriv`).
Indeed `∂_j(ρ' H_i) = ∂_jρ' H_i + ρ' G_{ji}` with `G_{ji} = g * ∂_j∂_iψ`, and
`∑_{ij} M_{ji} G_{ji} = g * (∑_{ij} M_{ji} ∂_j∂_iψ) = 0` by the symmetry of the Hessian of `ψ`.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal ContDiff

namespace HRS.MS.UniqN2b

open HRS HRS.Whole HRS.Whole.AppendixALemmas HRS.MS.UniqT3 HRS.MS.UniqM1 HRS.MS.UniqNDefs

variable {d : ℕ}

/-- The symmetry of the Hessian against an antisymmetric matrix. -/
theorem n2b_hess_sum_zero {ψ : Euc d → ℝ} (hψ : ContDiff ℝ 2 ψ) (M : Matrix (Fin d) (Fin d) ℝ)
    (hM : ∀ i j, M j i + M i j = 0) (x : Euc d) :
    ∑ i, ∑ j, M j i * D1 j (D1 i ψ) x = 0 := by
  have hd : DifferentiableAt ℝ (fderiv ℝ ψ) x :=
    ((hψ.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)) x
  have h1 : ∀ k l, D1 l (D1 k ψ) x =
      fderiv ℝ (fderiv ℝ ψ) x (EuclideanSpace.single l 1) (EuclideanSpace.single k 1) := by
    intro k l
    unfold D1
    rw [fderiv_clm_apply hd (differentiableAt_const _)]
    simp
  have hsymm := (hψ.contDiffAt (x := x)).isSymmSndFDerivAt (by simp)
  have hsym : ∀ i j, D1 j (D1 i ψ) x = D1 i (D1 j ψ) x := fun i j => by
    rw [h1, h1]; exact hsymm _ _
  set X : ℝ := ∑ i, ∑ j, M j i * D1 j (D1 i ψ) x with hX
  have h2 : X = -X := by
    calc X = ∑ j, ∑ i, M j i * D1 j (D1 i ψ) x := Finset.sum_comm
      _ = ∑ i, ∑ j, M i j * D1 i (D1 j ψ) x := rfl
      _ = ∑ i, ∑ j, -(M j i * D1 j (D1 i ψ) x) := by
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
          rw [← hsym i j]
          have h' : M i j = -M j i := by linarith [hM i j]
          rw [h']; ring
      _ = -X := by simp [hX, Finset.sum_neg_distrib]
  linarith

/-- Product rule for `∂_j (ρ' · (g * ∂_iψ))`. -/
theorem n2b_fderiv_prod {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {ρ' : Euc d → ℝ}
    (hρ : ContDiff ℝ 1 ρ') {ψ : Euc d → ℝ} (hψ : ContDiff ℝ 2 ψ) (hψc : HasCompactSupport ψ)
    (i j : Fin d) (y : Euc d) :
    fderiv ℝ (fun y => ρ' y * kernelConvDeriv d s i ψ y) y (EuclideanSpace.single j (1 : ℝ)) =
      D1 j ρ' y * kernelConvDeriv d s i ψ y +
        ρ' y * HRS.Whole.convFun (rieszKernel d s) (D1 j (D1 i ψ)) y := by
  have hl := rieszKernel_locallyIntegrable (d := d) hs0 hsd
  have hK : kernelConvDeriv d s i ψ = HRS.Whole.convFun (rieszKernel d s) (D1 i ψ) := rfl
  rw [hK, fderiv_fun_mul (hρ.differentiable (by norm_num) y)
    (convFun_diff hl (D1_contDiff hψ i) (D1_supp hψc i) y)]
  have := convFun_D1 hl (D1_contDiff hψ i) (D1_supp hψc i) j y
  simp only [D1, add_apply, smul_apply,
    smul_eq_mul] at this ⊢
  rw [this]; ring

/-- Integrability of `y ↦ g(y - x) h(x)` for `h` continuous with compact support. -/
theorem n2b_conv_integrable {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {h : Euc d → ℝ}
    (hh : Continuous h) (hhc : HasCompactSupport h) (y : Euc d) :
    Integrable (fun x => rieszKernel d s (y - x) * h x) volume := by
  have hl := rieszKernel_locallyIntegrable (d := d) hs0 hsd
  have := hhc.convolutionExists_left (ContinuousLinearMap.mul ℝ ℝ) hh hl y
  refine this.congr (Eventually.of_forall fun x => ?_)
  simp [mul_comm]

theorem n2b_D1D1_cont {ψ : Euc d → ℝ} (hψ : ContDiff ℝ 2 ψ) (i j : Fin d) :
    Continuous (D1 j (D1 i ψ)) :=
  ((D1_contDiff hψ i).continuous_fderiv one_ne_zero).clm_apply continuous_const

/-- `∑_{ij} M_{ji} G_{ji} = 0`. -/
theorem n2b_G_sum_zero {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {ψ : Euc d → ℝ} (hψ : ContDiff ℝ 2 ψ)
    (hψc : HasCompactSupport ψ) (M : Matrix (Fin d) (Fin d) ℝ) (hM : ∀ i j, M j i + M i j = 0)
    (y : Euc d) :
    ∑ i, ∑ j, M j i * HRS.Whole.convFun (rieszKernel d s) (D1 j (D1 i ψ)) y = 0 := by
  have hint : ∀ i j, Integrable (fun x => rieszKernel d s (y - x) * D1 j (D1 i ψ) x) volume :=
    fun i j => n2b_conv_integrable hs0 hsd (n2b_D1D1_cont hψ i j)
      (D1_supp (D1_supp hψc i) j) y
  have hint' : ∀ i j, Integrable (fun x => M j i * (rieszKernel d s (y - x) * D1 j (D1 i ψ) x)) volume :=
    fun i j => (hint i j).const_mul (M j i)
  have h1 : ∑ i, ∑ j, M j i * HRS.Whole.convFun (rieszKernel d s) (D1 j (D1 i ψ)) y =
      ∫ x, rieszKernel d s (y - x) * ∑ i, ∑ j, M j i * D1 j (D1 i ψ) x := by
    have hpt : ∀ x, rieszKernel d s (y - x) * ∑ i, ∑ j, M j i * D1 j (D1 i ψ) x =
        ∑ i, ∑ j, M j i * (rieszKernel d s (y - x) * D1 j (D1 i ψ) x) := by
      intro x
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    simp_rw [hpt]
    rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hint' i j]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum _ fun j _ => hint' i j]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_const_mul]
    rfl
  rw [h1]
  simp [n2b_hess_sum_zero hψ M hM]

theorem n2b_wt_mul (y : Euc d) : (1 + ‖y‖) ^ (-((d : ℝ) + 3)) * (1 + ‖y‖) = wt d y := by
  unfold wt
  rw [← Real.rpow_add_one (by positivity)]
  congr 1; ring

/-- `|a h| ≤ Cρ C wt` from decay of `a` and linear growth of `h`. -/
theorem n2b_wt_dom {Cρ C : ℝ} {a h : Euc d → ℝ}
    (ha : ∀ y, |a y| ≤ Cρ * (1 + ‖y‖) ^ (-((d : ℝ) + 3)))
    (hh : ∀ y, |h y| ≤ C * (1 + ‖y‖)) (y : Euc d) : |a y * h y| ≤ (Cρ * C) * wt d y := by
  rw [abs_mul, ← n2b_wt_mul]
  have h1 : 0 ≤ Cρ * (1 + ‖y‖) ^ (-((d : ℝ) + 3)) := (abs_nonneg _).trans (ha y)
  calc |a y| * |h y| ≤ (Cρ * (1 + ‖y‖) ^ (-((d : ℝ) + 3))) * (C * (1 + ‖y‖)) :=
        mul_le_mul (ha y) (hh y) (abs_nonneg _) h1
    _ = _ := by ring

theorem n2b_D1_le (j : Fin d) (u : Euc d → ℝ) (y : Euc d) : |D1 j u y| ≤ ‖fderiv ℝ u y‖ := by
  unfold D1
  rw [← Real.norm_eq_abs]
  refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
  simp

/-- **Antisymmetric cancellation.**  For `M j i + M i j = 0`, `ψ ∈ C²_c`, `ρ' ∈ C¹` with decay and
`f` with uniform local `L²` mass:
`nMain D ρ' f ψ = ∑_{ij} M_{ji} ∫ f · (∂_jρ' · (g * ∂_iψ))`. -/
theorem n2b_nMain_eq {D : WholeDyn d} (hs0 : 0 ≤ D.s) (hsd : D.s < d)
    (hM : ∀ i j, D.M j i + D.M i j = 0)
    {ρ' : Euc d → ℝ} (hρ : ContDiff ℝ 1 ρ') {Cρ : ℝ}
    (hρ0 : ∀ y, |ρ' y| ≤ Cρ * (1 + ‖y‖) ^ (-((d : ℝ) + 3)))
    (hρ1 : ∀ y, ‖fderiv ℝ ρ' y‖ ≤ Cρ * (1 + ‖y‖) ^ (-((d : ℝ) + 3)))
    {A : ℝ} {f : Euc d → ℝ} (hf : LocMass A f)
    {ψ : Euc d → ℝ} (hψ : ContDiff ℝ 2 ψ) (hψc : HasCompactSupport ψ) :
    nMain D ρ' f ψ =
      ∑ i, ∑ j, D.M j i * ∫ y, f y * (D1 j ρ' y * kernelConvDeriv d D.s i ψ y) := by
  have hρc : Continuous ρ' := hρ.continuous
  have hDρ : ∀ j, Continuous (D1 j ρ') := fun j =>
    (hρ.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hHc : ∀ i, Continuous (kernelConvDeriv d D.s i ψ) := fun i =>
    K_cont hs0 hsd (D1_contDiff hψ i).continuous (D1_supp hψc i)
  have hGc : ∀ i j, Continuous (HRS.Whole.convFun (rieszKernel d D.s) (D1 j (D1 i ψ))) :=
    fun i j => K_cont hs0 hsd (n2b_D1D1_cont hψ i j) (D1_supp (D1_supp hψc i) j)
  -- integrability of the two pieces
  have I1 : ∀ i j, Integrable (fun y => f y * (D1 j ρ' y * kernelConvDeriv d D.s i ψ y)) volume := by
    intro i j
    obtain ⟨C1, hC1⟩ := conv_bound hs0 hsd (D1_contDiff hψ i).continuous (D1_supp hψc i)
    exact key_int hf.1 (A ^ 2) hf.2 ((hDρ j).mul (hHc i)).aestronglyMeasurable (Cρ * C1)
      (n2b_wt_dom (fun y => (n2b_D1_le j ρ' y).trans (hρ1 y)) (fun y => hC1 y))
  have I2 : ∀ i j, Integrable (fun y => f y * (ρ' y *
      HRS.Whole.convFun (rieszKernel d D.s) (D1 j (D1 i ψ)) y)) volume := by
    intro i j
    obtain ⟨C1, hC1⟩ := conv_bound hs0 hsd (n2b_D1D1_cont hψ i j) (D1_supp (D1_supp hψc i) j)
    exact key_int hf.1 (A ^ 2) hf.2 (hρc.mul (hGc i j)).aestronglyMeasurable (Cρ * C1)
      (n2b_wt_dom hρ0 (fun y => hC1 y))
  unfold nMain
  have step : ∀ i j, (∫ x, f x * fderiv ℝ (fun y => ρ' y * kernelConvDeriv d D.s i ψ y) x
        (EuclideanSpace.single j (1 : ℝ))) =
      (∫ y, f y * (D1 j ρ' y * kernelConvDeriv d D.s i ψ y)) +
        ∫ y, f y * (ρ' y * HRS.Whole.convFun (rieszKernel d D.s) (D1 j (D1 i ψ)) y) := by
    intro i j
    rw [← integral_add (I1 i j) (I2 i j)]
    congr 1; funext y
    rw [n2b_fderiv_prod hs0 hsd hρ hψ hψc i j y]
    ring
  have hzero : ∑ i, ∑ j, D.M j i * ∫ y, f y * (ρ' y *
      HRS.Whole.convFun (rieszKernel d D.s) (D1 j (D1 i ψ)) y) = 0 := by
    have hI : ∀ i j, Integrable (fun y => D.M j i * (f y * (ρ' y *
        HRS.Whole.convFun (rieszKernel d D.s) (D1 j (D1 i ψ)) y))) volume :=
      fun i j => (I2 i j).const_mul _
    have : ∑ i, ∑ j, D.M j i * ∫ y, f y * (ρ' y *
        HRS.Whole.convFun (rieszKernel d D.s) (D1 j (D1 i ψ)) y) =
        ∫ y, ∑ i, ∑ j, D.M j i * (f y * (ρ' y *
          HRS.Whole.convFun (rieszKernel d D.s) (D1 j (D1 i ψ)) y)) := by
      rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hI i j]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [integral_finsetSum _ fun j _ => hI i j]
      exact Finset.sum_congr rfl fun j _ => (integral_const_mul _ _).symm
    rw [this]
    have h0 : ∀ y, ∑ i, ∑ j, D.M j i * (f y * (ρ' y *
        HRS.Whole.convFun (rieszKernel d D.s) (D1 j (D1 i ψ)) y)) = 0 := by
      intro y
      have := n2b_G_sum_zero hs0 hsd hψ hψc D.M hM y
      calc _ = f y * ρ' y * ∑ i, ∑ j, D.M j i *
            HRS.Whole.convFun (rieszKernel d D.s) (D1 j (D1 i ψ)) y := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun j _ => by ring
        _ = 0 := by rw [this, mul_zero]
    simp [h0]
  have hsplit : ∀ i j, D.M j i * (∫ x, f x * fderiv ℝ (fun y => ρ' y * kernelConvDeriv d D.s i ψ y) x
        (EuclideanSpace.single j (1 : ℝ))) =
      D.M j i * (∫ y, f y * (D1 j ρ' y * kernelConvDeriv d D.s i ψ y)) +
        D.M j i * ∫ y, f y * (ρ' y * HRS.Whole.convFun (rieszKernel d D.s) (D1 j (D1 i ψ)) y) := by
    intro i j; rw [step, mul_add]
  simp_rw [hsplit, Finset.sum_add_distrib]
  rw [hzero, add_zero]

end HRS.MS.UniqN2b
