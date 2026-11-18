import HRS.MS.SA16SNl1

/-!
# S.A.16 (SA16S) Nl2: the weak identity of the nonlocal term on `C_c^∞` (P6, part 2)

`sa16sp_pairing_cc`: for `φ, ψ ∈ C_c^∞`, `μ = C.ρ τ'` of class `C^1`, `0 ≤ s < d`:
`∫ (eucNonlocal s M μ φ) ψ = ∫ φ · nonlocalTestRd C τ' ψ`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff Convolution

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer

section Nl2
variable {d : ℕ}

theorem sa16sp_pairing_cc (C : WholeCoeff d) (τ' : ℝ) (hs0 : 0 ≤ C.s) (hsd : C.s < d)
    (hμ : ContDiff ℝ 1 (C.ρ τ')) {φ ψ : Euc d → ℝ} (hφ : IsCcInfty φ) (hψ : IsCcInfty ψ) :
    ∫ x, HRS.MH.AdjointRd.eucNonlocal C.s C.M (C.ρ τ') φ x * ψ x =
      ∫ x, φ x * nonlocalTestRd C τ' ψ x := by
  set g : Euc d → ℝ := rieszKernel d C.s with hg
  set μ : Euc d → ℝ := C.ρ τ' with hμdef
  have hκ : LocallyIntegrable g volume := rieszKernel_locallyIntegrable hs0 hsd
  have hκe : ∀ z, g (-z) = g z := fun z => by simp [hg, rieszKernel, norm_neg]
  set e : Fin d → Euc d := fun j => EuclideanSpace.single j 1 with he
  -- the functions `f_j = μ ∂_jφ` and `H_j = g ⋆ f_j`
  have hdφ : ∀ j, IsCcInfty (fun y => fderiv ℝ φ y (e j)) := fun j => sa16s_cc_fderiv hφ _
  have hdψ : ∀ i, IsCcInfty (fun y => fderiv ℝ ψ y (e i)) := fun i => sa16s_cc_fderiv hψ _
  have hf1 : ∀ j, ContDiff ℝ 1 (fun y => μ y * fderiv ℝ φ y (e j)) :=
    fun j => hμ.mul ((hdφ j).1.of_le (by simp))
  have hfs : ∀ j, HasCompactSupport (fun y => μ y * fderiv ℝ φ y (e j)) :=
    fun j => (hdφ j).2.mul_left
  have hfc : ∀ j, Continuous (fun y => μ y * fderiv ℝ φ y (e j)) := fun j => (hf1 j).continuous
  -- derivative of `H_j`
  have hHd : ∀ j x, DifferentiableAt ℝ (convFun g (fun y => μ y * fderiv ℝ φ y (e j))) x :=
    fun j x => (sa16sp_convFun_fderiv hκ (hf1 j) (hfs j) x).1
  have hHder : ∀ i j x, fderiv ℝ (convFun g (fun y => μ y * fderiv ℝ φ y (e j))) x (e i) =
      convFun g (fun y => fderiv ℝ (fun y => μ y * fderiv ℝ φ y (e j)) y (e i)) x :=
    fun i j x => (sa16sp_convFun_fderiv hκ (hf1 j) (hfs j) x).2 (e i)
  have hHcont : ∀ i j, Continuous (fun x => fderiv ℝ (convFun g (fun y => μ y * fderiv ℝ φ y (e j))) x (e i)) := by
    intro i j
    have : (fun x => fderiv ℝ (convFun g (fun y => μ y * fderiv ℝ φ y (e j))) x (e i)) =
        convFun g (fun y => fderiv ℝ (fun y => μ y * fderiv ℝ φ y (e j)) y (e i)) := funext (hHder i j)
    rw [this]
    exact sa16sp_convFun_cont hκ (((hf1 j).continuous_fderiv (by simp)).clm_apply continuous_const)
      ((hfs j).fderiv_apply ℝ (e i))
  -- `Ψ_i = g ⋆ ∂_iψ`
  set Ψ : Fin d → Euc d → ℝ := fun i => convFun g (fun y => fderiv ℝ ψ y (e i)) with hΨ
  have hΨ1 : ∀ i, ContDiff ℝ 1 (fun y => fderiv ℝ ψ y (e i)) := fun i => (hdψ i).1.of_le (by simp)
  have hΨd : ∀ i y, DifferentiableAt ℝ (Ψ i) y := fun i y => (sa16sp_convFun_fderiv hκ (hΨ1 i) (hdψ i).2 y).1
  have hΨder : ∀ i j y, fderiv ℝ (Ψ i) y (e j) =
      convFun g (fun y => fderiv ℝ (fun y => fderiv ℝ ψ y (e i)) y (e j)) y :=
    fun i j y => (sa16sp_convFun_fderiv hκ (hΨ1 i) (hdψ i).2 y).2 (e j)
  have hΨc : ∀ i, Continuous (Ψ i) := fun i => sa16sp_convFun_cont hκ (hΨ1 i).continuous (hdψ i).2
  have hΨdc : ∀ i j, Continuous (fun y => fderiv ℝ (Ψ i) y (e j)) := by
    intro i j
    have : (fun y => fderiv ℝ (Ψ i) y (e j)) =
        convFun g (fun y => fderiv ℝ (fun y => fderiv ℝ ψ y (e i)) y (e j)) := funext (hΨder i j)
    rw [this]
    exact sa16sp_convFun_cont hκ (((sa16s_cc_fderiv (hdψ i) _).1.continuous))
      ((sa16s_cc_fderiv (hdψ i) _).2)
  -- `Q_i = μ Ψ_i`
  set Q : Fin d → Euc d → ℝ := fun i y => μ y * Ψ i y with hQ
  have hμd : Differentiable ℝ μ := hμ.differentiable (by simp)
  have hQd : ∀ i, Differentiable ℝ (Q i) := fun i y => (hμd y).mul (hΨd i y)
  have hQder : ∀ i j y, fderiv ℝ (Q i) y (e j) =
      fderiv ℝ μ y (e j) * Ψ i y + μ y * fderiv ℝ (Ψ i) y (e j) := by
    intro i j y
    show fderiv ℝ (fun y => μ y * Ψ i y) y (e j) = _
    have hh : HasFDerivAt (fun y => μ y * Ψ i y) (μ y • fderiv ℝ (Ψ i) y + Ψ i y • fderiv ℝ μ y) y :=
      (hμd y).hasFDerivAt.mul (hΨd i y).hasFDerivAt
    rw [hh.fderiv]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    ring
  have hQdc : ∀ i j, Continuous (fun y => fderiv ℝ (Q i) y (e j)) := by
    intro i j
    have : (fun y => fderiv ℝ (Q i) y (e j)) =
        fun y => fderiv ℝ μ y (e j) * Ψ i y + μ y * fderiv ℝ (Ψ i) y (e j) := funext (hQder i j)
    rw [this]
    exact (((hμ.continuous_fderiv (by simp)).clm_apply continuous_const).mul (hΨc i)).add
      (hμ.continuous.mul (hΨdc i j))
  -- the key identity for one pair `(i, j)`
  have key : ∀ i j, ∫ x, fderiv ℝ (convFun g (fun y => μ y * fderiv ℝ φ y (e j))) x (e i) * ψ x =
      ∫ x, φ x * fderiv ℝ (Q i) x (e j) := by
    intro i j
    have h1 := sa16sp_ibp_C1 (H := convFun g (fun y => μ y * fderiv ℝ φ y (e j)))
      (fun x => hHd j x) (e i) (hHcont i j) hψ
    have h2 := sa16sp_swap (κ := g) (f := fun y => μ y * fderiv ℝ φ y (e j))
      (w := fun y => fderiv ℝ ψ y (e i)) hκ hκe (hfc j) (hfs j) (hdψ i).1.continuous (hdψ i).2
    have h3 := sa16sp_ibp_C1 (H := Q i) (hQd i) (e j) (hQdc i j) hφ
    have e1 : ∫ x, fderiv ℝ (convFun g (fun y => μ y * fderiv ℝ φ y (e j))) x (e i) * ψ x =
        ∫ x, ψ x * fderiv ℝ (convFun g (fun y => μ y * fderiv ℝ φ y (e j))) x (e i) := by
      refine integral_congr_ae (Eventually.of_forall fun x => ?_); ring
    have e2 : ∫ y, (μ y * fderiv ℝ φ y (e j)) * Ψ i y = ∫ x, fderiv ℝ φ x (e j) * Q i x := by
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp only [hQ]; ring
    rw [e1, h1, h2]
    simp only [hΨ] at e2 ⊢
    rw [e2]
    linarith
  -- assemble
  have hint1 : ∀ i j, Integrable (fun x => fderiv ℝ (convFun g (fun y => μ y * fderiv ℝ φ y (e j))) x (e i) * ψ x) :=
    fun i j => ((hHcont i j).mul hψ.1.continuous).integrable_of_hasCompactSupport hψ.2.mul_left
  have hint2 : ∀ i j, Integrable (fun x => φ x * fderiv ℝ (Q i) x (e j)) :=
    fun i j => (hφ.1.continuous.mul (hQdc i j)).integrable_of_hasCompactSupport hφ.2.mul_right
  have hL : ∀ x, HRS.MH.AdjointRd.eucNonlocal C.s C.M μ φ x * ψ x = ∑ i : Fin d, ∑ j : Fin d, C.M j i *
      (fderiv ℝ (convFun g (fun y => μ y * fderiv ℝ φ y (e j))) x (e i) * ψ x) := by
    intro x
    unfold HRS.MH.AdjointRd.eucNonlocal
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_assoc]
    rfl
  have hNl : ∀ x, φ x * nonlocalTestRd C τ' ψ x = ∑ i : Fin d, ∑ j : Fin d, C.M j i *
      (φ x * fderiv ℝ (Q i) x (e j)) := by
    intro x
    unfold nonlocalTestRd
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hpd : partialDeriv (fun _ : Fin 1 => j) (fun y => C.ρ τ' y * gradient (convFun (rieszKernel d C.s) ψ) y i) x =
        fderiv ℝ (Q i) x (e j) := by
      unfold partialDeriv
      rw [iteratedFDeriv_one_apply]
      have hfun : (fun y => C.ρ τ' y * gradient (convFun (rieszKernel d C.s) ψ) y i) = Q i := by
        funext y
        simp only [hQ, hΨ]
        rw [sa16sp_gradient_apply, (sa16sp_convFun_fderiv hκ (hψ.1.of_le (by simp)) hψ.2 y).2 (e i)]
      rw [hfun]
    rw [hpd]
    ring
  simp_rw [hL, hNl]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ fun j _ => (hint1 i j).const_mul _),
    integral_finsetSum _ (fun i _ => integrable_finsetSum _ fun j _ => (hint2 i j).const_mul _)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ (fun j _ => (hint1 i j).const_mul _),
    integral_finsetSum _ (fun j _ => (hint2 i j).const_mul _)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_const_mul, integral_const_mul, key i j]

end Nl2

end HRS.Whole.AppendixA.Phase2SA16R
