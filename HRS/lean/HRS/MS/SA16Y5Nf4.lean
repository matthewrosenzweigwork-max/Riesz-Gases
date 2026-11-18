import HRS.MS.SA16Y5Nf3

/-!
# S.A.16 (SA16Y5) Nf4: `Φ_a(w) = ∫ wrep w · nonlocalTestRd C τ' ψ` on all of `W^{m,p}` (`m ≥ 1`)

The derivative-on-the-solution functional is the adjoint pairing against the nonlocal test function (identification of the limit nonlocal term; no operator
on `W^{m,p}` is used).  Density of `Jcc` plus the integration by parts of `sa16y4_nl_ibp` on `C_c^∞`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer

section Nf4
variable {d : ℕ} {p : ℝ} [Fact (2 ≤ p)]

theorem sa16y5_Phi_eq {m : ℕ} (hm : 1 ≤ m) (C : WholeCoeff d) (τ' : ℝ) (hs0 : 0 ≤ C.s) (hsd : C.s < d)
    (hμ : ContDiff ℝ 1 (C.ρ τ')) {ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hψ : IsCcInfty ψ)
    (hN : ∀ i : Fin d, MemLp (fun x => C.ρ τ' x * kernelConvDeriv d C.s i ψ x)
      (ENNReal.conjExponent (ENNReal.ofReal p)) volume)
    (hNt : MemLp (nonlocalTestRd C τ' ψ) (ENNReal.conjExponent (ENNReal.ofReal p)) volume) (w : WmpSpace d m p) :
    sa16y5_Phi d m hm p C.s C.M (C.ρ τ') ψ w = ∫ x, wrep d m p w x * nonlocalTestRd C τ' ψ x := by
  have hl := rieszKernel_locallyIntegrable (d := d) hs0 hsd
  have hψ2 : ContDiff ℝ 2 ψ := hψ.1.of_le (by simp)
  have hκc : ∀ i, Continuous (kernelConvDeriv d C.s i ψ) := fun i =>
    HRS.MS.UniqT3.K_cont hs0 hsd (HRS.MS.UniqT3.D1_contDiff hψ2 i).continuous (HRS.MS.UniqT3.D1_supp hψ.2 i)
  have hκd : ∀ i, Differentiable ℝ (kernelConvDeriv d C.s i ψ) := fun i =>
    HRS.MS.UniqT3.convFun_diff hl (HRS.MS.UniqT3.D1_contDiff hψ2 i) (HRS.MS.UniqT3.D1_supp hψ.2 i)
  have hNd : ∀ i, Differentiable ℝ (fun x => C.ρ τ' x * kernelConvDeriv d C.s i ψ x) := fun i =>
    (hμ.differentiable (by simp)).mul (hκd i)
  have hdN : ∀ i j, Continuous (fun x => fderiv ℝ (fun y => C.ρ τ' y * kernelConvDeriv d C.s i ψ y) x
      (EuclideanSpace.single j (1 : ℝ))) := by
    intro i j
    have : (fun x => fderiv ℝ (fun y => C.ρ τ' y * kernelConvDeriv d C.s i ψ y) x (EuclideanSpace.single j (1 : ℝ))) =
        fun x => HRS.MS.UniqT3.D1 j (C.ρ τ') x * kernelConvDeriv d C.s i ψ x +
          C.ρ τ' x * HRS.Whole.convFun (rieszKernel d C.s) (HRS.MS.UniqT3.D1 j (HRS.MS.UniqT3.D1 i ψ)) x :=
      funext fun x => HRS.MS.UniqN2b.n2b_fderiv_prod hs0 hsd hμ hψ2 hψ.2 i j x
    rw [this]
    exact (((hμ.continuous_fderiv one_ne_zero).clm_apply continuous_const).mul (hκc i)).add
      (hμ.continuous.mul (HRS.MS.UniqT3.K_cont hs0 hsd (HRS.MS.UniqN2b.n2b_D1D1_cont hψ2 i j)
        (HRS.MS.UniqT3.D1_supp (HRS.MS.UniqT3.D1_supp hψ.2 i) j)))
  have hPhi : ∀ y : WmpSpace d m p, sa16y5_Phi d m hm p C.s C.M (C.ρ τ') ψ y = -∑ i : Fin d, ∑ j : Fin d, C.M j i *
      ((sa16so_pairN d m p (sa16y4_tau1 d m hm j) (hN i)).comp (WmpSpace d m p).subtypeL y) := by
    intro y
    simp only [sa16y5_Phi, ContinuousLinearMap.comp_apply, sa16so_pairN_apply]
    rfl
  refine (sa16r_Jcc_dense d m p).induction_on w (isClosed_eq ?_ ?_) (fun φ => ?_)
  · refine Continuous.congr ?_ (fun y => (hPhi y).symm)
    exact (continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
      continuous_const.mul ((sa16so_pairN d m p (sa16y4_tau1 d m hm j) (hN i)).comp
        (WmpSpace d m p).subtypeL).continuous).neg
  · simp_rw [← sa16so_ellN_apply m hNt]
    exact (sa16so_ellN d m p hNt).continuous
  · rw [hPhi]
    have e2w : ∫ x, wrep d m p (sa16r_Jcc d m p φ) x * nonlocalTestRd C τ' ψ x =
        ∫ x, φ.1 x * nonlocalTestRd C τ' ψ x := by
      refine integral_congr_ae ?_
      rw [sa16r_Jcc_eq]
      filter_upwards [sa16r_cc_elt_wrep (p := p) φ.2 m] with x hx
      rw [hx]
    rw [e2w]
    have hφ : IsCcInfty (φ : EuclideanSpace ℝ (Fin d) → ℝ) := φ.2
    have e2 : ∀ x, φ.1 x * nonlocalTestRd C τ' ψ x = ∑ i : Fin d, ∑ j : Fin d, C.M j i *
        (φ.1 x * fderiv ℝ (fun y => C.ρ τ' y * kernelConvDeriv d C.s i ψ y) x (EuclideanSpace.single j (1 : ℝ))) := by
      intro x
      rw [sa16y4_nlTest_eq C τ' hs0 hsd hψ x, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    have hint : ∀ i j : Fin d, Integrable (fun x => φ.1 x *
        fderiv ℝ (fun y => C.ρ τ' y * kernelConvDeriv d C.s i ψ y) x (EuclideanSpace.single j (1 : ℝ))) :=
      fun i j => (hφ.1.continuous.mul (hdN i j)).integrable_of_hasCompactSupport hφ.2.mul_right
    simp_rw [e2]
    rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => (hint i j).const_mul _, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum _ fun j _ => (hint i j).const_mul _, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_const_mul]
    have hib := sa16y4_ibp_cc (hNd i) (hNd i).continuous (EuclideanSpace.single j (1 : ℝ)) (hdN i j) hφ
    have e3 : (sa16so_pairN d m p (sa16y4_tau1 d m hm j) (hN i)).comp (WmpSpace d m p).subtypeL
        (sa16r_Jcc d m p φ) = ∫ x, fderiv ℝ φ.1 x (EuclideanSpace.single j 1) *
          (C.ρ τ' x * kernelConvDeriv d C.s i ψ x) := by
      rw [ContinuousLinearMap.comp_apply, sa16so_pairN_apply, sa16r_Jcc_eq]
      refine integral_congr_ae ?_
      filter_upwards [sa16r_cc_elt_coe (p := p) hφ m] with x hx
      show (((sa16r_cc_elt (p := p) hφ m : WmpSpace d m p) : WLp d m p) :
        EuclideanSpace ℝ (Fin d) → (WIndex d m → ℝ)) x (sa16y4_tau1 d m hm j) * _ = _
      rw [hx]
      have hp1 : partialDeriv (fun _ : Fin 1 => j) φ.1 x = fderiv ℝ φ.1 x (EuclideanSpace.single j 1) := by
        simp [partialDeriv, iteratedFDeriv_one_apply]
      exact congrArg (· * _) hp1
    rw [e3, hib]; ring
end Nf4

end HRS.Whole.AppendixA.Phase2SA16R
