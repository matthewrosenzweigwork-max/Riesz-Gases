import HRS.MS.SA16Y5Nf2
import HRS.MS.SA16Y4Nc3
import HRS.MS.SA16Y5Sm1

/-!
# S.A.16 (SA16Y5) Nl1 (fractional order; copy of Nf1 with `T : W^{m+2} → W^m`): the nonlocal pairing of an order-one operator with the derivative on the solution

`sa16y5_nl_ibp`: for a `C^1` coefficient `a = C.ρ τ'`, `N : W^{m+2,p} →L W^{m+1,p}` with zeroth component `eucNonlocal C.s C.M a φ` on `Jcc φ`,
`m ≥ 1`, `ψ ∈ C_c^∞` and `a κ_i ∈ L^{p'}`: for every `y ∈ W^{m+2,p}`
`ℓ_ψ(N y) = -∑_{ij} M_{ji} ∫ (ι² y)_{e_j} (a κ_i)`, `κ_i = ∂_i(g ⋆ ψ)`.  This is the weaker-norm form of the nonlocal term: it is bounded by
`‖ι² y‖` with a constant depending only on `‖a κ_i‖_{p'}` (copy of `sa16y4_nl_ibp`, whose proof it follows).
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer

section Nf1
variable {d : ℕ} {p : ℝ} [Fact (2 ≤ p)]

theorem sa16y5f_nl_ibp {m : ℕ} (hm : 1 ≤ m) (C : WholeCoeff d) (τ' : ℝ) (hs0 : 0 ≤ C.s) (hsd : C.s < d)
    (hμ : ContDiff ℝ 1 (C.ρ τ')) {ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hψ : IsCcInfty ψ)
    (hN : ∀ i : Fin d, MemLp (fun x => C.ρ τ' x * kernelConvDeriv d C.s i ψ x)
      (ENNReal.conjExponent (ENNReal.ofReal p)) volume)
    (T : WmpSpace d (m + 1 + 1) p →L[ℝ] WmpSpace d m p)
    (hT : ∀ φ : ccSub d, wrep d m p (T (sa16r_Jcc d (m + 1 + 1) p φ)) =ᵐ[volume]
      HRS.MH.AdjointRd.eucNonlocal C.s C.M (C.ρ τ') φ.1) (y : WmpSpace d (m + 1 + 1) p) :
    sa16r_ell d m p hψ (T y) = -∑ i : Fin d, ∑ j : Fin d, C.M j i *
      ∫ x, sa16y4_cmp d m p (sa16y4_tau1 d m hm j) (sa16sz_iota2 d m p y) x *
        (C.ρ τ' x * kernelConvDeriv d C.s i ψ x) := by
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
  have key : ∀ y : WmpSpace d (m + 1 + 1) p, sa16r_ell d m p hψ (T y) = -∑ i : Fin d, ∑ j : Fin d, C.M j i *
      ((sa16so_pairN d m p (sa16y4_tau1 d m hm j) (hN i)).comp (WmpSpace d m p).subtypeL (sa16sz_iota2 d m p y)) := by
    intro y
    refine (sa16r_Jcc_dense d (m + 1 + 1) p).induction_on y (isClosed_eq ?_ ?_) (fun φ => ?_)
    · exact (sa16r_ell d m p hψ).continuous.comp T.continuous
    · exact (continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ =>
        continuous_const.mul (((sa16so_pairN d m p (sa16y4_tau1 d m hm j) (hN i)).comp
          (WmpSpace d m p).subtypeL).continuous.comp (sa16sz_iota2 d m p).continuous)).neg
    · have hφ : IsCcInfty (φ : EuclideanSpace ℝ (Fin d) → ℝ) := φ.2
      -- left side
      have e1 : sa16r_ell d m p hψ (T (sa16r_Jcc d (m + 1 + 1) p φ)) = ∫ x, φ.1 x * nonlocalTestRd C τ' ψ x := by
        rw [sa16r_ell_apply, ← sa16sp_pairing_cc C τ' hs0 hsd hμ hφ hψ]
        exact integral_congr_ae (by filter_upwards [hT φ] with x hx; rw [hx])
      rw [e1]
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
          (sa16sz_iota2 d m p (sa16r_Jcc d (m + 1 + 1) p φ)) = ∫ x, fderiv ℝ φ.1 x (EuclideanSpace.single j 1) *
            (C.ρ τ' x * kernelConvDeriv d C.s i ψ x) := by
        rw [sa16sz_iota2_Jcc, ContinuousLinearMap.comp_apply, sa16so_pairN_apply, sa16r_Jcc_eq]
        refine integral_congr_ae ?_
        filter_upwards [sa16r_cc_elt_coe (p := p) hφ m] with x hx
        show (((sa16r_cc_elt (p := p) hφ m : WmpSpace d m p) : WLp d m p) :
          EuclideanSpace ℝ (Fin d) → (WIndex d m → ℝ)) x (sa16y4_tau1 d m hm j) * _ = _
        rw [hx]
        have hp1 : partialDeriv (fun _ : Fin 1 => j) φ.1 x = fderiv ℝ φ.1 x (EuclideanSpace.single j 1) := by
          simp [partialDeriv, iteratedFDeriv_one_apply]
        exact congrArg (· * _) hp1
      rw [e3, hib]; ring
  refine (key y).trans ?_
  simp only [ContinuousLinearMap.comp_apply, sa16so_pairN_apply]
  rfl

theorem sa16y5f_nl_rep {m : ℕ} (hm : 1 ≤ m) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (M : Matrix (Fin d) (Fin d) ℝ)
    {a : EuclideanSpace ℝ (Fin d) → ℝ} (ha1 : ContDiff ℝ 1 a) {ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hψ : IsCcInfty ψ)
    (hN : ∀ i : Fin d, MemLp (fun x => a x * kernelConvDeriv d s i ψ x)
      (ENNReal.conjExponent (ENNReal.ofReal p)) volume)
    (N : WmpSpace d (m + 1 + 1) p →L[ℝ] WmpSpace d m p)
    (hT : ∀ φ : ccSub d, wrep d m p (N (sa16r_Jcc d (m + 1 + 1) p φ)) =ᵐ[volume]
      HRS.MH.AdjointRd.eucNonlocal s M a φ.1) (y : WmpSpace d (m + 1 + 1) p) :
    sa16r_ell d m p hψ (N y) = sa16y5_Phi d m hm p s M a ψ (sa16sz_iota2 d m p y) := by
  have := sa16y5f_nl_ibp (p := p) hm (sa16y4_cf d s M a) 0 hs0 hsd ha1 hψ hN N hT y
  exact this

end Nf1

end HRS.Whole.AppendixA.Phase2SA16R
