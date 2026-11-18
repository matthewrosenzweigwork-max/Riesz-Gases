import HRS.MS.SA16Y3Dy2
import HRS.MS.SA16SNl3

/-!
# S.A.16 (SA16Y4) Wk1: integration by parts for the first jet component of `W^{m,p}` against `C^1` test functions in `L^{p'}`

`sa16y4_comp_ibp` (`m ≥ 1`): `∫ G_{e_k} N = -∫ (wrep G) ∂_k N` for `N ∈ C^1`, `N, ∂_k N ∈ L^{p'}`.
(Dy2 `sa16y3_comp_ell` is the `C_c^∞` case with an unspecified `M`; here `M = -∂_k N` explicitly and `N` is only `C^1`.)
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer

section Wk1
variable {d : ℕ} {p : ℝ} [Fact (2 ≤ p)]

/-- the index of the first derivative `∂_k` -/
def sa16y4_tau1 (d m : ℕ) (hm : 1 ≤ m) (k : Fin d) : WIndex d m := ⟨⟨1, by omega⟩, fun _ => k⟩

theorem sa16y4_comp_ibp {m : ℕ} (hm : 1 ≤ m) (k : Fin d) {N : EuclideanSpace ℝ (Fin d) → ℝ}
    (hN1 : ContDiff ℝ 1 N) (hN : MemLp N (ENNReal.conjExponent (ENNReal.ofReal p)) volume)
    (hNd : MemLp (fun x => fderiv ℝ N x (EuclideanSpace.single k 1)) (ENNReal.conjExponent (ENNReal.ofReal p)) volume)
    (G : WmpSpace d m p) :
    ∫ x, ((((G : WmpSpace d m p) : WLp d m p) : EuclideanSpace ℝ (Fin d) → (WIndex d m → ℝ)) x
        (sa16y4_tau1 d m hm k)) * N x =
      -∫ x, wrep d m p G x * fderiv ℝ N x (EuclideanSpace.single k 1) := by
  have hMm : MemLp (fun x => -fderiv ℝ N x (EuclideanSpace.single k 1))
      (ENNReal.conjExponent (ENNReal.ofReal p)) volume := hNd.neg
  have key : ∀ G : WmpSpace d m p, (sa16so_pairN d m p (sa16y4_tau1 d m hm k) hN).comp (WmpSpace d m p).subtypeL G =
      sa16so_ellN d m p hMm G := by
    intro G
    refine (sa16r_Jcc_dense d m p).induction_on G (isClosed_eq ?_ ?_) (fun φ => ?_)
    · exact ((sa16so_pairN d m p (sa16y4_tau1 d m hm k) hN).comp (WmpSpace d m p).subtypeL).continuous
    · exact (sa16so_ellN d m p hMm).continuous
    · have hφ : IsCcInfty (φ : EuclideanSpace ℝ (Fin d) → ℝ) := φ.2
      rw [ContinuousLinearMap.comp_apply, sa16so_pairN_apply, sa16so_ellN_apply, sa16r_Jcc_eq]
      have e1 : ∫ x, (((((WmpSpace d m p).subtypeL (sa16r_cc_elt (p := p) hφ m)) : WLp d m p) :
          EuclideanSpace ℝ (Fin d) → (WIndex d m → ℝ)) x (sa16y4_tau1 d m hm k)) * N x =
          ∫ x, fderiv ℝ (φ : EuclideanSpace ℝ (Fin d) → ℝ) x (EuclideanSpace.single k 1) * N x := by
        refine integral_congr_ae ?_
        filter_upwards [sa16r_cc_elt_coe (p := p) hφ m] with x hx
        show (((sa16r_cc_elt (p := p) hφ m : WmpSpace d m p) : WLp d m p) :
          EuclideanSpace ℝ (Fin d) → (WIndex d m → ℝ)) x (sa16y4_tau1 d m hm k) * N x = _
        rw [hx]
        have hp1 : partialDeriv (fun _ : Fin 1 => k) (φ : EuclideanSpace ℝ (Fin d) → ℝ) x =
            fderiv ℝ (φ : EuclideanSpace ℝ (Fin d) → ℝ) x (EuclideanSpace.single k 1) := by
          simp [partialDeriv, iteratedFDeriv_one_apply]
        exact congrArg (· * N x) hp1
      have e3 : ∫ x, wrep d m p (sa16r_cc_elt (p := p) hφ m) x * (-fderiv ℝ N x (EuclideanSpace.single k 1)) =
          ∫ x, (φ : EuclideanSpace ℝ (Fin d) → ℝ) x * (-fderiv ℝ N x (EuclideanSpace.single k 1)) := by
        refine integral_congr_ae ?_
        filter_upwards [sa16r_cc_elt_wrep (p := p) hφ m] with x hx
        rw [hx]
      rw [e1, e3]
      have hφc : Continuous (φ : EuclideanSpace ℝ (Fin d) → ℝ) := hφ.1.continuous
      have hNc : Continuous N := hN1.continuous
      have hdN : Continuous (fun x => fderiv ℝ N x (EuclideanSpace.single k 1)) :=
        (hN1.continuous_fderiv (by simp)).clm_apply continuous_const
      have hdφ : Continuous (fun x => fderiv ℝ (φ : EuclideanSpace ℝ (Fin d) → ℝ) x (EuclideanSpace.single k 1)) :=
        (hφ.1.continuous_fderiv (by simp)).clm_apply continuous_const
      have hdφs : HasCompactSupport (fun x => fderiv ℝ (φ : EuclideanSpace ℝ (Fin d) → ℝ) x (EuclideanSpace.single k 1)) :=
        (hφ.2.fderiv ℝ).comp_left (g := fun A : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ => A (EuclideanSpace.single k 1)) (by simp)
      have h1 : Integrable (fun x => fderiv ℝ N x (EuclideanSpace.single k 1) * (φ : EuclideanSpace ℝ (Fin d) → ℝ) x) :=
        (hdN.mul hφc).integrable_of_hasCompactSupport hφ.2.mul_left
      have h2 : Integrable (fun x => N x * fderiv ℝ (φ : EuclideanSpace ℝ (Fin d) → ℝ) x (EuclideanSpace.single k 1)) :=
        (hNc.mul hdφ).integrable_of_hasCompactSupport hdφs.mul_left
      have h3 : Integrable (fun x => N x * (φ : EuclideanSpace ℝ (Fin d) → ℝ) x) :=
        (hNc.mul hφc).integrable_of_hasCompactSupport hφ.2.mul_left
      have := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume) (v := EuclideanSpace.single k 1)
        (f := N) (g := (φ : EuclideanSpace ℝ (Fin d) → ℝ)) h1 h2 h3
        (fun x _ => (hN1.differentiable (by simp)) x) (fun x _ => (hφ.1.differentiable (by simp)) x)
      have e5 : ∫ x, fderiv ℝ (φ : EuclideanSpace ℝ (Fin d) → ℝ) x (EuclideanSpace.single k 1) * N x =
          ∫ x, N x * fderiv ℝ (φ : EuclideanSpace ℝ (Fin d) → ℝ) x (EuclideanSpace.single k 1) :=
        integral_congr_ae (Eventually.of_forall fun x => mul_comm _ _)
      have e6 : ∫ x, (φ : EuclideanSpace ℝ (Fin d) → ℝ) x * (-fderiv ℝ N x (EuclideanSpace.single k 1)) =
          -∫ x, fderiv ℝ N x (EuclideanSpace.single k 1) * (φ : EuclideanSpace ℝ (Fin d) → ℝ) x := by
        rw [← integral_neg]
        exact integral_congr_ae (Eventually.of_forall fun x => by ring)
      rw [e5, e6, this]
  have h := key G
  rw [ContinuousLinearMap.comp_apply, sa16so_pairN_apply, sa16so_ellN_apply] at h
  refine h.trans ?_
  rw [← integral_neg]
  exact integral_congr_ae (Eventually.of_forall fun x => by ring)

end Wk1

end HRS.Whole.AppendixA.Phase2SA16R
