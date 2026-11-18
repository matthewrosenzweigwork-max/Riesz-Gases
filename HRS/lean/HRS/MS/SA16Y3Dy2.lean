import HRS.MS.SA16Y3Dy1
import HRS.MS.SA16StrongSL4

/-!
# S.A.16 (SA16Y3) Dy2: component pairings of `WmpSpace` against smooth test functions (packet P8, iso case, step b2)

`sa16y3_comp_ell`: for `N ∈ C_c^∞` and a component `τ` of the jet, the pairing `G ↦ ∫ (G x τ) N x` on `WmpSpace d m p`
equals the zeroth-component pairing `G ↦ ∫ wrep G · M` with `M = (-1)^{|τ|} ∂^{idx'} N ∈ C_c^∞` (`idx'` from the
multi-index integration by parts `sa16s_ibp_tuple`). Proof: density of `Jcc` (`sa16r_Jcc_dense`), both sides continuous.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer

section Dy2
variable {d : ℕ} {p : ℝ}

theorem sa16y3_comp_ell [Fact (2 ≤ p)] {m : ℕ} {N : EuclideanSpace ℝ (Fin d) → ℝ} (hN : IsCcInfty N)
    (τ : WIndex d m) :
    ∃ M : EuclideanSpace ℝ (Fin d) → ℝ, IsCcInfty M ∧ ∀ G : WmpSpace d m p,
      ∫ x, ((((G : WmpSpace d m p) : WLp d m p) : EuclideanSpace ℝ (Fin d) → (WIndex d m → ℝ)) x τ) * N x =
        ∫ x, wrep d m p G x * M x := by
  obtain ⟨idx', hidx⟩ := sa16s_ibp_tuple (d := d) (τ.1 : ℕ) τ.2
  obtain ⟨M, hMdef⟩ : ∃ M : EuclideanSpace ℝ (Fin d) → ℝ,
      M = fun x => (-1 : ℝ) ^ (τ.1 : ℕ) * partialDeriv idx' N x := ⟨_, rfl⟩
  have hpd : IsCcInfty (partialDeriv idx' N) := sa16s_cc_partialDeriv hN idx'
  have hM : IsCcInfty M := by
    rw [hMdef]
    exact ⟨contDiff_const.mul hpd.1, hpd.2.mul_left⟩
  have hNm : MemLp N (ENNReal.conjExponent (ENNReal.ofReal p)) volume :=
    hN.1.continuous.memLp_of_hasCompactSupport hN.2
  have hMm : MemLp M (ENNReal.conjExponent (ENNReal.ofReal p)) volume :=
    hM.1.continuous.memLp_of_hasCompactSupport hM.2
  have key : ∀ G : WmpSpace d m p, (sa16so_pairN d m p τ hNm).comp (WmpSpace d m p).subtypeL G =
      sa16so_ellN d m p hMm G := by
    intro G
    refine (sa16r_Jcc_dense d m p).induction_on G (isClosed_eq ?_ ?_) (fun φ => ?_)
    · exact ((sa16so_pairN d m p τ hNm).comp (WmpSpace d m p).subtypeL).continuous
    · exact (sa16so_ellN d m p hMm).continuous
    · have hφ : IsCcInfty (φ : EuclideanSpace ℝ (Fin d) → ℝ) := φ.2
      rw [ContinuousLinearMap.comp_apply, sa16so_pairN_apply, sa16so_ellN_apply, sa16r_Jcc_eq]
      have e1 : ∫ x, (((((WmpSpace d m p).subtypeL (sa16r_cc_elt (p := p) hφ m)) : WLp d m p) :
          EuclideanSpace ℝ (Fin d) → (WIndex d m → ℝ)) x τ) * N x =
          ∫ x, partialDeriv τ.2 (φ : EuclideanSpace ℝ (Fin d) → ℝ) x * N x := by
        refine integral_congr_ae ?_
        filter_upwards [sa16r_cc_elt_coe (p := p) hφ m] with x hx
        show (((sa16r_cc_elt (p := p) hφ m : WmpSpace d m p) : WLp d m p) :
          EuclideanSpace ℝ (Fin d) → (WIndex d m → ℝ)) x τ * N x = _
        rw [hx]
        rfl
      have e2 : ∫ x, partialDeriv τ.2 (φ : EuclideanSpace ℝ (Fin d) → ℝ) x * N x =
          (-1 : ℝ) ^ (τ.1 : ℕ) * ∫ x, (φ : EuclideanSpace ℝ (Fin d) → ℝ) x * partialDeriv idx' N x :=
        hidx _ N hφ hN
      have e3 : ∫ x, wrep d m p (sa16r_cc_elt (p := p) hφ m) x * M x =
          ∫ x, (φ : EuclideanSpace ℝ (Fin d) → ℝ) x * M x := by
        refine integral_congr_ae ?_
        filter_upwards [sa16r_cc_elt_wrep (p := p) hφ m] with x hx
        rw [hx]
      have e4 : ∫ x, (φ : EuclideanSpace ℝ (Fin d) → ℝ) x * M x =
          (-1 : ℝ) ^ (τ.1 : ℕ) * ∫ x, (φ : EuclideanSpace ℝ (Fin d) → ℝ) x * partialDeriv idx' N x := by
        rw [← integral_const_mul]
        refine integral_congr_ae (Eventually.of_forall fun x => ?_)
        rw [hMdef]
        ring
      rw [e1, e2, e3, e4]
  refine ⟨M, hM, fun G => ?_⟩
  have h := key G
  rw [ContinuousLinearMap.comp_apply, sa16so_pairN_apply, sa16so_ellN_apply] at h
  exact h

end Dy2

end HRS.Whole.AppendixA.Phase2SA16R
