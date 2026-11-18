import HRS.MS.SA16Y3Pair1
import HRS.MS.SA16ZF1
import HRS.MS.SA16SEn13

/-!
# S.A.16 (SA16Y3) Diss1: dissipativity of `λ P_μ` on all of `W^{m+2,p}` (packet P7 iso, step (a), item (iii))

`sa16y3_diss`: let `T : W^{m+2,p} →L W^{m,p}` have jets `T(Jφ) ~ wJet m (P_μ φ)` for `φ ∈ C_c^∞` (`μ ≥ 0` in `C_b^∞`,
`‖D^kμ‖ ≤ Λ` for `k ≤ m+3`, `d-1 < s < d`). Then for `λ ≥ 0` and EVERY `G ∈ W^{m+2,p}`
`d(jetEnergy_m)_{ι²G}(λ T G) ≤ p λ C jetEnergy_m(ι²G)`, `C = C(d,s,p,Λ,m)` (density from `C_c^∞` via `sa16z_iso_pairing`).
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer
open HRS.Whole.AppendixA.Phase2SA16V2

section Diss1
variable {d : ℕ} {s p : ℝ} [Fact (2 ≤ p)]

theorem sa16y3_diss (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hθ1 : 1 < s + 2 - d) (m : ℕ) (Λ : ℝ) (hΛ : 0 ≤ Λ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {μ : Euc d → ℝ}, HRS.S16Frac.S16FracCb μ → (∀ x, 0 ≤ μ x) → sa16z_Cb (m + 3) Λ μ →
      ∀ (T : WmpSpace d (m + 1 + 1) p →L[ℝ] WmpSpace d m p),
        (∀ φ : ccSub d, (((T (sa16r_Jcc d (m + 1 + 1) p φ) : WmpSpace d m p) : WLp d m p) :
          Euc d → (WIndex d m → ℝ)) =ᵐ[volume] wJet m (sa16z_P s μ φ.1)) →
        ∀ {lam : ℝ}, 0 ≤ lam → ∀ G : WmpSpace d (m + 1 + 1) p,
          fderiv ℝ (jetEnergy d m p) (sa16sz_iota2 d m p G) (lam • T G) ≤
            p * lam * C * jetEnergy d m p (sa16sz_iota2 d m p G) := by
  have hp2 : (2 : ℝ) ≤ p := Fact.out
  have hp0 : 0 < p := by linarith
  obtain ⟨C, hC0, hC⟩ := sa16z_iso_pairing hd hs0 hsd hθ1 hp2 Λ hΛ m
  refine ⟨C, hC0, fun {μ} hμ hpos hCb T hT {lam} hlam G => ?_⟩
  have hder : fderiv ℝ (jetEnergy d m p) = sa16v2_Dj d m p :=
    funext fun G => (sa16v2_jetEnergy_hasFDerivAt d m p G).fderiv
  have hDc : Continuous (sa16v2_Dj d m p) := sa16v2_Dj_continuous d m p
  have hι2 := (sa16sz_iota2 d m p).continuous
  refine (sa16r_Jcc_dense d (m + 1 + 1) p).induction_on G (isClosed_le ?_ ?_) (fun φ => ?_)
  · rw [hder]
    exact (hDc.comp hι2).clm_apply (T.continuous.const_smul lam)
  · exact continuous_const.mul ((sa16sz_jetEnergy_cont m).comp hι2)
  · rw [sa16sz_iota2_Jcc, map_smul, smul_eq_mul, sa16y3_fderiv_pair m φ (T (sa16r_Jcc d (m + 1 + 1) p φ)) (hT φ),
      sa16sz_energy_cc]
    have h1 := hC hμ hpos φ.2 hCb
    have h2 : 0 ≤ p * lam := mul_nonneg hp0.le hlam
    calc lam * (p * ∫ x, sa16sz_dens m p φ.1 (sa16z_P s μ φ.1) x)
        = (p * lam) * ∫ x, sa16sz_dens m p φ.1 (sa16z_P s μ φ.1) x := by ring
      _ ≤ (p * lam) * (C * ∑ k : Fin (m + 1), ∫ x, sa16sz_vn φ.1 k x ^ p) := mul_le_mul_of_nonneg_left h1 h2
      _ = _ := by ring

end Diss1

end HRS.Whole.AppendixA.Phase2SA16R
