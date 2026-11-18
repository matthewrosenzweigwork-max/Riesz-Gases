import HRS.MS.SA16Y5Id1

/-!
# S.A.16 (SA16Y5) Id2: `Qh a N = P_a`, its bound and the compatibility with `Γ_a` (K3/B8)
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer

section Id2
variable {d : ℕ} {p : ℝ} [Fact (2 ≤ p)] {s : ℝ}

theorem sa16y5_Qh_iota (hd : 1 ≤ d) (hs : 0 < s) (hsd : s < d) (hsd1 : (d : ℝ) < s + 1) (m : ℕ)
    {a : ℝ} (ha : 0 < a) (M : Matrix (Fin d) (Fin d) ℝ) {μ : Euc d → ℝ} (hμ : ContDiff ℝ ∞ μ)
    (N : WmpSpace d (m + 1 + 1) p →L[ℝ] WmpSpace d m p)
    (hN : ∀ φ : ccSub d, wrep d m p (N (sa16r_Jcc d (m + 1 + 1) p φ)) =ᵐ[volume]
      HRS.MH.AdjointRd.eucNonlocal s M μ φ.1) (x : WmpSpace d (m + 1 + 1) p) :
    sa16r_iota d (m + 1) p (sa16y5_Qh d m p a N x) = sa16r_Gam d m p a (N x) := by
  refine (sa16r_Jcc_dense d (m + 1 + 1) p).induction_on x
    (isClosed_eq ((sa16r_iota d (m + 1) p).continuous.comp (sa16y5_Qh d m p a N).continuous)
      ((sa16r_Gam d m p a).continuous.comp N.continuous)) (fun φ => ?_)
  refine sa16r_wrep_inj d (m + 1) p _ _ ?_
  obtain ⟨hFc, B, hB⟩ := sa16y5_euc_cont_bdd hd hs hsd hsd1 M hμ φ.2
  have h1 := (sa16y5_Qh_wrep hd hs hsd hsd1 m ha M hμ N hN φ).1
  have h2 := sa16y5_Gam_wrep ha m (N (sa16r_Jcc d (m + 1 + 1) p φ)) (hN φ) hFc hB
  filter_upwards [sa16r_iota_wrep (p := p) (m + 1) (sa16y5_Qh d m p a N (sa16r_Jcc d (m + 1 + 1) p φ)), h1, h2]
    with z e1 e2 e3
  simp only [e1, e2, e3]

theorem sa16y5_Qh_bound (hd : 1 ≤ d) (hs : 0 < s) (hsd : s < d) (hsd1 : (d : ℝ) < s + 1) (m : ℕ)
    (MB W : ℝ) (hMB : 0 ≤ MB) (hW : 0 ≤ W) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (M : Matrix (Fin d) (Fin d) ℝ), (∀ i j, |M i j| ≤ MB) → ∀ {μ : Euc d → ℝ},
      ContDiff ℝ ∞ μ → (∀ κ ≤ m + 1 + 1 + 1, ∀ x, ‖iteratedFDeriv ℝ κ μ x‖ ≤ W) →
      ∀ (N : WmpSpace d (m + 1 + 1) p →L[ℝ] WmpSpace d m p),
      (∀ φ : ccSub d, wrep d m p (N (sa16r_Jcc d (m + 1 + 1) p φ)) =ᵐ[volume]
        HRS.MH.AdjointRd.eucNonlocal s M μ φ.1) →
      ∀ {a : ℝ}, 0 < a → a ≤ 1 → ‖sa16y5_Qh d m p a N‖ ≤ C * a ^ (-((s + 2 - d) / 2)) := by
  obtain ⟨C, hC0, hC⟩ := sa16y5_Pa_exists hd hs hsd hsd1 (m + 1 + 1) p MB W hMB hW
  refine ⟨C, hC0, fun M hM μ hμ hμb N hN a ha ha1 => ?_⟩
  obtain ⟨Pa, hPb, hPφ⟩ := hC M hM hμ hμb ha ha1
  have : sa16y5_Qh d m p a N = Pa := by
    refine ContinuousLinearMap.ext fun x => ?_
    refine (sa16r_Jcc_dense d (m + 1 + 1) p).induction_on x
      (isClosed_eq (sa16y5_Qh d m p a N).continuous Pa.continuous) (fun φ => ?_)
    refine sa16r_wrep_inj d (m + 1 + 1) p _ _ ?_
    filter_upwards [(sa16y5_Qh_wrep hd hs hsd hsd1 m ha M hμ N hN φ).1, hPφ φ] with z e1 e2
    rw [e1, e2]
  rw [this]
  exact hPb

end Id2

end HRS.Whole.AppendixA.Phase2SA16R
