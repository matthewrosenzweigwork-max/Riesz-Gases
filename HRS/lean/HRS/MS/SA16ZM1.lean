import HRS.MS.SA16ZR5

/-!
# S.A.16 (SA16Z) M1: `P_μ ψ = -c Λ^θ(μψ) + c_s ∑_i pvOdd_i(∂_iμ ψ)` (integration by parts)
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff SchwartzMap

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer

section M1
variable {d : ℕ} {s : ℝ}

theorem sa16z_P_lap (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hθ0 : 0 < s + 2 - d) :
    ∃ c : ℝ, 0 < c ∧ ∀ {μ : Euc d → ℝ}, HRS.S16Frac.S16FracCb μ → ∀ {ψ : Euc d → ℝ}, IsCcInfty ψ → ∀ x : Euc d,
      sa16z_P s μ ψ x = -c * fracLap d (s + 2 - d) (fun y => μ y * ψ y) x +
        HRS.CZ.Hls.hlsg_c s * ∑ i : Fin d,
          pvOdd d (s + 2 - d) (fun u : Euc d => u i) (fun y => sa16z_dm μ i y * ψ y) x := by
  obtain ⟨c, hc, hlap⟩ := HRS.S16Frac.s16frac_lap_fracLap hd hs0 hsd hθ0
  refine ⟨c, hc, fun {μ} hμ {ψ} hψ x => ?_⟩
  set W : 𝓢(Euc d, ℝ) := sa16z_schw hψ with hW
  have hWc : ⇑W = ψ := rfl
  set u := HRS.S16Frac.s16frac_mul μ hμ W with hu
  have hua : ∀ y, u y = μ y * ψ y := fun y => HRS.S16Frac.s16frac_mul_apply μ hμ W y
  have hibp : ∀ i : Fin d, fderiv ℝ (convFun (rieszKernel d s) (sa16z_src μ ψ i)) x (sa16z_e i) =
      fderiv ℝ (fun y => fderiv ℝ (convFun (rieszKernel d s) u) y (sa16z_e i)) x (sa16z_e i) -
        fderiv ℝ (convFun (rieszKernel d s) (fun z => fderiv ℝ μ z (sa16z_e i) * ψ z)) x (sa16z_e i) := by
    intro i
    have := (HRS.S16Frac.s16frac_ibp hd hs0 hsd hμ W i i x).2.2.2
    have e1 : (fun z => μ z * HRS.S16Cze.s16cze_pd W i z) = sa16z_src μ ψ i := by
      funext z; rw [HRS.S16Cze.s16cze_pd_apply]; rfl
    rw [e1] at this
    exact this
  unfold sa16z_P
  simp_rw [hibp]
  have e2 : (⇑u : Euc d → ℝ) = fun y => μ y * ψ y := funext hua
  rw [Finset.sum_sub_distrib, hlap u x, e2]
  have e3 : ∀ i : Fin d, fderiv ℝ (convFun (rieszKernel d s) (fun z => fderiv ℝ μ z (sa16z_e i) * ψ z)) x (sa16z_e i) =
      -(HRS.CZ.Hls.hlsg_c s) * pvOdd d (s + 2 - d) (fun u : Euc d => u i) (fun y => sa16z_dm μ i y * ψ y) x := by
    intro i
    exact sa16z_conv_fderiv_pvOdd hd hs0 hsd ⟨(sa16z_dm_smooth hμ.1 i).mul hψ.1, hψ.2.mul_left⟩ i x
  simp_rw [e3]
  rw [← Finset.mul_sum]
  ring

end M1

end HRS.Whole.AppendixA.Phase2SA16R
