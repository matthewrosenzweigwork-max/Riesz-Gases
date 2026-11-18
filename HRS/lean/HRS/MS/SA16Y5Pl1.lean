import HRS.MS.SA16Y5Rm1

/-!
# S.A.16 (SA16Y5) Pl1: `P_μ ψ = -c Λ^θ(μψ) - ∑_i ∂_i(g ⋆ (∂_iμ ψ))` and the `L^p` bound of the second term (`θ < 1`)

`sa16y5_P_lap'`: the integration-by-parts identity of `sa16z_P_lap` before the second term is converted into a principal
value (valid for all `0 < θ = s+2-d`); `sa16y5_Rw_bound`: `‖∑_i ∂_i (g ⋆ (∂_iμ w))‖_p ≤ K d ‖w‖_p` under `Dec 2 W μ`
(`0 ≤ s < d-1`, `d < p(s+1)`), by `sa16y5_D0`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff SchwartzMap

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer
open HRS.Whole.AppendixA.Phase2SA16Q

section Pl1
variable {d : ℕ} {s : ℝ}

theorem sa16y5_P_lap' (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hθ0 : 0 < s + 2 - d) :
    ∃ c : ℝ, 0 < c ∧ ∀ {μ : Euc d → ℝ}, HRS.S16Frac.S16FracCb μ → ∀ {ψ : Euc d → ℝ}, IsCcInfty ψ → ∀ x : Euc d,
      sa16z_P s μ ψ x = -c * fracLap d (s + 2 - d) (fun y => μ y * ψ y) x -
        ∑ i : Fin d, fderiv ℝ (convFun (rieszKernel d s) (fun z => sa16z_dm μ i z * ψ z)) x (sa16z_e i) := by
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
  rfl

theorem sa16y5_Rw_bound (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hs1 : s < (d : ℝ) - 1) {p : ℝ} (hp : 2 ≤ p)
    (hfar : (d : ℝ) < p * (s + 1)) {W : ℝ} (hW : 0 ≤ W) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {μ w : Euc d → ℝ}, ContDiff ℝ ∞ μ → sa16y5_Dec 2 W μ → IsCcInfty w →
      eLpNorm (fun x => ∑ i : Fin d, fderiv ℝ (convFun (rieszKernel d s) (fun z => sa16z_dm μ i z * w z)) x (sa16z_e i))
        (ENNReal.ofReal p) volume ≤ ENNReal.ofReal (K * (d : ℝ)) * eLpNorm w (ENNReal.ofReal p) volume := by
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    simpa using ENNReal.ofReal_le_ofReal (by linarith : (1 : ℝ) ≤ p)
  obtain ⟨K, hK0, hK⟩ := sa16y5_D0 hd hs0 hs1 hp hfar hW
  refine ⟨K, hK0, fun {μ w} hμ hdec hw => ?_⟩
  have hfun : (fun x => ∑ i : Fin d, fderiv ℝ (convFun (rieszKernel d s) (fun z => sa16z_dm μ i z * w z)) x
      (sa16z_e i)) = ∑ i : Fin d, (fun x => fderiv ℝ (convFun (rieszKernel d s)
        (fun z => sa16z_dm μ i z * w z)) x (sa16z_e i)) := by
    funext x; simp [Finset.sum_apply]
  have hi : ∀ i : Fin d, eLpNorm (fun x => fderiv ℝ (convFun (rieszKernel d s) (fun z => sa16z_dm μ i z * w z)) x
      (sa16z_e i)) (ENNReal.ofReal p) volume ≤ ENNReal.ofReal K * eLpNorm w (ENNReal.ofReal p) volume :=
    fun i => hK (sa16z_dm_smooth hμ i) (sa16y5_Dec_dm hμ hdec i) hw i
  rw [hfun]
  refine (eLpNorm_sum_le hp1).trans ((Finset.sum_le_sum fun i _ => hi i).trans (le_of_eq ?_))
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ENNReal.ofReal_mul hK0,
    ENNReal.ofReal_natCast]
  ring

end Pl1

end HRS.Whole.AppendixA.Phase2SA16R
