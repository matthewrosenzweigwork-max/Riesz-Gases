import HRS.MS.WadAux63
import HRS.MS.MovAdjAux11
import HRS.MS.MovLinAux11

/-!
# S8.3, packet S8D-2, part 10: the `L²(μ)` decay of classical solutions (bridge to S6.2/S6.7)

`s8d_l2_classical`: there are `λ > 0`, `C₀ ≥ 1` with, for every frozen classical adjoint solution `w` on `[0,t]`,
`∫ρ (w_0 - μ(w_0))² ≤ (C₀ e^{-λt})² ∫ρ (φ - μ(φ))²`.  It is `ψ[w_0] = T(t)^† ψ[φ]` (`s67_psi_eq`) together with
`‖T(t)‖ ≤ C₀e^{-λt}` on `L²_0` (`movlin_L2_decay`); here `critCoeff d a β ρβ` is, by definition, the stationary
coefficient `(quadraticGradientDyn d (d/2) a β).coeff (fun _ => ρβ)` of S6.7.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Metric
open scoped ENNReal NNReal ContDiff

namespace HRS.MS.Wad

open HRS HRS.Whole

variable {d : ℕ}

theorem s8d_norm_sq_mk {s β q : ℝ} {ρ : Euc d → ℝ} (H : HRS.MS.MovLin.Mov2dTh d s β q ρ)
    (ψ0 : SchwartzMap (Euc d) ℝ) (hψ0 : (⇑ψ0 : Euc d → ℝ) = fun x => Real.sqrt (ρ x))
    (hρ0 : ∀ x, 0 ≤ ρ x) {u : Euc d → ℝ} (hu : AEStronglyMeasurable u (volume : Measure (Euc d)))
    (hbd : ∃ B : ℝ, ∀ x, |u x| ≤ B) :
    ‖HRS.MS.MovAdj.s67mk' H ψ0 hψ0 hu hbd‖ ^ 2 = ∫ x, ρ x * (u x - ∫ y, u y * ρ y) ^ 2 := by
  have hae := HRS.MS.MovAdj.s67mk'_ae H ψ0 hψ0 hu hbd
  set v := HRS.MS.MovAdj.s67mk' H ψ0 hψ0 hu hbd with hv
  have h1 : ‖v‖ ^ 2 = ∫ x, (movFun v x) ^ 2 := by
    have h2 : ‖(v : Lp ℝ 2 (volume : Measure (Euc d)))‖ ^ 2 =
        inner ℝ (v : Lp ℝ 2 (volume : Measure (Euc d))) (v : Lp ℝ 2 (volume : Measure (Euc d))) :=
      (real_inner_self_eq_norm_sq _).symm
    have h3 : ‖v‖ = ‖(v : Lp ℝ 2 (volume : Measure (Euc d)))‖ := rfl
    rw [h3, h2, MeasureTheory.L2.inner_def]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    show inner ℝ ((v : Lp ℝ 2 (volume : Measure (Euc d))) x) ((v : Lp ℝ 2 (volume : Measure (Euc d))) x) =
      (movFun v x) ^ 2
    simp [sq]
  rw [h1]
  refine integral_congr_ae (hae.mono fun x hx => ?_)
  show (movFun v x) ^ 2 = _
  rw [hx]
  unfold HRS.MS.MovAdj.s67psi
  rw [mul_pow, Real.sq_sqrt (hρ0 x)]

set_option maxHeartbeats 1600000 in
theorem s8d_l2_classical (hd : 2 ≤ d) {a β : ℝ} (ha : 0 < a) (hβ : 0 < β) {ρβ : Euc d → ℝ}
    (hρ : IsThermalEquilibrium d ((d : ℝ) / 2) a β ρβ) :
    ∃ lam C0 : ℝ, 0 < lam ∧ 1 ≤ C0 ∧ ∀ {t : ℝ} {φ : Euc d → ℝ} {w : ℝ → Euc d → ℝ}, 0 ≤ t →
      IsClassicalAdjointW (critCoeff d a β ρβ) t φ w →
      ∫ x, ρβ x * (w 0 x - ∫ y, w 0 y * ρβ y) ^ 2 ≤
        (C0 * Real.exp (-lam * t)) ^ 2 * ∫ x, ρβ x * (φ x - ∫ y, φ y * ρβ y) ^ 2 := by
  have hs0 : (0 : ℝ) ≤ (d : ℝ) / 2 := by positivity
  have hsd : (d : ℝ) / 2 < d := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have H : HRS.MS.MovLin.Mov2dTh d ((d : ℝ) / 2) β a ρβ := ⟨hd, hs0, hsd, hβ, ha, hρ⟩
  obtain ⟨ψ0, hψ0⟩ := HRS.MS.MovLin.mov2d_sqrt_schwartz H
  obtain ⟨lam, hlam, C0, hC0, hdec⟩ := HRS.MS.MovLin.movlin_L2_decay H ψ0 hψ0
  have hρ0 : ∀ x, 0 ≤ ρβ x := hρ.1.1.nonneg
  refine ⟨lam, C0, hlam, hC0, fun {t φ w} ht hw => ?_⟩
  have hw' : IsClassicalAdjointW (((quadraticGradientDyn d ((d : ℝ) / 2) a β).coeff (fun _ => ρβ))) t φ w := hw
  have h0I : (0 : ℝ) ∈ Set.Icc (0 : ℝ) t := ⟨le_rfl, ht⟩
  have heq := HRS.MS.MovAdj.s67_psi_eq H ψ0 hψ0 hw' ht h0I
  have hn1 := HRS.MS.MovAdj.s67_f_aux hw' h0I
  have hn2 := HRS.MS.MovAdj.s67_phi_aux hw' ht
  set A := HRS.MS.MovAdj.s67mk' H ψ0 hψ0 hn1.1 hn1.2 with hA
  set B := HRS.MS.MovAdj.s67mk' H ψ0 hψ0 hn2.1 hn2.2 with hB
  have hnorm : ‖A‖ ≤ C0 * Real.exp (-lam * t) * ‖B‖ := by
    rw [heq]
    have hT : ‖HRS.MS.MovLin.mov2d_T H ψ0 hψ0 (t - 0)‖ ≤ C0 * Real.exp (-lam * t) := by
      refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
      have := hdec (t - 0) (sub_nonneg.2 ht) v
      simpa using this
    calc ‖(ContinuousLinearMap.adjoint (HRS.MS.MovLin.mov2d_T H ψ0 hψ0 (t - 0))) B‖
        ≤ ‖ContinuousLinearMap.adjoint (HRS.MS.MovLin.mov2d_T H ψ0 hψ0 (t - 0))‖ * ‖B‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ = ‖HRS.MS.MovLin.mov2d_T H ψ0 hψ0 (t - 0)‖ * ‖B‖ := by rw [LinearIsometryEquiv.norm_map]
      _ ≤ C0 * Real.exp (-lam * t) * ‖B‖ := mul_le_mul_of_nonneg_right hT (norm_nonneg _)
  have hsqA := s8d_norm_sq_mk H ψ0 hψ0 hρ0 hn1.1 hn1.2
  have hsqB := s8d_norm_sq_mk H ψ0 hψ0 hρ0 hn2.1 hn2.2
  rw [← hsqA, ← hsqB, ← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) hnorm 2

end HRS.MS.Wad
