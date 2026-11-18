import HRS.MS.MfeConfAux105

/-!
# S.B.1, packet F9 (part 9): pointwise limits of the level-`M` commutator energy and of its Gibbs mean

For `r ∈ [0,T]`, the concrete family `k_M = sb1kM d s M`, and the Lipschitz bound of the exact transport:
* `sb1_kM_Ck_tendsto`: `C^M_r(Z) → C_r(Z)` for every collision-free `Z`;
* `sb1_kM_EQ_tendsto`: `E_{Q^M_r} C^M_r → E_{Q_r} C_r`.
-/

noncomputable section

open MeasureTheory Filter Topology
open HRS HRS.Whole
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MfeConf

variable {d N : ℕ}

theorem sb1_Kpi_pos' {s : ℝ} {k : Euc d → ℝ} {ρ0 : Euc d → ℝ} {Cρ M1 : ℝ} (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d)
    (hN : 1 ≤ N) {β : ℝ} (hβ : 0 ≤ β) (hk : Sb1KerU d s k) (R : Sb1Rho ρ0 Cρ M1) :
    0 < ∫ X : Whole.EucConfig d N, sb1FF k β N ρ0 X ∂(Measure.pi fun _ : Fin N => Whole.withDensityReal ρ0) := by
  haveI : IsProbabilityMeasure (Whole.withDensityReal ρ0) := HRS.MS.Thm.cb_withDensityReal_isProb R.dens
  unfold sb1FF
  refine integral_exp_pos ?_
  exact Integrable.of_bound (C := sb1CwR d s Cρ M1 β N)
    (Real.measurable_exp.comp ((sb1_En_meas hk R).const_mul _)).aestronglyMeasurable
    (Eventually.of_forall fun X => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact sb1_E_le hd hs0 hsd hN hβ hk R X)

section Main

variable {D : Whole.WholeDyn d} {T C B C3 : ℝ} {ρ : ℝ → Euc d → ℝ} (H : Sb1Tr3 D T C B C3 ρ)

include H

theorem sb1_lv_EQ_eq {k : Euc d → ℝ} (hk : Measurable k) {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) T) :
    sb1_lv_EQ D k N ρ r = (sb1Kpi k D.invβ⁻¹ N ρ r)⁻¹ *
      sb1Phipi k (fun r => Whole.mfeTransportW D (ρ r)) D.invβ⁻¹ N ρ r := by
  have hdens := (H.tr.slice r hr).dens
  unfold sb1_lv_EQ
  rw [sb1_integral_modGibbs hk hdens, sb1_gibbs_eq_Kpi H hr]
  congr 1
  unfold sb1Phipi
  rw [sb1_integral_pi hdens]
  refine integral_congr_ae (Eventually.of_forall fun X => ?_)
  simp only [sb1FF, sb1_lv_Ck, mul_assoc]
  rfl

theorem sb1_kM_Ck_tendsto (hs0 : 0 ≤ D.s) {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) T) {Kr : ℝ} (hKr : 0 ≤ Kr)
    (hL : ∀ x y, ‖Whole.mfeTransportW D (ρ r) x - Whole.mfeTransportW D (ρ r) y‖ ≤ Kr * ‖x - y‖)
    (hLc : Continuous (Whole.mfeTransportW D (ρ r)))
    (Z : Whole.EucConfig d N) (hZ : ∀ i j, i ≠ j → Z i ≠ Z j) :
    Tendsto (fun M => sb1_lv_Ck D (sb1kM d D.s M) N ρ r Z) atTop (𝓝 (sb1CN D N ρ r Z)) := by
  obtain ⟨A, hA0, hA⟩ := sb1kM_hk_bound (d := d) D.s hs0
  have hd := H.tr.hd
  have hsd := H.tr.hsd
  have R := H.rho hd hr
  unfold sb1_lv_Ck sb1CN
  rw [show Whole.commutatorKernel d D.s (Whole.mfeTransportW D (ρ r)) =
      sb1hk (Whole.rieszKernel d D.s) (Whole.mfeTransportW D (ρ r)) from sb1_commKernel_eq D.s _]
  refine sb1_pairE_tendsto (hn := fun M x y => sb1hk (sb1kM d D.s M) (Whole.mfeTransportW D (ρ r)) x y)
    hd hs0 hsd R (mul_nonneg hA0 hKr) (fun M x y => hA M hKr hL x y) (fun M => ?_) (fun x y hxy => ?_) Z hZ
  · have hc : Continuous (fun p : Euc d × Euc d => sb1hk (sb1kM d D.s M) (Whole.mfeTransportW D (ρ r)) p.1 p.2) := by
      unfold sb1hk
      have h1 : Continuous (fderiv ℝ (sb1kM d D.s M)) :=
        ((sb1kM_isKernel D.s hs0 M).smooth.continuous_fderiv (by norm_num))
      exact (h1.comp (continuous_fst.sub continuous_snd)).clm_apply
        ((hLc.comp continuous_fst).sub (hLc.comp continuous_snd))
    exact hc.measurable
  · exact sb1kM_fderiv_tend D.s hs0 (sub_ne_zero.2 hxy) _

theorem sb1_kM_EQ_tendsto (hβ : 0 < D.invβ) (hN : 1 ≤ N) {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) T) {Kr : ℝ} (hKr : 0 ≤ Kr)
    (hL : ∀ x y, ‖Whole.mfeTransportW D (ρ r) x - Whole.mfeTransportW D (ρ r) y‖ ≤ Kr * ‖x - y‖) :
    Tendsto (fun M => sb1_lv_EQ D (sb1kM d D.s M) N ρ r) atTop (𝓝 (sb1EQ D N ρ r)) := by
  have hs0 := H.tr.hs0
  obtain ⟨A, hA0, hA⟩ := sb1kM_hk_bound (d := d) D.s hs0
  have hd := H.tr.hd
  have hsd := H.tr.hsd
  have R := H.rho hd hr
  have hβ0 : 0 ≤ D.invβ⁻¹ := (inv_pos.2 hβ).le
  have hg := sb1KerU_riesz d D.s hs0
  have hconv : ∀ z : Euc d, z ≠ 0 → Tendsto (fun M => sb1kM d D.s M z) atTop (𝓝 (Whole.rieszKernel d D.s z)) :=
    fun z hz => sb1kM_tend D.s hs0 hz
  have hLc : Continuous (Whole.mfeTransportW D (ρ r)) := by
    have : LipschitzWith (Real.toNNReal Kr) (Whole.mfeTransportW D (ρ r)) := by
      refine LipschitzWith.of_dist_le_mul fun x y => ?_
      rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ hKr]; exact hL x y
    exact this.continuous
  have hKt := sb1_K_tendsto hd hs0 hsd hN hβ0 (sb1kM_ker D.s hs0) hg hconv R (N := N)
  have hPt := sb1_Phi_tendsto hd hs0 hsd hN hβ0 (sb1kM_ker D.s hs0) hconv R (mul_nonneg hA0 hKr)
    (hn := fun M x y => sb1hk (sb1kM d D.s M) (Whole.mfeTransportW D (ρ r)) x y)
    (h := sb1hk (Whole.rieszKernel d D.s) (Whole.mfeTransportW D (ρ r)))
    (fun M x y => hA M hKr hL x y)
    (fun M => by
      have h1 : Continuous (fderiv ℝ (sb1kM d D.s M)) :=
        ((sb1kM_isKernel D.s hs0 M).smooth.continuous_fderiv (by norm_num))
      have hc : Continuous (fun p : Euc d × Euc d => sb1hk (sb1kM d D.s M) (Whole.mfeTransportW D (ρ r)) p.1 p.2) := by
        unfold sb1hk
        exact (h1.comp (continuous_fst.sub continuous_snd)).clm_apply
          ((hLc.comp continuous_fst).sub (hLc.comp continuous_snd))
      exact hc.measurable)
    (fun x y hxy => sb1kM_fderiv_tend D.s hs0 (sub_ne_zero.2 hxy) _)
  have hKpos := sb1_Kpi_pos' (N := N) hd hs0 hsd hN hβ0 hg R
  have e1 : ∀ M, sb1_lv_EQ D (sb1kM d D.s M) N ρ r = (sb1Kpi (sb1kM d D.s M) D.invβ⁻¹ N ρ r)⁻¹ *
      sb1Phipi (sb1kM d D.s M) (fun r => Whole.mfeTransportW D (ρ r)) D.invβ⁻¹ N ρ r := fun M =>
    sb1_lv_EQ_eq H (sb1kM_ker D.s hs0 M).meas hr
  have e2 : sb1EQ D N ρ r = (sb1Kpi (Whole.rieszKernel d D.s) D.invβ⁻¹ N ρ r)⁻¹ *
      sb1Phipi (Whole.rieszKernel d D.s) (fun r => Whole.mfeTransportW D (ρ r)) D.invβ⁻¹ N ρ r :=
    sb1_EQ_eq H hr
  simp only [e1, e2]
  refine (hKt.inv₀ hKpos.ne').mul ?_
  unfold sb1Phipi
  simp only [sb1hk] at hPt ⊢
  exact hPt

end Main

end HRS.MS.MfeConf
