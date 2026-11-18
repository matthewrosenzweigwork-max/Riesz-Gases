import HRS.MS.MfeConfAux121

/-!
# S.B.1, packet F9 (part 25): integrability of the commutator energy under the singular Gibbs reference, and the packaging `SbMovEnt`

`sb1_CN_Qint`: `C_N(v_r;·,μ_r)` is integrable under `Q_r = ℚ_{N,β}(μ_r)` (the density of `Q_r` is bounded by a multiple of
`μ_r^{⊗N}` and the pair energy is dominated by the integrable majorant `sb1Bmaj`).
-/

noncomputable section

open MeasureTheory Filter Topology
open HRS HRS.Whole HRS.MD.EQLawPath HRS.MP.SelfSimP4Impl
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MfeConf

variable {d N : ℕ}

section Main

variable {D : Whole.WholeDyn d} {T C B C3 : ℝ} {ρ : ℝ → Euc d → ℝ} (H : Sb1Tr3 D T C B C3 ρ)

include H

theorem sb1_CN_Qint (hN : 1 ≤ N) (hβ : 0 < D.invβ) {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) T) {Kr : ℝ} (hKr : 0 ≤ Kr)
    (hL : ∀ x y, ‖Whole.mfeTransportW D (ρ r) x - Whole.mfeTransportW D (ρ r) y‖ ≤ Kr * ‖x - y‖) :
    Integrable (sb1CN D N ρ r) (sb1Q D N ρ r) := by
  have hs0 := H.tr.hs0
  have hd := H.tr.hd
  have hsd := H.tr.hsd
  have hβ0 : 0 < D.invβ⁻¹ := inv_pos.2 hβ
  set β := D.invβ⁻¹ with hβdef
  have R := H.rho hd hr
  have hg := sb1KerU_riesz d D.s hs0
  haveI : IsProbabilityMeasure (Whole.withDensityReal (ρ r)) := HRS.MS.Thm.cb_withDensityReal_isProb R.dens
  have hK : 0 < Whole.gibbsNormalizer (Whole.rieszKernel d D.s) N β (Whole.withDensityReal (ρ r)) := by
    rw [sb1_K_eq R]; exact sb1_Kpi_pos' hd hs0 hsd hN hβ0.le hg R
  have hσ : 0 ≤ Whole.movtr_sigma D.s := sb1_sigma_nonneg hs0
  have hb : ∀ x y, |sb1hk (Whole.rieszKernel d D.s) (Whole.mfeTransportW D (ρ r)) x y| ≤
      Whole.movtr_sigma D.s * Kr * ‖x - y‖ ^ (-D.s) := by
    intro x y
    refine sb1_hk_bound hs0 (fun z hz e => ?_) hKr hL x y
    have := sb1gE_grad_le hs0 (le_refl (0 : ℝ)) hz e (d := d) (s := D.s)
    rwa [Whole.movtr_gEps_zero] at this
  have hvm := (sb1_vm_of_lip H hKr hL).measurable
  have hCN : sb1CN D N ρ r = fun Z => Whole.pairEnergy (sb1hk (Whole.rieszKernel d D.s) (Whole.mfeTransportW D (ρ r)))
      Z (Whole.withDensityReal (ρ r)) := funext fun Z => by unfold sb1CN; rw [sb1_commKernel_eq]
  -- integrability under the product measure
  obtain ⟨hBi, -⟩ := sb1_Bmaj_int hd hs0 hsd R (mul_nonneg hσ hKr) hN (N := N)
  have hPint : Integrable (sb1CN D N ρ r) (Measure.pi fun _ : Fin N => Whole.withDensityReal (ρ r)) := by
    rw [hCN]
    refine hBi.mono' (sb1_pairE_meas R (sb1_meas_hk _ hvm)).aestronglyMeasurable (Eventually.of_forall fun X => ?_)
    rw [Real.norm_eq_abs]
    exact sb1_pairE_abs_le hd hs0 hsd R (mul_nonneg hσ hKr) hb hN X
  -- domination of the Gibbs measure by the product measure
  have hρi : Integrable (ρ r) := R.integrable
  have hpi := HRS.MS.Canon.cn_pi_withDensityReal (N := N) (ρ r) R.dens.nonneg hρi
  set Cw := sb1CwR d D.s C3 (C3 * ∫ y : Euc d, sb1w ((d : ℝ) + 2) y) β N with hCw
  set K := Whole.gibbsNormalizer (Whole.rieszKernel d D.s) N β (Whole.withDensityReal (ρ r)) with hKdef
  have hQ : sb1Q D N ρ r ≤ ENNReal.ofReal (K⁻¹ * Cw) • Measure.pi fun _ : Fin N => Whole.withDensityReal (ρ r) := by
    unfold sb1Q
    rw [sb1_modGibbs_eq_Dm hg.meas R.dens hK, hpi]
    unfold sb1Dm
    rw [← withDensity_smul' _ _ ENNReal.ofReal_ne_top]
    refine withDensity_mono (Eventually.of_forall fun X => ?_)
    show ENNReal.ofReal (sb1qd (Whole.rieszKernel d D.s) β N (ρ r) X) ≤
      ENNReal.ofReal (K⁻¹ * Cw) * ENNReal.ofReal (∏ i, ρ r (X i))
    rw [← ENNReal.ofReal_mul (mul_nonneg (inv_pos.2 hK).le (by rw [hCw]; unfold sb1CwR; exact (Real.exp_pos _).le))]
    refine ENNReal.ofReal_le_ofReal ?_
    unfold sb1qd
    have hP0 : 0 ≤ ∏ i, ρ r (X i) := Finset.prod_nonneg fun i _ => R.dens.nonneg _
    have := sb1_E_le hd hs0 hsd hN hβ0.le hg R X
    calc K⁻¹ * ((∏ i, ρ r (X i)) * Real.exp (-β * N * sb1En (Whole.rieszKernel d D.s) (ρ r) X))
        ≤ K⁻¹ * ((∏ i, ρ r (X i)) * Cw) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left this hP0) (inv_pos.2 hK).le
      _ = K⁻¹ * Cw * ∏ i, ρ r (X i) := by ring
  exact (hPint.smul_measure ENNReal.ofReal_ne_top).mono_measure hQ

/-- **`SbMovEnt` for an initial law dominated by the canonical Gibbs measure** (F9, bounded-density case), modulo the explicit
analytic inputs `SM` (vanishing force-defect remainder), `hBmeas` and `hTM` (measurability). -/
theorem sb1_bdd_movEnt (hM : D.M = -1) (hT : 0 < T) (hN : 1 ≤ N) (hβ : 0 < D.invβ) {cV CV : ℝ} (hcV : 0 < cV)
    (hV : ∀ x, cV * ‖x‖ ^ 2 - CV ≤ D.V x) (Kf : ℝ → ℝ) (hKi : IntegrableOn Kf (Set.Icc 0 T))
    (hLip : ∀ t ∈ Set.Icc (0 : ℝ) T, Whole.HasLipBoundW (Whole.mfeTransportW D (ρ t)) (Kf t))
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {Pm : Measure Ω} [IsProbabilityMeasure Pm]
    {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ} {W : ℝ≥0 → Ω → (Fin N → Euc d)}
    {X₀ : Ω → Whole.EucConfig d N} {X : ℝ≥0 → Ω → Whole.EucConfig d N}
    (hX : Whole.IsWholeStrongSolution Pm D T X₀ W X) (hF : Whole.IsWholeFilteredSolution Pm ℱ W' W X)
    (hX₀ : Measurable X₀)
    (hν0 : relEntropy (Pm.map X₀) (Measure.pi fun _ : Fin N => Whole.withDensityReal (ρ 0)) ≠ ⊤)
    (hEn0 : Integrable (sb1En (Whole.rieszKernel d D.s) (ρ 0) : Whole.EucConfig d N → ℝ) (Pm.map X₀))
    (hmom : ∫⁻ x, ENNReal.ofReal (‖x‖ ^ 2) ∂(Pm.map X₀) < ⊤)
    (c0 : ℝ) (hc0 : 0 ≤ c0)
    (hbdd : Pm.map X₀ ≤ ENNReal.ofReal c0 • sb1Dm (fun Z => sb1Gw D (Whole.rieszKernel d D.s) N Z))
    (η : ℕ → ℝ) (A3 A4 : ℝ) (hη : Tendsto η atTop (𝓝 0)) (hη0 : ∀ M, 0 ≤ η M) (hA3 : 0 < A3) (hA4 : 0 ≤ A4)
    (hBmeas : ∀ (M : ℕ) (r : ℝ), Measurable (sb1_lv_B (N := N) D (sb1kM d D.s M) hT.le ρ r))
    (hB : ∀ (M : ℕ), ∀ r ∈ Set.Icc (0 : ℝ) T, ∀ Z : Whole.EucConfig d N,
      |sb1_lv_B (N := N) D (sb1kM d D.s M) hT.le ρ r Z| ≤ η M * (1 + Kf r) *
        (A3 * (sb1PM (sb1kM d D.s M) N Z + sb1ell d N Z) + A4))
    (hTM : ∀ M : ℕ, AEStronglyMeasurable (fun s => ∫ y, (-(D.invβ⁻¹ * N) *
        (sb1_lv_Ck D (sb1kM d D.s M) N ρ s y - sb1_lv_EQ D (sb1kM d D.s M) N ρ s) +
        sb1_lv_B (N := N) D (sb1kM d D.s M) hT.le ρ s y)
        ∂(sb1Flow D (sb1kM d D.s M) N (Pm.map (X 0))
          (Pm.map (bfPath (p4r_shiftFil_brownian hF.brownian))) s)) (volume.restrict (Set.Icc 0 T))) :
    SbMovEnt D N T ρ Pm X₀ X := by
  intro _
  obtain ⟨hc1, hc2, hmain⟩ := sb1_bdd_entropy H hM hT hN hβ hcV hV Kf hKi hLip hX hF hX₀ hν0 hEn0 hmom c0 hc0 hbdd
    η A3 A4 hη hη0 hA3 hA4 hBmeas hB hTM
  refine ⟨fun t ht => ?_, fun r hr => ?_⟩
  · obtain ⟨hfin, hle⟩ := hmain t ht
    have hsub : Set.Icc (0 : ℝ) t ⊆ Set.Icc 0 T := Set.Icc_subset_Icc le_rfl ht.2
    exact ⟨hfin, fun r hr => hc1 r (hsub hr), hc2.mono_set hsub, hle⟩
  · obtain ⟨hK0, hL0⟩ := sb1_lip_of_hasLip (hLip r hr)
    exact sb1_CN_Qint H hN hβ hr hK0 hL0

end Main

end HRS.MS.MfeConf
