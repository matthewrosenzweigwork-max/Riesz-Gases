import HRS.MS.MfeConfAux35

/-!
# S.B.1, packet F3 (part 17): `SbLogK` (the whole-space `movT_logK_integral`)

* `sb1Kpi k`, `sb1Phipi k`: `K_k(r) = ∫ F dμ_r^N`, `Φ_k(r) = ∫ F 𝖥_N^{h_k} dμ_r^N`;
* `sb1_Mlevel`: for a regular admissible kernel, `K_k(t) - K_k(0) = ∫_0^t βN Φ_k` (Part I: `sb1_hasDerivAt_K`, `sb1_dK_eq`);
* `sb1_logK_main`: **F3** `SbLogK D N T ρ` from `Sb1Tr3` and the Lipschitz hypothesis `HasLipBoundW (u_V^t) (K t)`,
  `K` integrable: smoothing `k_n = movtr_gEps(1/(n+1))`, `n → ∞` (one-time limits `sb1_K_tendsto`, `sb1_Phi_tendsto`),
  then the chain rule for absolutely continuous functions (`sb1_log_of_integral_eq`).
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MfeConf

variable {d N : ℕ}

/-- `K_k(r) = ∫ F dμ_r^N` -/
def sb1Kpi (k : Euc d → ℝ) (β : ℝ) (N : ℕ) (ρ : ℝ → Euc d → ℝ) (r : ℝ) : ℝ :=
  ∫ X : Whole.EucConfig d N, sb1FF k β N (ρ r) X ∂(Measure.pi fun _ : Fin N => Whole.withDensityReal (ρ r))

/-- `Φ_k(r) = ∫ F P dμ_r^N` -/
def sb1Phipi (k : Euc d → ℝ) (u : ℝ → Euc d → Euc d) (β : ℝ) (N : ℕ) (ρ : ℝ → Euc d → ℝ) (r : ℝ) : ℝ :=
  ∫ X : Whole.EucConfig d N, sb1FF k β N (ρ r) X * Whole.pairEnergy (sb1hk k (u r)) X (Whole.withDensityReal (ρ r))
    ∂(Measure.pi fun _ : Fin N => Whole.withDensityReal (ρ r))

section Main

variable {D : Whole.WholeDyn d} {T C B C3 : ℝ} {ρ : ℝ → Euc d → ℝ}

theorem sb1_Kpi_eq (H : Sb1Tr3 D T C B C3 ρ) {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) T) (k : Euc d → ℝ) (β : ℝ) :
    sb1Kpi k β N ρ r = ∫ X : Whole.EucConfig d N, sb1Wf k β N ρ r X := by
  unfold sb1Kpi sb1Wf
  rw [sb1_integral_pi (H.tr.slice r hr).dens]
  rfl

theorem sb1_Phipi_eq (H : Sb1Tr3 D T C B C3 ρ) {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) T) (k : Euc d → ℝ) (β : ℝ) :
    sb1Phipi k (fun r => Whole.mfeTransportW D (ρ r)) β N ρ r = ∫ X : Whole.EucConfig d N, sb1Wf k β N ρ r X *
      Whole.pairEnergy (fun x y => fderiv ℝ k (x - y) (Whole.mfeTransportW D (ρ r) x - Whole.mfeTransportW D (ρ r) y))
        X (Whole.withDensityReal (ρ r)) := by
  unfold sb1Phipi
  rw [sb1_integral_pi (H.tr.slice r hr).dens]
  refine integral_congr_ae (Eventually.of_forall fun X => ?_)
  show (∏ i, ρ r (X i)) * (Real.exp (-β * N * sb1En k (ρ r) X) *
      Whole.pairEnergy (fun x y => fderiv ℝ k (x - y) (Whole.mfeTransportW D (ρ r) x - Whole.mfeTransportW D (ρ r) y))
        X (Whole.withDensityReal (ρ r))) =
    ((∏ i, ρ r (X i)) * Real.exp (-β * N * sb1En k (ρ r) X)) *
      Whole.pairEnergy (fun x y => fderiv ℝ k (x - y) (Whole.mfeTransportW D (ρ r) x - Whole.mfeTransportW D (ρ r) y))
        X (Whole.withDensityReal (ρ r))
  ring

theorem sb1_hasDerivAt_Kpi (H : Sb1Tr3 D T C B C3 ρ) (hT : 0 ≤ T) {β : ℝ} (hβ : 0 ≤ β) (hN : 1 ≤ N)
    {k : Euc d → ℝ} {Lg : ℝ} (hk : Sb1KerU d D.s k) (hR : Sb1KerR d k Lg) {r : ℝ} (hr : r ∈ Set.Ioo (0 : ℝ) T) :
    HasDerivAt (fun r => sb1Kpi k β N ρ r)
      (β * N * sb1Phipi k (fun r => Whole.mfeTransportW D (ρ r)) β N ρ r) r := by
  have hIcc : r ∈ Set.Icc (0 : ℝ) T := ⟨hr.1.le, hr.2.le⟩
  have h1 := sb1_hasDerivAt_K H hT hk hR hβ hN hr
  rw [sb1_dK_eq H hk hR hIcc hβ hN, ← sb1_Phipi_eq H hIcc k β] at h1
  refine h1.congr_of_eventuallyEq ?_
  filter_upwards [Ioo_mem_nhds hr.1 hr.2] with r' hr'
  exact sb1_Kpi_eq H ⟨hr'.1.le, hr'.2.le⟩ k β

theorem sb1_Phipi_aesm (H : Sb1Tr3 D T C B C3 ρ) (hT : 0 ≤ T) {β : ℝ} (hβ : 0 < β) (hN : 1 ≤ N)
    {k : Euc d → ℝ} {Lg : ℝ} (hk : Sb1KerU d D.s k) (hR : Sb1KerR d k Lg) :
    AEStronglyMeasurable (fun r => sb1Phipi k (fun r => Whole.mfeTransportW D (ρ r)) β N ρ r)
      (volume.restrict (Set.Icc 0 T)) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hβN : 0 < β * N := mul_pos hβ hN0
  have hβN' : β * N ≠ 0 := hβN.ne'
  have h1 : AEStronglyMeasurable (fun r => (β * N)⁻¹ * deriv (sb1Kpi k β N ρ) r)
      (volume.restrict (Set.Ioo 0 T)) := ((measurable_deriv _).const_mul _).aestronglyMeasurable
  have h2 : AEStronglyMeasurable (fun r => sb1Phipi k (fun r => Whole.mfeTransportW D (ρ r)) β N ρ r)
      (volume.restrict (Set.Ioo 0 T)) := by
    refine h1.congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    rw [(sb1_hasDerivAt_Kpi H hT hβ.le hN hk hR hr).deriv]
    field_simp
  rwa [Measure.restrict_congr_set Ioo_ae_eq_Icc] at h2

theorem sb1_Mlevel (H : Sb1Tr3 D T C B C3 ρ) (hT : 0 ≤ T) {β : ℝ} (hβ : 0 < β) (hN : 1 ≤ N)
    {k : Euc d → ℝ} {Lg : ℝ} (hk : Sb1KerU d D.s k) (hR : Sb1KerR d k Lg) {Φb : ℝ → ℝ}
    (hΦb : IntegrableOn Φb (Set.Icc 0 T))
    (hbd : ∀ r ∈ Set.Icc (0 : ℝ) T, |sb1Phipi k (fun r => Whole.mfeTransportW D (ρ r)) β N ρ r| ≤ Φb r)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    sb1Kpi k β N ρ t - sb1Kpi k β N ρ 0 =
      ∫ r in (0 : ℝ)..t, β * N * sb1Phipi k (fun r => Whole.mfeTransportW D (ρ r)) β N ρ r := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hβN : 0 < β * N := mul_pos hβ hN0
  have hcont : ContinuousOn (sb1Kpi k β N ρ) (Set.Icc 0 T) :=
    (sb1_Kk_contOn H hk hβ.le hN).congr (fun r hr => sb1_Kpi_eq H hr k β)
  have hsub : Set.Icc (0 : ℝ) t ⊆ Set.Icc 0 T := Set.Icc_subset_Icc le_rfl ht.2
  have hint : IntervalIntegrable
      (fun r => β * N * sb1Phipi k (fun r => Whole.mfeTransportW D (ρ r)) β N ρ r) volume 0 t := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le ht.1]
    refine Integrable.mono' ((hΦb.mono_set (fun r hr => hsub ⟨hr.1.le, hr.2⟩)).const_mul (β * N)) ?_ ?_
    · exact ((sb1_Phipi_aesm H hT hβ hN hk hR).mono_set (fun r hr => hsub ⟨hr.1.le, hr.2⟩)).const_mul _
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hβN.le]
      exact mul_le_mul_of_nonneg_left (hbd r (hsub ⟨hr.1.le, hr.2⟩)) hβN.le
  have := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht.1 (hcont.mono hsub)
    (fun r hr => sb1_hasDerivAt_Kpi H hT hβ.le hN hk hR ⟨hr.1, hr.2.trans_le ht.2⟩) hint
  exact this.symm

/-! ### Bounds of the transport kernels -/

theorem sb1_lip_of_hasLip {u : Euc d → Euc d} {K : ℝ} (h : Whole.HasLipBoundW u K) :
    0 ≤ K ∧ ∀ x y, ‖u x - u y‖ ≤ K * ‖x - y‖ := by
  obtain ⟨L, hL, hLK⟩ := h
  have hK0 : 0 ≤ K := (L.coe_nonneg).trans hLK
  refine ⟨hK0, fun x y => ?_⟩
  have := hL.dist_le_mul x y
  rw [dist_eq_norm, dist_eq_norm] at this
  exact this.trans (mul_le_mul_of_nonneg_right hLK (norm_nonneg _))

theorem sb1_hk_bound {s : ℝ} (hs0 : 0 ≤ s) {k : Euc d → ℝ}
    (hg : ∀ z : Euc d, z ≠ 0 → ∀ e, |fderiv ℝ k z e| ≤ Whole.movtr_sigma s * ‖z‖ ^ (-s - 1) * ‖e‖)
    {u : Euc d → Euc d} {Kc : ℝ} (hKc : 0 ≤ Kc) (hu : ∀ x y, ‖u x - u y‖ ≤ Kc * ‖x - y‖) (x y : Euc d) :
    |sb1hk k u x y| ≤ Whole.movtr_sigma s * Kc * ‖x - y‖ ^ (-s) := by
  have hσ := sb1_sigma_nonneg hs0
  by_cases hxy : x = y
  · subst hxy
    simp only [sb1hk, sub_self, map_zero, abs_zero]
    exact mul_nonneg (mul_nonneg hσ hKc) (Real.rpow_nonneg (norm_nonneg _) _)
  · have hz : x - y ≠ 0 := sub_ne_zero.2 hxy
    have hzp : 0 < ‖x - y‖ := norm_pos_iff.2 hz
    unfold sb1hk
    refine (hg _ hz _).trans ?_
    have h3 : ‖x - y‖ ^ (-s - 1) * ‖x - y‖ = ‖x - y‖ ^ (-s) := by
      rw [← Real.rpow_add_one hzp.ne']; congr 1; ring
    calc Whole.movtr_sigma s * ‖x - y‖ ^ (-s - 1) * ‖u x - u y‖
        ≤ Whole.movtr_sigma s * ‖x - y‖ ^ (-s - 1) * (Kc * ‖x - y‖) :=
          mul_le_mul_of_nonneg_left (hu x y) (mul_nonneg hσ (Real.rpow_nonneg hzp.le _))
      _ = Whole.movtr_sigma s * Kc * ‖x - y‖ ^ (-s) := by rw [← h3]; ring

theorem sb1_commKernel_eq (s : ℝ) (v : Euc d → Euc d) :
    Whole.commutatorKernel d s v = sb1hk (Whole.rieszKernel d s) v := by
  funext x y
  unfold Whole.commutatorKernel sb1hk Whole.rieszKernelGrad gradient
  rw [real_inner_comm, InnerProductSpace.toDual_symm_apply]

end Main

end HRS.MS.MfeConf
