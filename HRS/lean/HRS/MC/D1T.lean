import HRS.MC.D1TAux6

/-!
# Packet D1T: Lemma D.1, torus clause for `0 < s < d`

For a profile `ψ` and `b > 0` realising the Euclidean representation, the pointwise torus representation
`g(x) = b ∫_0^∞ t^{d-s} (Pφ_t(x) - ∫φ) dt/t` (with absolute convergence) holds for `x ≠ 0`
(`d1t_pos`).  Route: Fourier-side representation of the coefficients (`D1F.d1f_pos`), Fubini against the
heat factor (`d1t_heat_eq`), uniform domination of the damped series (`d1t_G_bound`, using the
uniform theta bound) and dominated convergence as `ε ↓ 0`.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal BigOperators

namespace HRS.MC.D1T

open HRS

variable {d : ℕ}

theorem d1t_dom_integrable {s : ℝ} (hs : 0 < s) (hsd : s < d) {δ0 : ℝ} (hδ0 : 0 < δ0) (M K : ℝ) :
    IntegrableOn (fun t : ℝ => t ^ ((d : ℝ) - s - 1) *
      (if t ≤ δ0 then M else K * (t ^ (2 * (d + 1)))⁻¹)) (Ioi 0) := by
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  rw [← Ioc_union_Ioi_eq_Ioi hδ0.le]
  refine IntegrableOn.union ?_ ?_
  · have h1 : IntegrableOn (fun t : ℝ => t ^ ((d : ℝ) - s - 1) * M) (Ioc 0 δ0) :=
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le hδ0.le).mp
        (intervalIntegral.intervalIntegrable_rpow' (by linarith))).mul_const M
    exact h1.congr_fun (fun t ht => by simp [ht.2]) measurableSet_Ioc
  · have h1 : IntegrableOn
        (fun t : ℝ => K * t ^ ((d : ℝ) - s - 1 - ((2 * (d + 1) : ℕ) : ℝ))) (Ioi δ0) :=
      (integrableOn_Ioi_rpow_of_lt (by push_cast; linarith) hδ0).const_mul K
    refine h1.congr_fun (fun t ht => ?_) measurableSet_Ioi
    have ht' : 0 < t := lt_trans hδ0 ht
    have ht2 : ¬ t ≤ δ0 := not_le.mpr ht
    simp only [ht2, if_false]
    rw [Real.rpow_sub ht', Real.rpow_natCast, div_eq_mul_inv]
    ring

theorem d1t_pos (hd : 1 ≤ d) {s : ℝ} (hs : 0 < s) (hsd : s < d) {ψ : Euc d → ℝ}
    (hψ : IsFDLProfile ψ) {b : ℝ} (hb0 : 0 < b)
    (hb : ∀ x : Euc d, x ≠ 0 → Whole.rieszKernel d s x =
        b * ∫ t in Set.Ioi (0 : ℝ), t ^ ((d : ℝ) - s) * fdlPhiScale ψ t x / t) :
    ∀ x : Torus d, x ≠ 0 →
      IntegrableOn (fun t : ℝ =>
        t ^ ((d : ℝ) - s) * (fdlPer (fdlPhiScale ψ t) x - ∫ y, fdlPhi ψ y) / t) (Set.Ioi 0) ∧
      periodicRiesz d s x = b * ∫ t in Set.Ioi (0 : ℝ),
        t ^ ((d : ℝ) - s) * (fdlPer (fdlPhiScale ψ t) x - ∫ y, fdlPhi ψ y) / t := by
  intro x hx
  obtain ⟨δ0, hδ0, M, K, hK0, hbd⟩ := d1t_G_bound hψ x hx
  set D : ℝ → ℝ := fun t => if t ≤ δ0 then M else K * (t ^ (2 * (d + 1)))⁻¹ with hD
  set Bnd : ℝ → ℝ := fun t => t ^ ((d : ℝ) - s - 1) * D t with hBnd
  have hBint : IntegrableOn Bnd (Ioi 0) := d1t_dom_integrable hs hsd hδ0 M K
  -- the integrands
  set Fe : ℝ → ℝ → ℝ := fun ε t => t ^ ((d : ℝ) - s) * d1tG ψ x ε t / t with hFe
  set Fq : ℝ → ℝ := fun t =>
    t ^ ((d : ℝ) - s) * (fdlPer (fdlPhiScale ψ t) x - ∫ y, fdlPhi ψ y) / t with hFq
  have hrpow : ∀ t : ℝ, 0 < t → t ^ ((d : ℝ) - s) / t = t ^ ((d : ℝ) - s - 1) := by
    intro t ht
    rw [Real.rpow_sub_one ht.ne']
  have hmeas : ∀ ε : ℝ, 0 < ε → AEStronglyMeasurable (Fe ε) (volume.restrict (Ioi 0)) := by
    intro ε hε
    exact (((measurable_id.pow_const _).mul (d1tG_continuous hψ hε x).measurable).div
      measurable_id).aestronglyMeasurable
  have hbound : ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ t ∈ Ioi (0 : ℝ), ‖Fe ε t‖ ≤ Bnd t := by
    intro ε hε hε1 t ht
    have ht' : 0 < t := ht
    have h1 : Fe ε t = t ^ ((d : ℝ) - s - 1) * d1tG ψ x ε t := by
      simp only [hFe]; rw [← hrpow t ht']; ring
    rw [h1, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos ht' _)]
    exact mul_le_mul_of_nonneg_left (hbd ε hε hε1 t ht') (Real.rpow_pos_of_pos ht' _).le
  have hlim : ∀ t ∈ Ioi (0 : ℝ), Tendsto (fun ε => Fe ε t) (𝓝[>] 0) (𝓝 (Fq t)) := by
    intro t ht
    have ht' : 0 < t := ht
    have := ((d1tG_tendsto hd hψ ht' x).const_mul (t ^ ((d : ℝ) - s))).div_const t
    exact this
  -- dominated convergence
  have hDCT : Tendsto (fun ε => ∫ t in Ioi (0 : ℝ), Fe ε t) (𝓝[>] 0)
      (𝓝 (∫ t in Ioi (0 : ℝ), Fq t)) := by
    refine tendsto_integral_filter_of_dominated_convergence Bnd ?_ ?_ hBint ?_
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      exact hmeas ε hε
    · filter_upwards [Ioc_mem_nhdsGT one_pos] with ε hε
      exact ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => hbound ε hε.1 hε.2 t ht
    · exact ae_restrict_of_forall_mem measurableSet_Ioi hlim
  -- identification of the limit
  have hheat : Tendsto (fun ε => heatRiesz d s ε x) (𝓝[>] 0)
      (𝓝 (b * ∫ t in Ioi (0 : ℝ), Fq t)) := by
    refine (hDCT.const_mul b).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact (d1t_heat_eq hd hs hsd hψ hb0 hb hε x).symm
  refine ⟨?_, ?_⟩
  · -- integrability of the limit integrand
    have hseq : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝[>] 0) :=
      tendsto_nhdsWithin_iff.mpr ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
        Eventually.of_forall fun n => Set.mem_Ioi.mpr (by positivity)⟩
    have hmeasq : AEStronglyMeasurable Fq (volume.restrict (Ioi 0)) := by
      refine aestronglyMeasurable_of_tendsto_ae (u := atTop)
        (f := fun n : ℕ => Fe (1 / ((n : ℝ) + 1))) (fun n => hmeas _ (by positivity)) ?_
      exact ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => (hlim t ht).comp hseq
    refine Integrable.mono' hBint hmeasq ?_
    refine ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_
    refine le_of_tendsto (tendsto_norm.comp (hlim t ht)) ?_
    filter_upwards [Ioc_mem_nhdsGT one_pos] with ε hε
    exact hbound ε hε.1 hε.2 t ht
  · exact hheat.limUnder_eq

end HRS.MC.D1T
