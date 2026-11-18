import HRS.MS.R26T8AP11g1

/-!
# S8.2 T8A P11g (part 2): `r26t8a_g2_ibp`
For `R26P10Hyp d y τ h` and a bounded `C^1` `Γ` with bounded gradient:
`∫ Γ div h = - ∫ ∑_j ∂_jΓ h_j`, both integrands integrable.  (Cut-off `δ → 0`, copy of `r26t8a_p10a_eps_ibp`.)
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82

variable {d : ℕ}

set_option maxHeartbeats 3200000 in
theorem r26t8a_g2_ibp {y : Euc d} {τ : ℝ} {h : Euc d → Euc d} (H : R26P10Hyp d y τ h)
    {Γ : Euc d → ℝ} (hΓ : ContDiff ℝ 1 Γ) {B0 B1 : ℝ} (hB0 : ∀ u, |Γ u| ≤ B0)
    (hB1 : ∀ u, ‖fderiv ℝ Γ u‖ ≤ B1) :
    Integrable (fun u => Γ u * r26t8a_divh h u) ∧
    Integrable (fun u => ∑ j : Fin d, fderiv ℝ Γ u (EuclideanSpace.single j 1) * h u j) ∧
    ∫ u, Γ u * r26t8a_divh h u = -∫ u, ∑ j : Fin d, fderiv ℝ Γ u (EuclideanSpace.single j 1) * h u j := by
  have hd := H.hd
  have hτ0 := H.τ0
  have hτd : τ + 1 < (d : ℝ) := H.τd
  haveI : Nontrivial (Euc d) := by
    apply Module.nontrivial_of_finrank_pos (R := ℝ)
    simp; omega
  obtain ⟨chi, hchi⟩ := r26t8a_p10a_exists_cutoff d
  obtain ⟨Cχ, hCχ0, hCχ⟩ := r26t8a_cut_fderiv_bound hchi (d := d)
  have hGc : Continuous Γ := hΓ.continuous
  have hB00 : 0 ≤ B0 := (abs_nonneg _).trans (hB0 0)
  have hB10 : 0 ≤ B1 := (norm_nonneg _).trans (hB1 0)
  obtain ⟨C, c, hC0, hc, hh⟩ := H.hb
  have hDΓ : ∀ (u : Euc d) (j : Fin d), |fderiv ℝ Γ u (EuclideanSpace.single j 1)| ≤ B1 := by
    intro u j
    rw [← Real.norm_eq_abs]
    calc ‖fderiv ℝ Γ u (EuclideanSpace.single j 1)‖
        ≤ ‖fderiv ℝ Γ u‖ * ‖(EuclideanSpace.single j (1 : ℝ) : Euc d)‖ := (fderiv ℝ Γ u).le_opNorm _
      _ ≤ B1 := by rw [r26t8a_norm_single, mul_one]; exact hB1 u
  have gdiv : R26P10GP y (τ + 1) (fun u => Γ u * r26t8a_divh h u) :=
    r26t8a_p10a_gp_of_bound (B := B0 * d) H.hdb (by positivity) (fun u _ => by
      rw [abs_mul, abs_of_nonneg (norm_nonneg _)]
      calc |Γ u| * |r26t8a_divh h u| ≤ B0 * (d * ‖fderiv ℝ h u‖) :=
            mul_le_mul (hB0 u) (r26t8a_divh_le h u) (abs_nonneg _) hB00
        _ = _ := by ring)
  have F1int : Integrable (fun u => Γ u * r26t8a_divh h u) := by
    refine r26t8a_p10a_gp_integrable (y := y) (τ := τ + 1) hd (by linarith) (by linarith) gdiv ?_
    exact r26t8a_p10a_aesm hd y (hGc.continuousOn.mul (r26t8a_divh_continuousOn H.C1))
  have dΓc : ∀ j : Fin d, Continuous fun u : Euc d => fderiv ℝ Γ u (EuclideanSpace.single j 1) :=
    fun j => (hΓ.continuous_fderiv (by simp)).clm_apply continuous_const
  have gF2 : R26P10GP y τ (fun u => ∑ j : Fin d, fderiv ℝ Γ u (EuclideanSpace.single j 1) * h u j) :=
    r26t8a_p10a_gp_of_bound (B := B1 * d) H.hb (by positivity) (fun u _ => by
      rw [abs_of_nonneg (norm_nonneg _)]
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      calc ∑ j : Fin d, |fderiv ℝ Γ u (EuclideanSpace.single j 1) * h u j|
          ≤ ∑ j : Fin d, B1 * ‖h u‖ := by
            refine Finset.sum_le_sum fun j _ => ?_
            rw [abs_mul]
            exact mul_le_mul (hDΓ u j) (r26t8a_abs_coord_le _ _) (abs_nonneg _) hB10
        _ = _ := by simp; ring)
  have F2meas : AEStronglyMeasurable
      (fun u => ∑ j : Fin d, fderiv ℝ Γ u (EuclideanSpace.single j 1) * h u j) volume := by
    refine r26t8a_p10a_aesm hd y ?_
    refine continuousOn_finset_sum _ fun j _ => ?_
    have hj : Continuous fun v : Euc d => v j := (EuclideanSpace.proj j).continuous
    exact (dΓc j).continuousOn.mul (hj.comp_continuousOn H.C1.continuousOn)
  have F2int := r26t8a_p10a_gp_integrable (y := y) (τ := τ) hd hτ0 (by linarith) gF2 F2meas
  have hid : ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 2 →
      (∫ u, r26t8a_cut chi y δ u * (Γ u * r26t8a_divh h u)) +
        (∫ u, Γ u * ∑ j : Fin d,
          fderiv ℝ (r26t8a_cut chi y δ) u (EuclideanSpace.single j 1) * h u j) =
      -∫ u, r26t8a_cut chi y δ u * (∑ j : Fin d, fderiv ℝ Γ u (EuclideanSpace.single j 1) * h u j) := by
    intro δ hδ hδ2
    have hj := fun j : Fin d => r26t8a_g1_ibp_j hchi H hΓ hB0 hB1 hδ (hCχ y hδ) j
    have hsum1 : ∫ u, ∑ j : Fin d, Γ u * r26t8a_Dj chi y δ h j u =
        ∑ j : Fin d, ∫ u, Γ u * r26t8a_Dj chi y δ h j u :=
      integral_finset_sum _ fun j _ => (hj j).1
    have hsum2 : ∫ u, ∑ j : Fin d, fderiv ℝ Γ u (EuclideanSpace.single j 1) * r26t8a_Hj chi y δ h j u =
        ∑ j : Fin d, ∫ u, fderiv ℝ Γ u (EuclideanSpace.single j 1) * r26t8a_Hj chi y δ h j u :=
      integral_finset_sum _ fun j _ => (hj j).2.1
    have hcut : ∀ u, r26t8a_cut chi y δ u * (∑ j : Fin d, fderiv ℝ Γ u (EuclideanSpace.single j 1) * h u j) =
        ∑ j : Fin d, fderiv ℝ Γ u (EuclideanSpace.single j 1) * r26t8a_Hj chi y δ h j u := by
      intro u
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [r26t8a_Hj]; ring
    have hpt : ∀ u, ∑ j : Fin d, Γ u * r26t8a_Dj chi y δ h j u =
        r26t8a_cut chi y δ u * (Γ u * r26t8a_divh h u) +
          Γ u * ∑ j : Fin d,
            fderiv ℝ (r26t8a_cut chi y δ) u (EuclideanSpace.single j 1) * h u j := by
      intro u
      simp only [r26t8a_Dj, r26t8a_divh, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    have hI1 : Integrable (fun u => ∑ j : Fin d, Γ u * r26t8a_Dj chi y δ h j u) :=
      integrable_finset_sum _ fun j _ => (hj j).1
    have hI2 : Integrable (fun u => r26t8a_cut chi y δ u * (Γ u * r26t8a_divh h u)) := by
      refine Integrable.mono' F1int.norm
        (((r26t8a_cut_contDiff hchi y δ).continuous.aestronglyMeasurable).mul F1int.aestronglyMeasurable)
        (Filter.Eventually.of_forall fun u => ?_)
      have := r26t8a_cut_mem hchi y δ u
      rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg this.1]
      exact mul_le_of_le_one_left (norm_nonneg _) this.2
    have hI3 : Integrable (fun u => Γ u * ∑ j : Fin d,
        fderiv ℝ (r26t8a_cut chi y δ) u (EuclideanSpace.single j 1) * h u j) := by
      have := hI1.sub hI2
      refine this.congr (Filter.Eventually.of_forall fun u => ?_)
      simp only [Pi.sub_apply, hpt u]; ring
    have e1 := integral_add hI2 hI3
    have e2 : ∫ u, (∑ j : Fin d, Γ u * r26t8a_Dj chi y δ h j u) =
        ∫ u, (r26t8a_cut chi y δ u * (Γ u * r26t8a_divh h u) +
          Γ u * ∑ j : Fin d,
            fderiv ℝ (r26t8a_cut chi y δ) u (EuclideanSpace.single j 1) * h u j) := by
      congr 1; funext u; exact hpt u
    rw [← e1, ← e2, hsum1]
    calc ∑ j : Fin d, ∫ u, Γ u * r26t8a_Dj chi y δ h j u
        = ∑ j : Fin d, -∫ u, fderiv ℝ Γ u (EuclideanSpace.single j 1) * r26t8a_Hj chi y δ h j u :=
          Finset.sum_congr rfl fun j _ => (hj j).2.2
      _ = -∑ j : Fin d, ∫ u, fderiv ℝ Γ u (EuclideanSpace.single j 1) * r26t8a_Hj chi y δ h j u := by
          rw [Finset.sum_neg_distrib]
      _ = -∫ u, ∑ j : Fin d, fderiv ℝ Γ u (EuclideanSpace.single j 1) * r26t8a_Hj chi y δ h j u := by
          rw [hsum2]
      _ = _ := by congr 1; congr 1; funext u; exact (hcut u).symm
  have t1 := r26t8a_cut_tendsto hd hchi y F1int
  have t3 := r26t8a_cut_tendsto hd hchi y F2int
  have t2 : Tendsto (fun δ : ℝ => ∫ u, Γ u * ∑ j : Fin d,
      fderiv ℝ (r26t8a_cut chi y δ) u (EuclideanSpace.single j 1) * h u j) (𝓝[>] 0) (𝓝 0) := by
    refine r26t8a_p10a_cut_term (y := y) (τ := τ) hd hτ0 (by linarith)
      (K := B0 * d * Cχ * (2 * C)) _ (by positivity) ?_
    intro δ hδ hδ2 u
    by_cases h2 : ‖u - y‖ ≤ 2 * δ
    · rw [if_pos h2]
      by_cases hu : u = y
      · have hz : fderiv ℝ (r26t8a_cut chi y δ) u = 0 :=
          r26t8a_cut_fderiv_zero_lt hchi y hδ (by rw [hu]; simpa using hδ)
        subst hu
        simp [hz]
        positivity
      · have hn : 0 < ‖u - y‖ := norm_pos_iff.2 (sub_ne_zero.2 hu)
        have hn1 : ‖u - y‖ ≤ 1 := by linarith
        have hp : 1 ≤ ‖u - y‖ ^ (-τ) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hn hn1 (by linarith)
        have hh' := hh u hu
        have hE : Real.exp (-c * ‖u‖ ^ 2) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg ‖u‖])
        have hhu : ‖h u‖ ≤ 2 * C * ‖u - y‖ ^ (-τ) := by
          rw [abs_of_nonneg (norm_nonneg _)] at hh'
          refine hh'.trans ?_
          have := mul_le_mul_of_nonneg_left hE hC0
          nlinarith
        have hcoord : ∀ j : Fin d, |fderiv ℝ (r26t8a_cut chi y δ) u (EuclideanSpace.single j 1)| ≤ Cχ / δ := by
          intro j
          rw [← Real.norm_eq_abs]
          calc ‖fderiv ℝ (r26t8a_cut chi y δ) u (EuclideanSpace.single j 1)‖
              ≤ ‖fderiv ℝ (r26t8a_cut chi y δ) u‖ * ‖(EuclideanSpace.single j (1 : ℝ) : Euc d)‖ :=
                (fderiv ℝ (r26t8a_cut chi y δ) u).le_opNorm _
            _ ≤ Cχ / δ := by rw [r26t8a_norm_single, mul_one]; exact hCχ y hδ u
        rw [Real.norm_eq_abs, abs_mul]
        have hs1 : |∑ j : Fin d, fderiv ℝ (r26t8a_cut chi y δ) u (EuclideanSpace.single j 1) * h u j|
            ≤ d * (Cχ / δ * ‖h u‖) := by
          refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
          calc ∑ j : Fin d, |fderiv ℝ (r26t8a_cut chi y δ) u (EuclideanSpace.single j 1) * h u j|
              ≤ ∑ j : Fin d, Cχ / δ * ‖h u‖ := by
                refine Finset.sum_le_sum fun j _ => ?_
                rw [abs_mul]
                exact mul_le_mul (hcoord j) (r26t8a_abs_coord_le _ _) (abs_nonneg _)
                  ((norm_nonneg _).trans (hCχ y hδ 0))
            _ = _ := by simp
        calc |Γ u| * |∑ j : Fin d, fderiv ℝ (r26t8a_cut chi y δ) u (EuclideanSpace.single j 1) * h u j|
            ≤ B0 * (d * (Cχ / δ * ‖h u‖)) :=
              mul_le_mul (hB0 u) hs1 (abs_nonneg _) hB00
          _ ≤ B0 * (d * (Cχ / δ * (2 * C * ‖u - y‖ ^ (-τ)))) := by
              gcongr
          _ = _ := by field_simp
    · rw [if_neg h2]
      have hz : fderiv ℝ (r26t8a_cut chi y δ) u = 0 :=
        r26t8a_cut_fderiv_zero_gt hchi y hδ (by linarith [not_le.1 h2])
      simp [hz]
  have t4 := t1.add t2
  have t5 : Tendsto (fun δ : ℝ => -∫ u, r26t8a_cut chi y δ u *
        (∑ j : Fin d, fderiv ℝ Γ u (EuclideanSpace.single j 1) * h u j))
      (𝓝[>] 0) (𝓝 (∫ u, Γ u * r26t8a_divh h u)) := by
    rw [add_zero] at t4
    refine t4.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 2)] with δ hδ
    exact hid δ hδ.1 hδ.2.le
  have t6 := t3.neg
  have := tendsto_nhds_unique t5 t6
  exact ⟨F1int, F2int, this⟩

end HRS.MS.R26T8A
