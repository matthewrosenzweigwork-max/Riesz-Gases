import HRS.MS.SA12V3B

/-!
# S.A.12 N1/N2 (SA12V3 worker), part C: bounded period `1 ≤ L ≤ Lmax`

`γ_L = L^{-s} g₁(·/L)` a.e., `g₁` locally integrable: `∫_{B(0,r')} |γ_L| ≤ L^d ∫_{B(0,r')} |g₁|`, hence
`|∫ γ_L(x-u) φ(u) du| ≤ C B` uniformly for `x` in the centred box.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff Pointwise

namespace HRS.MH.AdjointRd.Phase2SA12V3

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MH.AdjointRd
  HRS.MH.AdjointRd.Phase2SA12Construction

variable {d : ℕ}

theorem sa12v3_lattice_null (hd : 1 ≤ d) (L : ℝ) :
    volume {z : Euc d | ∃ k : Fin d → ℤ, z = L • latticePt k} = 0 := by
  haveI : NeZero d := ⟨by omega⟩
  have : {z : Euc d | ∃ k : Fin d → ℤ, z = L • latticePt k} = Set.range (fun k : Fin d → ℤ => L • latticePt k) := by
    ext z; simp [eq_comm]
  rw [this]
  exact (Set.countable_range _).measure_zero _

theorem sa12v3_gam_ae (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {L : ℝ} (hL : 0 < L)
    {γ : Euc d → ℝ} (hγ : IsPeriodicRieszKernel d s L γ) :
    ∀ᵐ z ∂(volume : Measure (Euc d)), γ z = HRS.MS.Ker1.ker1_gam d s L z := by
  rw [ae_iff]
  refine measure_mono_null (fun z hz => ?_) (sa12v3_lattice_null hd L)
  by_contra hne
  apply hz
  exact HRS.MS.Ker1.ker1_eq_gam hd hs0 hsd hL hγ z (fun k hk => hne ⟨k, hk⟩)

theorem sa12v3_g1_locInt (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) :
    LocallyIntegrable (HRS.MS.Ker1.ker1_g1 d s) volume := by
  have h := HRS.MS.Ker1.ker1_gam_locInt hd hs0 hsd (L := 1) one_pos
  have e : HRS.MS.Ker1.ker1_gam d s 1 = HRS.MS.Ker1.ker1_g1 d s := by
    funext z; simp [HRS.MS.Ker1.ker1_gam]
  rwa [e] at h

theorem sa12v3_gam_ball_integral (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {L : ℝ} (hL : 1 ≤ L)
    (r' : ℝ) (hr' : 0 ≤ r') :
    ∫ z in Metric.closedBall (0 : Euc d) r', |HRS.MS.Ker1.ker1_gam d s L z| ≤
      L ^ d * ∫ z in Metric.closedBall (0 : Euc d) r', |HRS.MS.Ker1.ker1_g1 d s z| := by
  have hL0 : 0 < L := lt_of_lt_of_le one_pos hL
  have hg1 : IntegrableOn (fun z => |HRS.MS.Ker1.ker1_g1 d s z|) (Metric.closedBall (0 : Euc d) r') volume :=
    ((sa12v3_g1_locInt hd hs0 hsd).integrableOn_isCompact (isCompact_closedBall _ _)).norm
  have e1 : ∀ z : Euc d, |HRS.MS.Ker1.ker1_gam d s L z| = L ^ (-s) * |HRS.MS.Ker1.ker1_g1 d s (L⁻¹ • z)| := by
    intro z
    simp only [HRS.MS.Ker1.ker1_gam, abs_mul]
    rw [abs_of_pos (Real.rpow_pos_of_pos hL0 _)]
  simp_rw [e1]
  rw [integral_const_mul]
  have h2 := Measure.setIntegral_comp_smul_of_pos (volume : Measure (Euc d))
    (fun y => |HRS.MS.Ker1.ker1_g1 d s y|) (R := L⁻¹) (Metric.closedBall (0 : Euc d) r') (inv_pos.2 hL0)
  rw [h2]
  have h3 : L⁻¹ • Metric.closedBall (0 : Euc d) r' = Metric.closedBall 0 (L⁻¹ * r') := by
    rw [smul_closedBall _ _ hr', smul_zero, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hL0)]
  rw [h3]
  have h4 : ∫ z in Metric.closedBall (0 : Euc d) (L⁻¹ * r'), |HRS.MS.Ker1.ker1_g1 d s z| ≤
      ∫ z in Metric.closedBall (0 : Euc d) r', |HRS.MS.Ker1.ker1_g1 d s z| := by
    refine setIntegral_mono_set hg1 (Eventually.of_forall fun z => abs_nonneg _) (Eventually.of_forall ?_)
    refine Metric.closedBall_subset_closedBall ?_
    exact mul_le_of_le_one_left hr' (inv_le_one_of_one_le₀ hL)
  have h5 : 0 ≤ ∫ z in Metric.closedBall (0 : Euc d) (L⁻¹ * r'), |HRS.MS.Ker1.ker1_g1 d s z| :=
    setIntegral_nonneg Metric.isClosed_closedBall.measurableSet (fun z _ => abs_nonneg _)
  rw [finrank_euclideanSpace_fin, smul_eq_mul, inv_pow, inv_inv]
  have h6 : L ^ (-s) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hL (by linarith)
  have h7 : 0 ≤ L ^ (-s) := Real.rpow_nonneg hL0.le _
  calc L ^ (-s) * (L ^ d * ∫ z in Metric.closedBall (0 : Euc d) (L⁻¹ * r'), |HRS.MS.Ker1.ker1_g1 d s z|)
      ≤ 1 * (L ^ d * ∫ z in Metric.closedBall (0 : Euc d) r', |HRS.MS.Ker1.ker1_g1 d s z|) := by
        refine mul_le_mul h6 (mul_le_mul_of_nonneg_left h4 (by positivity)) (by positivity) zero_le_one
    _ = _ := one_mul _

theorem sa12v3_box_norm {L : ℝ} {x : Euc d} (hx : x ∈ centeredBox d L) :
    ‖x‖ ≤ Real.sqrt (d * (L / 2) ^ 2) := by
  rw [EuclideanSpace.norm_eq]
  refine Real.sqrt_le_sqrt ?_
  calc ∑ i, ‖x i‖ ^ 2 ≤ ∑ _i : Fin d, (L / 2) ^ 2 := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [Real.norm_eq_abs]
        have h := hx i
        exact pow_le_pow_left₀ (abs_nonneg _) (abs_le.2 ⟨h.1, h.2.le⟩) 2
    _ = d * (L / 2) ^ 2 := by simp

/-- Bounded period range. -/
theorem sa12v3_bounded (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (Lmax R : ℝ) (hLm : 1 ≤ Lmax)
    (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ L : ℝ, 1 ≤ L → L ≤ Lmax → ∀ γ : Euc d → ℝ, IsPeriodicRieszKernel d s L γ →
      ∀ B : ℝ, ∀ φ : Euc d → ℝ, sa12v3_Test R B φ → ∀ x : Euc d, x ∈ centeredBox d L →
        |∫ u, γ (x - u) * φ u| ≤ C * B := by
  set r0 : ℝ := Real.sqrt (d * (Lmax / 2) ^ 2) with hr0
  set r' : ℝ := R + r0 with hr'
  have hr'0 : 0 ≤ r' := add_nonneg hR (Real.sqrt_nonneg _)
  set J : ℝ := ∫ z in Metric.closedBall (0 : Euc d) r', |HRS.MS.Ker1.ker1_g1 d s z| with hJ
  have hJ0 : 0 ≤ J := setIntegral_nonneg Metric.isClosed_closedBall.measurableSet (fun z _ => abs_nonneg _)
  have hLm0 : 0 ≤ Lmax := by linarith
  refine ⟨Lmax ^ d * J, by positivity, ?_⟩
  intro L hL hLL γ hγ B φ hT x hx
  have hL0 : 0 < L := lt_of_lt_of_le one_pos hL
  have hxn : ‖x‖ ≤ r0 := by
    refine (sa12v3_box_norm hx).trans (Real.sqrt_le_sqrt ?_)
    have : (L / 2) ^ 2 ≤ (Lmax / 2) ^ 2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
    exact mul_le_mul_of_nonneg_left this (Nat.cast_nonneg d)
  have hγi : IntegrableOn (fun z => |γ z|) (Metric.closedBall (0 : Euc d) r') volume :=
    (hγ.locInt.integrableOn_isCompact (isCompact_closedBall _ _)).norm
  have key := sa12v3_conv_le hγ.locInt hT x 0 (r' := r') (fun u hu => by
      rw [Metric.mem_closedBall, dist_zero_right]
      calc ‖x - u‖ ≤ ‖x‖ + ‖u‖ := norm_sub_le _ _
        _ ≤ r0 + R := add_le_add hxn hu
        _ = r' := by rw [hr']; ring) 0 (fun z => |γ z|) (fun _ => abs_nonneg _) hγi
    (Eventually.of_forall fun z _ => by simp)
  have h1 : ∫ z in Metric.closedBall (0 : Euc d) r', |γ z| =
      ∫ z in Metric.closedBall (0 : Euc d) r', |HRS.MS.Ker1.ker1_gam d s L z| := by
    refine setIntegral_congr_ae Metric.isClosed_closedBall.measurableSet ?_
    filter_upwards [sa12v3_gam_ae hd hs0 hsd hL0 hγ] with z hz _
    rw [hz]
  have h2 := sa12v3_gam_ball_integral hd hs0 hsd hL r' hr'0
  have h3 : L ^ d * J ≤ Lmax ^ d * J := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hL0.le hLL d) hJ0
  have hB := hT.B_nonneg
  calc |∫ u, γ (x - u) * φ u| ≤ B * ∫ z in Metric.closedBall (0 : Euc d) r', |γ z| := key
    _ ≤ B * (Lmax ^ d * J) := by
        refine mul_le_mul_of_nonneg_left ?_ hB
        rw [h1]; exact h2.trans h3
    _ = _ := by ring

end HRS.MH.AdjointRd.Phase2SA12V3
