import HRS.MS.UniqN3aE

/-!
# N3a, part F: `m_q v̂ ∈ L²` for `v ∈ C²_c` (Fatou along an a.e.-convergent subsequence)
-/

noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff FourierTransform ComplexConjugate SchwartzMap LineDeriv

namespace HRS.MS.UniqN3a
open HRS HRS.Whole HRS.PDE.ToolboxRd HRS.PDE.ToolboxRd.FourierAux HRS.MS.UniqT2

variable {d : ℕ}

theorem Sn_sub_l2 {v : Euc d → ℝ} (hv : ContDiff ℝ 2 v) (hvc : HasCompactSupport v) {R : ℝ}
    (hsupp : Function.support v ⊆ closedBall 0 R) {η : ℝ} (hη : 0 < η) :
    ∃ N : ℕ, ∀ n, N ≤ n → ∫ x, (Sn n hv hvc x - v x) ^ 2 ≤ η ^ 2 * Vol d (R + 1) := by
  obtain ⟨N, hN⟩ := mo_unif hv.continuous hvc hη
  refine ⟨N, fun n hn => ?_⟩
  refine (l2_le (h := fun x => Sn n hv hvc x - v x) (R := R + 1) (M := η) ?_ ?_ ?_).2
  · exact ((mo_contDiff n hv.continuous).continuous).sub hv.continuous
  · intro x hx
    by_cases h1 : mo n v x = 0
    · have h2 : v x ≠ 0 := fun h2 => hx (by simp [Sn_apply, h1, h2])
      have := hsupp h2
      exact closedBall_subset_closedBall (by linarith) this
    · exact mo_supp n hsupp x h1
  · intro x; exact hN n hn x

theorem a_tendsto {v : Euc d → ℝ} (hv : ContDiff ℝ 2 v) (hvc : HasCompactSupport v) :
    Tendsto (fun n => ∫ ξ, ‖fourierL2 (Sn n hv hvc) ξ - fourierL2 v ξ‖ ^ 2) atTop (𝓝 0) := by
  obtain ⟨R1, hR1⟩ := hvc.isCompact.isBounded.subset_closedBall (0 : Euc d)
  have hsupp : Function.support v ⊆ closedBall (0 : Euc d) R1 := fun x hx => hR1 (subset_tsupport _ hx)
  have hmv : MemLp v 2 volume := hv.continuous.memLp_of_hasCompactSupport hvc
  have hms : ∀ n, MemLp (⇑(Sn n hv hvc)) 2 volume := fun n => (Sn n hv hvc).memLp 2 volume
  have heq : ∀ n, ∫ ξ, ‖fourierL2 (Sn n hv hvc) ξ - fourierL2 v ξ‖ ^ 2 =
      ∫ x, (Sn n hv hvc x - v x) ^ 2 := by
    intro n
    have hs := hms n
    have h1 := fourierL2_sub hs hmv
    have h2 : ∫ ξ, ‖fourierL2 (fun x => Sn n hv hvc x - v x) ξ‖ ^ 2 =
        ∫ x, (Sn n hv hvc x - v x) ^ 2 := integral_norm_sq_fourierL2 (hs.sub hmv)
    rw [← h2]
    refine integral_congr_ae ?_
    filter_upwards [h1] with ξ hξ
    rw [hξ]
  simp_rw [heq]
  rw [Metric.tendsto_atTop]
  intro ε hε
  set V := Vol d (R1 + 1) with hV
  have hV0 : 0 ≤ V := Vol_nonneg _
  set η : ℝ := Real.sqrt (ε / (2 * (V + 1))) with hη
  have hη0 : 0 < η := Real.sqrt_pos.2 (by positivity)
  obtain ⟨N, hN⟩ := Sn_sub_l2 hv hvc hsupp hη0
  refine ⟨N, fun n hn => ?_⟩
  have h1 := hN n hn
  have h2 : η ^ 2 = ε / (2 * (V + 1)) := Real.sq_sqrt (by positivity)
  have h3 : 0 ≤ ∫ x, (Sn n hv hvc x - v x) ^ 2 := integral_nonneg fun x => sq_nonneg _
  rw [Real.dist_eq, sub_zero, abs_of_nonneg h3]
  calc _ ≤ η ^ 2 * V := h1
    _ = ε / (2 * (V + 1)) * V := by rw [h2]
    _ < ε := by
        rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
        nlinarith

theorem a_eLpNorm_tendsto {v : Euc d → ℝ} (hv : ContDiff ℝ 2 v) (hvc : HasCompactSupport v) :
    Tendsto (fun n => eLpNorm (fun ξ => fourierL2 (Sn n hv hvc) ξ - fourierL2 v ξ) 2 volume)
      atTop (𝓝 0) := by
  have hmv : MemLp v 2 volume := hv.continuous.memLp_of_hasCompactSupport hvc
  have hmem : ∀ n, MemLp (fun ξ => fourierL2 (Sn n hv hvc) ξ - fourierL2 v ξ) 2 volume := fun n =>
    (memLp_fourierL2 ((Sn n hv hvc).memLp 2 volume)).sub (memLp_fourierL2 hmv)
  have heq : ∀ n, eLpNorm (fun ξ => fourierL2 (Sn n hv hvc) ξ - fourierL2 v ξ) 2 volume =
      ENNReal.ofReal ((∫ ξ, ‖fourierL2 (Sn n hv hvc) ξ - fourierL2 v ξ‖ ^ 2) ^ ((1 : ℝ) / 2)) := by
    intro n
    rw [(hmem n).eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
    simp [ENNReal.toReal_ofNat, Real.rpow_two]
  simp_rw [heq]
  have h0 := a_tendsto hv hvc
  have h1 : Tendsto (fun n => (∫ ξ, ‖fourierL2 (Sn n hv hvc) ξ - fourierL2 v ξ‖ ^ 2) ^ ((1 : ℝ) / 2))
      atTop (𝓝 ((0 : ℝ) ^ ((1 : ℝ) / 2))) :=
    (Real.continuousAt_rpow_const 0 ((1 : ℝ) / 2) (Or.inr (by norm_num))).tendsto.comp h0
  rw [Real.zero_rpow (by norm_num)] at h1
  have := ENNReal.tendsto_ofReal h1
  simpa using this

theorem exists_ae_subseq {v : Euc d → ℝ} (hv : ContDiff ℝ 2 v) (hvc : HasCompactSupport v) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧ ∀ᵐ ξ ∂(volume : Measure (Euc d)),
      Tendsto (fun k => fourierL2 (Sn (ns k) hv hvc) ξ) atTop (𝓝 (fourierL2 v ξ)) := by
  have hm : TendstoInMeasure volume (fun n => fourierL2 (Sn n hv hvc)) atTop (fourierL2 v) :=
    tendstoInMeasure_of_tendsto_eLpNorm (by norm_num) (a_eLpNorm_tendsto hv hvc)
  exact hm.exists_seq_tendsto_ae

/-- **`m_q v̂ ∈ L²` for `v ∈ C²_c`.** -/
theorem G_memLp {c s : ℝ} (hc : 0 < c) (hs2 : (d : ℝ) - 2 ≤ s) (hsd : s < d) (q : Euc d)
    {v : Euc d → ℝ} (hv : ContDiff ℝ 2 v) (hvc : HasCompactSupport v) :
    MemLp (fun ξ => ((mq c s q ξ : ℝ) : ℂ) * fourierL2 v ξ) 2 volume := by
  obtain ⟨ns, hns, hae⟩ := exists_ae_subseq hv hvc
  obtain ⟨E, hE⟩ := energy_bound hv hvc
  have hmv : MemLp v 2 volume := hv.continuous.memLp_of_hasCompactSupport hvc
  set C : ℝ := 2 * (c * ‖q‖ ^ 2) ^ 2 * E with hC
  have hmeasm : Measurable fun ξ : Euc d => ((mq c s q ξ : ℝ) : ℂ) :=
    Complex.measurable_ofReal.comp (measurable_mq c s q)
  have hG : ∀ n, AEStronglyMeasurable (fun ξ => ((mq c s q ξ : ℝ) : ℂ) *
      fourierL2 (Sn n hv hvc) ξ) volume := fun n =>
    hmeasm.aestronglyMeasurable.mul (aestronglyMeasurable_fourierL2 ((Sn n hv hvc).memLp 2 volume))
  have hG0 : AEStronglyMeasurable (fun ξ => ((mq c s q ξ : ℝ) : ℂ) * fourierL2 v ξ) volume :=
    hmeasm.aestronglyMeasurable.mul (aestronglyMeasurable_fourierL2 hmv)
  have hbound : ∀ᶠ k in atTop, eLpNorm (fun ξ => ((mq c s q ξ : ℝ) : ℂ) *
      fourierL2 (Sn (ns k) hv hvc) ξ) 2 volume ≤ ENNReal.ofReal (Real.sqrt C) := by
    have hev : ∀ᶠ k in atTop, energy (Sn (ns k) hv hvc) ≤ E :=
      hns.tendsto_atTop.eventually hE
    filter_upwards [hev] with k hk
    obtain ⟨hint, hle⟩ := mq_schwartz hc hs2 hsd q (Sn (ns k) hv hvc)
    have hmem : MemLp (fun ξ => ((mq c s q ξ : ℝ) : ℂ) * fourierL2 (Sn (ns k) hv hvc) ξ) 2 volume :=
      (memLp_two_iff_integrable_sq_norm (hG (ns k))).2 hint
    rw [hmem.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
    simp only [ENNReal.toReal_ofNat, Real.rpow_two]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [Real.sqrt_eq_rpow, one_div]
    have h1 : 0 ≤ ∫ ξ, ‖((mq c s q ξ : ℝ) : ℂ) * fourierL2 (Sn (ns k) hv hvc) ξ‖ ^ 2 :=
      integral_nonneg fun ξ => sq_nonneg _
    have h2 : ∫ ξ, ‖((mq c s q ξ : ℝ) : ℂ) * fourierL2 (Sn (ns k) hv hvc) ξ‖ ^ 2 ≤ C := by
      refine hle.trans ?_
      rw [hC]
      gcongr
    exact Real.rpow_le_rpow h1 h2 (by norm_num)
  have hlim : ∀ᵐ ξ ∂(volume : Measure (Euc d)), Tendsto (fun k => ((mq c s q ξ : ℝ) : ℂ) *
      fourierL2 (Sn (ns k) hv hvc) ξ) atTop (𝓝 (((mq c s q ξ : ℝ) : ℂ) * fourierL2 v ξ)) := by
    filter_upwards [hae] with ξ hξ
    exact hξ.const_mul _
  have hfin := Lp.eLpNorm_le_of_ae_tendsto (p := 2) (u := atTop) hbound (fun k => hG (ns k)) hG0 hlim
  exact lt_of_le_of_lt hfin ENNReal.ofReal_lt_top

end HRS.MS.UniqN3a
