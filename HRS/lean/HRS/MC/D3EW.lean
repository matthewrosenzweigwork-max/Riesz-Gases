import HRS.MC.D3EWAux2

/-!
# Packet D3EW: Lemma D.3 on `ℝ^d`, item (ii) for the short-scale kernel `w_λ`.

Spec: `HRS/Appendix/FDL.lean`, `HRS.fdl_kernel_euclid` (the `fdlWE` conjuncts of (ii)).
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal ContDiff

namespace HRS.MC.D3EW

open HRS HRS.MC.FDLE

variable {d : ℕ}

lemma d3ew_K_contDiffOn {φ : Euc d → ℝ} (hφ : ContDiff ℝ ∞ φ) (b s : ℝ) :
    ContDiffOn ℝ ∞ (Function.uncurry (fun (t : ℝ) (z : Euc d) => (b * t ^ (-s - 1)) * φ (t⁻¹ • z)))
      (Ioi (0 : ℝ) ×ˢ univ) := by
  intro p hp
  apply ContDiffAt.contDiffWithinAt
  have hp0 : p.1 ≠ 0 := (show (0 : ℝ) < p.1 from hp.1).ne'
  have h1 : ContDiffAt ℝ ∞ (fun p : ℝ × Euc d => p.1 ^ (-s - 1)) p :=
    (Real.contDiffAt_rpow_const_of_ne hp0).comp p contDiff_fst.contDiffAt
  have h2 : ContDiffAt ℝ ∞ (fun p : ℝ × Euc d => p.1⁻¹) p :=
    (contDiffAt_inv ℝ hp0).comp p contDiff_fst.contDiffAt
  have h3 : ContDiffAt ℝ ∞ (fun p : ℝ × Euc d => p.1⁻¹ • p.2) p :=
    h2.smul contDiff_snd.contDiffAt
  have h4 : ContDiffAt ℝ ∞ (fun p : ℝ × Euc d => φ (p.1⁻¹ • p.2)) p :=
    (hφ.contDiffAt).comp p h3
  exact (contDiffAt_const.mul h1).mul h4

lemma d3ew_K_bdd {ψ : Euc d → ℝ} (hψ : IsFDLProfile ψ) (b s a lam : ℝ) (ha : 0 < a) (k : ℕ) :
    ∃ B : ℝ, ∀ t ∈ Ioc a lam, ∀ z : Euc d,
      ‖iteratedFDeriv ℝ k (fun z => (b * t ^ (-s - 1)) * fdlPhi ψ (t⁻¹ • z)) z‖ ≤ B := by
  obtain ⟨M, hM0, hM⟩ := d3ew_dphi_bound hψ k
  have hcont : ContinuousOn (fun t : ℝ => |b * t ^ (-s - 1)| * (t⁻¹) ^ k * M) (Icc a lam) := by
    apply ContinuousOn.mul
    apply ContinuousOn.mul
    · apply ContinuousOn.abs
      apply ContinuousOn.mul continuousOn_const
      exact ContinuousOn.rpow_const continuousOn_id
        (fun t ht => Or.inl (lt_of_lt_of_le ha ht.1).ne')
    · exact ContinuousOn.pow (continuousOn_inv₀.mono
        (fun t ht => (lt_of_lt_of_le ha ht.1).ne')) k
    · exact continuousOn_const
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  refine ⟨B, fun t ht z => ?_⟩
  have ht0 : 0 < t := lt_trans ha ht.1
  refine (d3ew_scale_bound (d3ew_phi_smooth hψ) _ ht0 k z).trans ?_
  have h1 := hB t (Ioc_subset_Icc_self ht)
  rw [Real.norm_of_nonneg (by positivity)] at h1
  refine le_trans ?_ h1
  gcongr
  exact hM _


/-- Tail integral of the power function against the indicator of `[c, ∞)`. -/
lemma d3ew_tail {e c κ : ℝ} (he : 0 < e) (hc : 0 < c) (hκ : 0 ≤ κ) (J : Set ℝ) :
    ∫ t in J, (Ici c).indicator (fun t : ℝ => κ * t ^ (-e - 1)) t ≤ κ * (c ^ (-e) / e) ∧
    IntegrableOn ((Ici c).indicator (fun t : ℝ => κ * t ^ (-e - 1))) J := by
  have hint : IntegrableOn (fun t : ℝ => t ^ (-e - 1)) (Ioi c) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) hc
  have hint0 : IntegrableOn (fun t : ℝ => t ^ (-e - 1)) (Ici c) := by
    rw [integrableOn_Ici_iff_integrableOn_Ioi]
    exact hint
  have hint' : IntegrableOn (fun t : ℝ => κ * t ^ (-e - 1)) (Ici c) := hint0.const_mul κ
  refine ⟨?_, (hint'.integrable_indicator measurableSet_Ici).integrableOn⟩
  rw [setIntegral_indicator measurableSet_Ici]
  calc ∫ t in J ∩ Ici c, κ * t ^ (-e - 1)
      ≤ ∫ t in Ici c, κ * t ^ (-e - 1) := by
        refine setIntegral_mono_set hint' ?_ (Filter.Eventually.of_forall fun x hx => hx.2)
        filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
        have : 0 < t := lt_of_lt_of_le hc ht
        exact mul_nonneg hκ (Real.rpow_nonneg this.le _)
    _ = κ * (c ^ (-e) / e) := by
        rw [integral_const_mul, integral_Ici_eq_integral_Ioi, integral_Ioi_rpow_of_lt (by linarith) hc]
        congr 1
        rw [show -e - 1 + 1 = -e by ring]
        field_simp

/-- Pointwise bound of the integrand of the derivative formula. -/
lemma d3ew_pt_bound {ψ : Euc d → ℝ} (hψ : IsFDLProfile ψ) (b s : ℝ) (hb0 : 0 < b) (j : ℕ) {M : ℝ}
    (hM : ∀ x, ‖iteratedFDeriv ℝ j (fdlPhi ψ) x‖ ≤ M) (z : Euc d) {t : ℝ} (ht : 0 < t) :
    |b * t ^ (-s - 1)| * (t⁻¹) ^ j * ‖iteratedFDeriv ℝ j (fdlPhi ψ) (t⁻¹ • z)‖
      ≤ (Ici ‖z‖).indicator (fun t : ℝ => (b * M) * t ^ (-((j : ℝ) + s) - 1)) t := by
  have hpos : 0 ≤ t ^ (-s - 1) := Real.rpow_nonneg ht.le _
  by_cases htz : ‖z‖ ≤ t
  · rw [Set.indicator_of_mem (show t ∈ Ici ‖z‖ from htz)]
    have h1 : t ^ (-((j : ℝ) + s) - 1) = t ^ (-s - 1) * (t⁻¹) ^ j := by
      rw [show -((j : ℝ) + s) - 1 = (-s - 1) + (-(j : ℝ)) by ring, Real.rpow_add ht,
        Real.rpow_neg ht.le, Real.rpow_natCast, inv_pow]
    rw [h1, abs_of_nonneg (mul_nonneg hb0.le hpos)]
    have := hM (t⁻¹ • z)
    have h2 : 0 ≤ b * t ^ (-s - 1) * (t⁻¹) ^ j :=
      mul_nonneg (mul_nonneg hb0.le hpos) (pow_nonneg (inv_nonneg.2 ht.le) _)
    calc b * t ^ (-s - 1) * (t⁻¹) ^ j * ‖iteratedFDeriv ℝ j (fdlPhi ψ) (t⁻¹ • z)‖
        ≤ b * t ^ (-s - 1) * (t⁻¹) ^ j * M := by gcongr
      _ = b * M * (t ^ (-s - 1) * (t⁻¹) ^ j) := by ring
  · push Not at htz
    rw [Set.indicator_of_notMem (show t ∉ Ici ‖z‖ from not_le.2 htz)]
    have h1 : 1 < ‖t⁻¹ • z‖ := by
      rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 ht.le), ← div_eq_inv_mul, one_lt_div ht]
      exact htz
    rw [d3ew_dphi_zero hψ j h1]
    simp

theorem d3ew_deriv (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {ψ : Euc d → ℝ}
    (hψ : IsFDLProfile ψ) {b : ℝ} (hb : IsFDLConst ψ s b) :
    ∀ j : ℕ, 0 < (j : ℝ) + s → ∃ C : ℝ, 0 ≤ C ∧ ∀ lam : ℝ, 0 < lam → lam < 1 → ∀ z : Euc d, z ≠ 0 →
      ‖iteratedFDeriv ℝ j (fdlWE ψ s b lam) z‖ ≤ (if ‖z‖ ≤ lam then C * ‖z‖ ^ (-s - (j : ℝ)) else 0) := by
  intro j hj
  obtain ⟨M, hM0, hM⟩ := d3ew_dphi_bound hψ j
  have hb0 : 0 < b := hb.1
  refine ⟨b * M / ((j : ℝ) + s), div_nonneg (mul_nonneg hb0.le hM0) hj.le,
    fun lam hl0 hl1 z hz => ?_⟩
  have hzpos : 0 < ‖z‖ := norm_pos_iff.2 hz
  by_cases hzl : lam < ‖z‖
  · have hev : fdlWE ψ s b lam =ᶠ[𝓝 z] fun _ => (0 : ℝ) := by
      filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hzl] with w hw
      exact fdle_W_vanish hψ (le_of_lt hw) hl0
    rw [(hev.iteratedFDeriv ℝ j).eq_of_nhds]
    simp [not_le.2 hzl]
  · push Not at hzl
    rw [if_pos hzl]
    set a : ℝ := ‖z‖ / 2 with ha_def
    have ha : 0 < a := by positivity
    have haz : a < ‖z‖ := by linarith
    set K : ℝ → Euc d → ℝ := fun t w => (b * t ^ (-s - 1)) * fdlPhi ψ (t⁻¹ • w) with hK
    have hev : fdlWE ψ s b lam =ᶠ[𝓝 z] fun w => ∫ t in Ioc a lam, K t w := by
      filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds haz] with w hw
      exact d3ew_rep_loc hψ s b lam ha.le hw.le
    have hmain : iteratedFDeriv ℝ j (fdlWE ψ s b lam) z
        = ∫ t in Ioc a lam, iteratedFDeriv ℝ j (K t) z := by
      rw [(hev.iteratedFDeriv ℝ j).eq_of_nhds]
      exact d3ew_iter_integral (J := Ioc a lam) (U := Ioi 0) measurableSet_Ioc
        measure_Ioc_lt_top isOpen_Ioi (fun t ht => lt_trans ha ht.1) j K
        (d3ew_K_contDiffOn (d3ew_phi_smooth hψ) b s) (d3ew_K_bdd hψ b s a lam ha) z
    rw [hmain]
    have hκ : 0 ≤ b * M := mul_nonneg hb0.le hM0
    obtain ⟨htail, hint⟩ := d3ew_tail hj hzpos hκ (Ioc a lam)
    calc ‖∫ t in Ioc a lam, iteratedFDeriv ℝ j (K t) z‖
        ≤ ∫ t in Ioc a lam, ‖iteratedFDeriv ℝ j (K t) z‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ t in Ioc a lam, (Ici ‖z‖).indicator
            (fun t : ℝ => (b * M) * t ^ (-((j : ℝ) + s) - 1)) t := by
          refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun t => norm_nonneg _) hint ?_
          filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
          have ht0 : 0 < t := lt_trans ha ht.1
          exact (d3ew_scale_bound (d3ew_phi_smooth hψ) _ ht0 j z).trans
            (d3ew_pt_bound hψ b s hb0 j hM z ht0)
      _ ≤ (b * M) * (‖z‖ ^ (-((j : ℝ) + s)) / ((j : ℝ) + s)) := htail
      _ = b * M / ((j : ℝ) + s) * ‖z‖ ^ (-s - (j : ℝ)) := by
          rw [show -s - (j : ℝ) = -((j : ℝ) + s) by ring]; ring


/-- The logarithmic integral. -/
lemma d3ew_log_integral {c lam κ : ℝ} (hc : 0 < c) (hcl : c ≤ lam) :
    ∫ t in Ioc 0 lam, (Ici c).indicator (fun t : ℝ => κ * t⁻¹) t
      = κ * Real.log (lam / c) := by
  rw [setIntegral_indicator measurableSet_Ici]
  have hset : Ioc 0 lam ∩ Ici c = Icc c lam := by
    ext t
    simp only [mem_inter_iff, mem_Ioc, mem_Ici, mem_Icc]
    constructor
    · rintro ⟨⟨_, h2⟩, h3⟩; exact ⟨h3, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨⟨lt_of_lt_of_le hc h1, h2⟩, h1⟩
  rw [hset, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hcl,
    intervalIntegral.integral_const_mul, integral_inv_of_pos hc (lt_of_lt_of_le hc hcl)]

lemma d3ew_log_int {c lam κ : ℝ} (hc : 0 < c) :
    IntegrableOn ((Ici c).indicator (fun t : ℝ => κ * t⁻¹)) (Ioc 0 lam) := by
  have hmeas : Measurable ((Ici c).indicator (fun t : ℝ => κ * t⁻¹)) :=
    (measurable_inv.const_mul κ).indicator measurableSet_Ici
  refine Integrable.mono' (g := fun _ => |κ| * c⁻¹) (integrable_const _) hmeas.aestronglyMeasurable
    (Filter.Eventually.of_forall fun t => ?_)
  by_cases ht : t ∈ Ici c
  · rw [Set.indicator_of_mem ht, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    have ht0 : 0 < t := lt_of_lt_of_le hc ht
    rw [abs_of_pos (inv_pos.2 ht0)]
    gcongr
    exact ht
  · rw [Set.indicator_of_notMem ht]
    simp only [norm_zero]
    positivity

theorem d3ew_log (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {ψ : Euc d → ℝ}
    (hψ : IsFDLProfile ψ) {b : ℝ} (hb : IsFDLConst ψ s b) :
    s = 0 → ∃ C : ℝ, 0 ≤ C ∧ ∀ lam : ℝ, 0 < lam → lam < 1 → ∀ z : Euc d, z ≠ 0 →
      |fdlWE ψ s b lam z| ≤ (if ‖z‖ ≤ lam then C * Real.log (lam / ‖z‖) else 0) := by
  intro hs
  subst hs
  obtain ⟨M, hM0, hM⟩ := d3ew_dphi_bound hψ 0
  have hb0 : 0 < b := hb.1
  refine ⟨b * M, mul_nonneg hb0.le hM0, fun lam hl0 hl1 z hz => ?_⟩
  have hzpos : 0 < ‖z‖ := norm_pos_iff.2 hz
  by_cases hzl : lam < ‖z‖
  · rw [fdle_W_vanish hψ hzl.le hl0, if_neg (not_le.2 hzl)]
    simp
  · push Not at hzl
    rw [if_pos hzl, ← d3ew_log_integral (κ := b * M) hzpos hzl, d3ew_rep, ← Real.norm_eq_abs]
    calc ‖∫ t in Ioc 0 lam, b * t ^ (-(0 : ℝ) - 1) * fdlPhi ψ (t⁻¹ • z)‖
        ≤ ∫ t in Ioc 0 lam, ‖b * t ^ (-(0 : ℝ) - 1) * fdlPhi ψ (t⁻¹ • z)‖ :=
          norm_integral_le_integral_norm _
      _ ≤ ∫ t in Ioc 0 lam, (Ici ‖z‖).indicator (fun t : ℝ => (b * M) * t⁻¹) t := by
          refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun t => norm_nonneg _)
            (d3ew_log_int hzpos) ?_
          filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
          have h1 := d3ew_pt_bound hψ b 0 hb0 0 hM z ht.1
          have h2 : ∀ u : ℝ, u ^ (-(((0 : ℕ) : ℝ) + 0) - 1) = u⁻¹ := fun u => by
            rw [show -(((0 : ℕ) : ℝ) + 0) - 1 = -1 by simp, Real.rpow_neg_one]
          simp only [h2, pow_zero, mul_one, norm_iteratedFDeriv_zero] at h1
          rw [norm_mul]
          simpa using h1

end HRS.MC.D3EW
