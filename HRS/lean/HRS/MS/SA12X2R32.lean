import HRS.MS.SA12X2R32B

/-!
# S.A.12 R32 (SA12X2): `r3_first_derivative_pair`

Split `K = Kn + Kf + c` at scale `r` (`r3Kn`, `r3Kf`). The Kn part is a Schur bound with `‖Kn‖₁ = Cn r^(d-s)`.
The Kf part is integrated by parts onto the kernel and cut off to the ball of radius `2R`; its L1 norm is
`≤ CD r^(-(s+2-d))` by `sa12x2_kf_L1`. The scale is `r = (min ε 1 /(Cn+1))^(1/(d-s))`.
-/

set_option autoImplicit false
set_option maxHeartbeats 3200000

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12

open HRS HRS.Whole HRS.MH.AdjointRdP

variable {d : ℕ}

theorem r3_first_derivative_pair (d : ℕ) (hd : 1 ≤ d) (s : ℝ)
    (hs0 : 0 ≤ s) (hsd : s < d) (hs2 : (d : ℝ) < s+2) (R : ℝ) (hR : 1 ≤ R) :
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε → ∀ a : Euc d,
      ∀ φ ψ : Euc d → ℝ, ContDiff ℝ 1 φ → ContDiff ℝ 1 ψ →
      Function.support φ ⊆ Metric.closedBall a R →
      Function.support ψ ⊆ Metric.closedBall a R →
      ∀ w : Euc d, ‖w‖ ≤ 1 →
      |∫ x, φ x*fderiv ℝ
        (fun x => ∫ y, rieszKernel d s (x-y)*ψ y) x w| ≤
        ε*(∫ x, ‖fderiv ℝ ψ x‖^2) +
        C*(1+ε^(-((s+2-d)/((d : ℝ)-s))))*
          ((∫ x, φ x^2)+(∫ y, ψ y^2)) := by
  obtain ⟨CD, hCD0, hCD⟩ := sa12x2_kf_L1 (d := d) hs0 hs2 (2 * R) (by linarith)
  obtain ⟨Cn, hCn⟩ : ∃ c : ℝ, c = ∫ k : Euc d, |r3N1 d s k| := ⟨_, rfl⟩
  have hCn0 : 0 ≤ Cn := hCn ▸ integral_nonneg fun _ => abs_nonneg _
  have hds : (0 : ℝ) < (d : ℝ) - s := by linarith
  obtain ⟨p, hp⟩ : ∃ p : ℝ, p = (s + 2 - d) / ((d : ℝ) - s) := ⟨_, rfl⟩
  have hp0 : 0 ≤ p := by rw [hp]; apply div_nonneg <;> linarith
  have hC1 : (0 : ℝ) < Cn + 1 := by linarith
  have hXp : 0 ≤ (Cn + 1) ^ p := Real.rpow_nonneg hC1.le _
  refine ⟨1 + CD / 2 * (Cn + 1) ^ p, by nlinarith [mul_nonneg (div_nonneg hCD0 zero_le_two) hXp], ?_⟩
  intro ε hε a φ ψ hφ hψ hφs hψs w hw
  rw [← hp]
  -- scale
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = min ε 1 := ⟨_, rfl⟩
  have hδ0 : 0 < δ := by rw [hδ]; exact lt_min hε one_pos
  have hδ1 : δ ≤ 1 := by rw [hδ]; exact min_le_right _ _
  have hδε : δ ≤ ε := by rw [hδ]; exact min_le_left _ _
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = (δ / (Cn + 1)) ^ (1 / ((d : ℝ) - s)) := ⟨_, rfl⟩
  have hx0 : 0 < δ / (Cn + 1) := div_pos hδ0 hC1
  have hr0 : 0 < r := by rw [hr]; exact Real.rpow_pos_of_pos hx0 _
  have hr1 : r ≤ 1 := by
    rw [hr]
    apply Real.rpow_le_one hx0.le _ (div_nonneg zero_le_one hds.le)
    rw [div_le_one hC1]; linarith
  have hrd : r ^ ((d : ℝ) - s) = δ / (Cn + 1) := by
    rw [hr, ← Real.rpow_mul hx0.le, one_div_mul_cancel hds.ne', Real.rpow_one]
  have hrθ : r ^ (-(s + 2 - d)) = (Cn + 1) ^ p * δ ^ (-p) := by
    rw [hr, ← Real.rpow_mul hx0.le]
    have e : 1 / ((d : ℝ) - s) * (-(s + 2 - d)) = -p := by rw [hp]; ring
    rw [e, Real.div_rpow hδ0.le hC1.le, Real.rpow_neg hC1.le, div_inv_eq_mul]
    ring
  have hδp : δ ^ (-p) ≤ 1 + ε ^ (-p) := by
    have hεp : 0 ≤ ε ^ (-p) := Real.rpow_nonneg hε.le _
    rcases le_total ε 1 with h | h
    · have hδe : δ = ε := by rw [hδ]; exact min_eq_left h
      rw [hδe]; linarith
    · have hδe : δ = 1 := by rw [hδ]; exact min_eq_right h
      rw [hδe, Real.one_rpow]; linarith
  have hrθ_le : r ^ (-(s + 2 - d)) ≤ (Cn + 1) ^ p * (1 + ε ^ (-p)) := by
    rw [hrθ]; exact mul_le_mul_of_nonneg_left hδp hXp
  have hcoef : Cn * r ^ ((d : ℝ) - s) ≤ δ := by
    rw [hrd, mul_div_assoc', div_le_iff₀ hC1]; nlinarith
  -- regularity and cutoffs
  have hφc : HasCompactSupport φ :=
    HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall a R) hφs
  have hψc : HasCompactSupport ψ :=
    HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall a R) hψs
  have hKn_int : Integrable (r3Kn d s r) := r3Kn_integrable hd hs0 hsd hr0
  have hKf_c1 : ContDiff ℝ 1 (r3Kf d s r) :=
    (r3Kf_contDiff (d := d) s hr0).of_le (by exact_mod_cast r3_le_infty 1)
  have hsplit := r3_fderiv_split (g := rieszKernel d s) (Kn := r3Kn d s r) (Kf := r3Kf d s r)
    (c := r3gp s r) (Ξ := ψ) (fun h => by have := r3_Kn_add_Kf s r h; linarith)
    hKn_int.locallyIntegrable hKf_c1.continuous.locallyIntegrable hψ hψc
  simp_rw [hsplit]
  have hA : Continuous (fun x => fderiv ℝ (fun x => ∫ y, r3Kn d s r (x - y) * ψ y) x w) :=
    ((r3_contDiff_conv hKn_int.locallyIntegrable (n := 1) hψ hψc).continuous_fderiv one_ne_zero).clm_apply
      continuous_const
  have hB : Continuous (fun x => fderiv ℝ (fun x => ∫ y, r3Kf d s r (x - y) * ψ y) x w) :=
    ((r3_contDiff_conv hKf_c1.continuous.locallyIntegrable (n := 1) hψ hψc).continuous_fderiv
      one_ne_zero).clm_apply continuous_const
  have hI1 : Integrable (fun x => φ x *
      fderiv ℝ (fun x => ∫ y, r3Kn d s r (x - y) * ψ y) x w) :=
    (hφ.continuous.mul hA).integrable_of_hasCompactSupport hφc.mul_right
  have hI2 : Integrable (fun x => φ x *
      fderiv ℝ (fun x => ∫ y, r3Kf d s r (x - y) * ψ y) x w) :=
    (hφ.continuous.mul hB).integrable_of_hasCompactSupport hφc.mul_right
  have hsum : ∫ x, φ x * (fderiv ℝ (fun x => ∫ y, r3Kn d s r (x - y) * ψ y) x w +
        fderiv ℝ (fun x => ∫ y, r3Kf d s r (x - y) * ψ y) x w) =
      (∫ x, φ x * fderiv ℝ (fun x => ∫ y, r3Kn d s r (x - y) * ψ y) x w) +
        ∫ x, φ x * fderiv ℝ (fun x => ∫ y, r3Kf d s r (x - y) * ψ y) x w := by
    simp_rw [mul_add]; exact integral_add hI1 hI2
  rw [hsum]
  -- basic integrals
  have hφ2 : Integrable (fun x => φ x ^ 2) := by
    have hc : HasCompactSupport (fun x => φ x ^ 2) :=
      hφc.comp_left (g := fun t : ℝ => t ^ 2) (by simp)
    exact Continuous.integrable_of_hasCompactSupport (f := fun x => φ x ^ 2)
      (hφ.continuous.pow 2) hc
  have hψ2 : Integrable (fun y => ψ y ^ 2) := by
    have hc : HasCompactSupport (fun y => ψ y ^ 2) :=
      hψc.comp_left (g := fun t : ℝ => t ^ 2) (by simp)
    exact Continuous.integrable_of_hasCompactSupport (f := fun y => ψ y ^ 2)
      (hψ.continuous.pow 2) hc
  have hDψ : Continuous (fun y => fderiv ℝ ψ y w) := (hψ.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hDψ2 : Integrable (fun y => (fderiv ℝ ψ y w) ^ 2) := by
    have hc : HasCompactSupport (fun y => (fderiv ℝ ψ y w) ^ 2) :=
      (hψc.fderiv_apply ℝ w).comp_left (g := fun t : ℝ => t ^ 2) (by simp)
    exact Continuous.integrable_of_hasCompactSupport (f := fun y => (fderiv ℝ ψ y w) ^ 2)
      (hDψ.pow 2) hc
  have hGi : Integrable (fun y => ‖fderiv ℝ ψ y‖ ^ 2) := by
    have hc : HasCompactSupport (fun y => ‖fderiv ℝ ψ y‖ ^ 2) :=
      ((hψc.fderiv ℝ).norm).comp_left (g := fun t : ℝ => t ^ 2) (by simp)
    exact Continuous.integrable_of_hasCompactSupport (f := fun y => ‖fderiv ℝ ψ y‖ ^ 2)
      ((hψ.continuous_fderiv one_ne_zero).norm.pow 2) hc
  have hD2 : ∀ y, (fderiv ℝ ψ y w) ^ 2 ≤ ‖fderiv ℝ ψ y‖ ^ 2 := by
    intro y
    have h1 : |fderiv ℝ ψ y w| ≤ ‖fderiv ℝ ψ y‖ := by
      rw [← Real.norm_eq_abs]
      exact (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_of_le_one_right (norm_nonneg _) hw)
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) h1 2
  have hXD : ∫ y, (fderiv ℝ ψ y w) ^ 2 ≤ ∫ y, ‖fderiv ℝ ψ y‖ ^ 2 :=
    integral_mono hDψ2 hGi hD2
  have hXD0 : 0 ≤ ∫ y, (fderiv ℝ ψ y w) ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have hXφ0 : 0 ≤ ∫ x, φ x ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have hYψ0 : 0 ≤ ∫ y, ψ y ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have hG0 : 0 ≤ ∫ x, ‖fderiv ℝ ψ x‖ ^ 2 := integral_nonneg fun _ => sq_nonneg _
  -- Kn part (Schur)
  have T1 : |∫ x, φ x * ∫ y, r3Kn d s r (x - y) * fderiv ℝ ψ y w| ≤
      (∫ h, |r3Kn d s r h|) * ((∫ x, φ x ^ 2) + ∫ y, (fderiv ℝ ψ y w) ^ 2) / 2 :=
    r3_pair_le (K := r3Kn d s r) (A := φ) (B := fun y => fderiv ℝ ψ y w)
      (r3Kn_meas (d := d) s r) hφ.continuous.measurable hDψ.measurable hKn_int hφ2 hDψ2
  have hKnl1 : ∫ h, |r3Kn d s r h| = Cn * r ^ ((d : ℝ) - s) := by
    rw [r3Kn_l1 hd s hr0, hCn]
  have hKn_le : (∫ h, |r3Kn d s r h|) ≤ δ := by rw [hKnl1]; exact hcoef
  -- the Kn term, with the derivative written as a convolution with `∂_w ψ`
  have hT1eq : ∫ x, φ x * fderiv ℝ (fun x => ∫ y, r3Kn d s r (x - y) * ψ y) x w =
      ∫ x, φ x * ∫ y, r3Kn d s r (x - y) * fderiv ℝ ψ y w :=
    integral_congr_ae (Eventually.of_forall fun x => by
      show φ x * fderiv ℝ (fun x => ∫ y, r3Kn d s r (x - y) * ψ y) x w =
        φ x * ∫ y, r3Kn d s r (x - y) * fderiv ℝ ψ y w
      rw [r3_fderiv_conv_apply hKn_int.locallyIntegrable hψ hψc x w])
  have hT1' : (∫ h, |r3Kn d s r h|) * ((∫ x, φ x ^ 2) + ∫ y, (fderiv ℝ ψ y w) ^ 2) / 2 ≤
      (∫ x, φ x ^ 2) / 2 + ε * (∫ x, ‖fderiv ℝ ψ x‖ ^ 2) / 2 := by
    have hS0 : 0 ≤ (∫ x, φ x ^ 2) + ∫ y, (fderiv ℝ ψ y w) ^ 2 := add_nonneg hXφ0 hXD0
    have h1 : (∫ h, |r3Kn d s r h|) * ((∫ x, φ x ^ 2) + ∫ y, (fderiv ℝ ψ y w) ^ 2) ≤
        δ * ((∫ x, φ x ^ 2) + ∫ y, (fderiv ℝ ψ y w) ^ 2) :=
      mul_le_mul_of_nonneg_right hKn_le hS0
    have h2 : δ * (∫ x, φ x ^ 2) ≤ ∫ x, φ x ^ 2 := mul_le_of_le_one_left hXφ0 hδ1
    have h3 : δ * (∫ y, (fderiv ℝ ψ y w) ^ 2) ≤ ε * (∫ x, ‖fderiv ℝ ψ x‖ ^ 2) :=
      mul_le_mul hδε hXD hXD0 hε.le
    have h4 : δ * ((∫ x, φ x ^ 2) + ∫ y, (fderiv ℝ ψ y w) ^ 2) =
        δ * (∫ x, φ x ^ 2) + δ * (∫ y, (fderiv ℝ ψ y w) ^ 2) := by ring
    linarith
  -- the Kf term: integrate by parts onto the kernel, then cut off to the ball of radius 2R
  obtain ⟨Kc, hKc⟩ : ∃ K : Euc d → ℝ,
      K = (closedBall (0 : Euc d) (2 * R)).indicator (fun h => fderiv ℝ (r3Kf d s r) h w) :=
    ⟨_, rfl⟩
  have hcontD : Continuous (fun h => fderiv ℝ (r3Kf d s r) h w) :=
    ((r3Kf_contDiff (d := d) s hr0).continuous_fderiv (by simp)).clm_apply
      continuous_const
  have hKc_meas : Measurable Kc := by
    rw [hKc]; exact hcontD.measurable.indicator measurableSet_closedBall
  have hKc_int : Integrable Kc := by
    rw [hKc]
    exact (hcontD.continuousOn.integrableOn_compact (isCompact_closedBall (0 : Euc d) (2 * R))).integrable_indicator
      measurableSet_closedBall
  have hpw : ∀ x, φ x * fderiv ℝ (fun x => ∫ y, r3Kf d s r (x - y) * ψ y) x w =
      φ x * ∫ y, Kc (x - y) * ψ y := by
    intro x
    by_cases hφx : φ x = 0
    · simp [hφx]
    · congr 1
      rw [r3_fderiv_conv_apply hKf_c1.continuous.locallyIntegrable hψ hψc x w,
        r3_ibp_conv hKf_c1 hψ hψc x w]
      refine integral_congr_ae (Eventually.of_forall fun y => ?_)
      by_cases hy : ψ y = 0
      · simp [hy]
      · have hx : ‖x - a‖ ≤ R := by
          have := hφs (Function.mem_support.2 hφx)
          rwa [mem_closedBall, dist_eq_norm] at this
        have hy' : ‖y - a‖ ≤ R := by
          have := hψs (Function.mem_support.2 hy)
          rwa [mem_closedBall, dist_eq_norm] at this
        have hxy : x - y ∈ closedBall (0 : Euc d) (2 * R) := by
          rw [mem_closedBall_zero_iff]
          have h3 := norm_sub_le (x - a) (y - a)
          rw [sub_sub_sub_cancel_right] at h3
          linarith
        simp only [hKc, indicator_of_mem hxy]
  have hT2eq : ∫ x, φ x * fderiv ℝ (fun x => ∫ y, r3Kf d s r (x - y) * ψ y) x w =
      ∫ x, φ x * ∫ y, Kc (x - y) * ψ y := integral_congr_ae (Eventually.of_forall hpw)
  have T2 : |∫ x, φ x * ∫ y, Kc (x - y) * ψ y| ≤
      (∫ h, |Kc h|) * ((∫ x, φ x ^ 2) + ∫ y, ψ y ^ 2) / 2 :=
    r3_pair_le (K := Kc) (A := φ) (B := ψ) hKc_meas hφ.continuous.measurable
      hψ.continuous.measurable hKc_int hφ2 hψ2
  have hKcabs : ∫ h, |Kc h| ≤ CD * r ^ (-(s + 2 - d)) := by
    have e : (fun h => |Kc h|) =
        (closedBall (0 : Euc d) (2 * R)).indicator (fun h => |fderiv ℝ (r3Kf d s r) h w|) := by
      funext h
      by_cases hh : h ∈ closedBall (0 : Euc d) (2 * R)
      · rw [hKc, indicator_of_mem hh, indicator_of_mem hh]
      · rw [hKc, indicator_of_notMem hh, indicator_of_notMem hh, abs_zero]
    rw [e]
    exact hCD r hr0 hr1 w hw
  have hY0 : 0 ≤ (∫ x, φ x ^ 2) + ∫ y, ψ y ^ 2 := add_nonneg hXφ0 hYψ0
  have hT2' : (∫ h, |Kc h|) * ((∫ x, φ x ^ 2) + ∫ y, ψ y ^ 2) / 2 ≤
      CD / 2 * (Cn + 1) ^ p * (1 + ε ^ (-p)) * ((∫ x, φ x ^ 2) + ∫ y, ψ y ^ 2) := by
    have h1 : ∫ h, |Kc h| ≤ CD * ((Cn + 1) ^ p * (1 + ε ^ (-p))) :=
      hKcabs.trans (mul_le_mul_of_nonneg_left hrθ_le hCD0)
    calc (∫ h, |Kc h|) * ((∫ x, φ x ^ 2) + ∫ y, ψ y ^ 2) / 2
        ≤ CD * ((Cn + 1) ^ p * (1 + ε ^ (-p))) * ((∫ x, φ x ^ 2) + ∫ y, ψ y ^ 2) / 2 := by
          gcongr
      _ = CD / 2 * (Cn + 1) ^ p * (1 + ε ^ (-p)) * ((∫ x, φ x ^ 2) + ∫ y, ψ y ^ 2) := by ring
  -- assembly
  rw [hT1eq, hT2eq]
  refine (abs_add_le _ _).trans ?_
  have hεG : 0 ≤ ε * (∫ x, ‖fderiv ℝ ψ x‖ ^ 2) := mul_nonneg hε.le hG0
  have hεp : 0 ≤ ε ^ (-p) := Real.rpow_nonneg hε.le _
  have hXφY : (∫ x, φ x ^ 2) ≤ (1 + ε ^ (-p)) * ((∫ x, φ x ^ 2) + ∫ y, ψ y ^ 2) := by
    nlinarith [mul_nonneg hεp hXφ0, mul_nonneg hεp hYψ0]
  have hYY : ((∫ x, φ x ^ 2) + ∫ y, ψ y ^ 2) ≤ (1 + ε ^ (-p)) * ((∫ x, φ x ^ 2) + ∫ y, ψ y ^ 2) :=
    le_mul_of_one_le_left hY0 (by linarith)
  have hid : (1 + CD / 2 * (Cn + 1) ^ p) * (1 + ε ^ (-p)) * ((∫ x, φ x ^ 2) + ∫ y, ψ y ^ 2) =
      (1 + ε ^ (-p)) * ((∫ x, φ x ^ 2) + ∫ y, ψ y ^ 2) +
        CD / 2 * (Cn + 1) ^ p * (1 + ε ^ (-p)) * ((∫ x, φ x ^ 2) + ∫ y, ψ y ^ 2) := by ring
  have hT1 := T1.trans hT1'
  have hT2 := T2.trans hT2'
  linarith [hT1, hT2, hXφY, hεG, hid]


end HRS.MH.AdjointRd.Phase2SA12
