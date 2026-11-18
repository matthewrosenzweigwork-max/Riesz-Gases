import HRS.Appendix.FDL

/-!
# Packet D1E: Lemma D.1, the Euclidean clauses (namespace `HRS.MC.D1E`)

Helpers for the assembled lemma D.1 (`fdl_rep`): `d1e_pos` (the `0 < s` Euclidean representation)
and `d1e_zero` (the `s = 0` renormalised representation, with `b * fdlPhi ψ 0 = 1`).
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

namespace HRS.MC.D1E

open HRS

variable {d : ℕ}

/-- `φ = ψ * ψ` is nonnegative. -/
theorem d1e_phi_nonneg {ψ : Euc d → ℝ} (hψ : IsFDLProfile ψ) (y : Euc d) : 0 ≤ fdlPhi ψ y := by
  unfold fdlPhi
  rw [convolution_def]
  refine integral_nonneg fun t => ?_
  simp only [ContinuousLinearMap.mul_apply']
  exact mul_nonneg (hψ.nonneg t) (hψ.nonneg _)

/-- `ψ` vanishes outside `B(0,1/2)`. -/
theorem d1e_psi_zero_of_norm {ψ : Euc d → ℝ} (hψ : IsFDLProfile ψ) {t : Euc d} (ht : 1 / 2 ≤ ‖t‖) :
    ψ t = 0 := by
  by_contra h
  have hmem : t ∈ tsupport ψ := subset_tsupport ψ (by simpa using h)
  have := hψ.support hmem
  rw [Metric.mem_ball, dist_zero_right] at this
  linarith

/-- `φ` vanishes outside `B(0,1)` (pointwise). -/
theorem d1e_phi_zero_of_norm {ψ : Euc d → ℝ} (hψ : IsFDLProfile ψ) {y : Euc d} (hy : 1 ≤ ‖y‖) :
    fdlPhi ψ y = 0 := by
  unfold fdlPhi
  rw [convolution_def]
  refine integral_eq_zero_of_ae (Filter.Eventually.of_forall fun t => ?_)
  simp only [ContinuousLinearMap.mul_apply', Pi.zero_apply]
  by_cases h1 : 1 / 2 ≤ ‖t‖
  · rw [d1e_psi_zero_of_norm hψ h1, zero_mul]
  by_cases h2 : 1 / 2 ≤ ‖y - t‖
  · rw [d1e_psi_zero_of_norm hψ h2, mul_zero]
  exfalso
  simp only [not_le] at h1 h2
  have h3 : ‖y‖ ≤ ‖t‖ + ‖y - t‖ := by
    calc ‖y‖ = ‖t + (y - t)‖ := by congr 1; abel
      _ ≤ ‖t‖ + ‖y - t‖ := norm_add_le _ _
  linarith

/-- Radiality of `φ = ψ * ψ`: `‖y‖ = ‖z‖ → φ y = φ z`. -/
theorem d1e_phi_radial {ψ : Euc d → ℝ} (hψ : IsFDLProfile ψ) {y z : Euc d} (hyz : ‖y‖ = ‖z‖) :
    fdlPhi ψ y = fdlPhi ψ z := by
  set L : Euc d ≃ₗᵢ[ℝ] Euc d := Submodule.reflection (Submodule.span ℝ {y - z})ᗮ with hL
  have hLy : L y = z := Submodule.reflection_sub hyz
  have hmp : MeasurePreserving L := L.measurePreserving
  have hemb : MeasurableEmbedding L := L.toHomeomorph.measurableEmbedding
  have hpt : ∀ x, ψ (L x) * ψ (L y - L x) = ψ x * ψ (y - x) := by
    intro x
    rw [← map_sub, hψ.radial (L (y - x)) (y - x) (LinearIsometryEquiv.norm_map L _),
      hψ.radial (L x) x (LinearIsometryEquiv.norm_map L _)]
  unfold fdlPhi
  rw [convolution_def, convolution_def, ← hLy]
  simp only [ContinuousLinearMap.mul_apply']
  have key := hmp.integral_comp hemb (fun t => ψ t * ψ (L y - t))
  rw [← key]
  congr 1
  funext x
  exact (hpt x).symm

/-- `ψ` has compact support. -/
theorem d1e_psi_compact {ψ : Euc d → ℝ} (hψ : IsFDLProfile ψ) : HasCompactSupport ψ :=
  (isCompact_closedBall (0 : Euc d) (1 / 2)).of_isClosed_subset (isClosed_tsupport ψ)
    (hψ.support.trans Metric.ball_subset_closedBall)

/-- `φ = ψ * ψ` is smooth. -/
theorem d1e_phi_smooth {ψ : Euc d → ℝ} (hψ : IsFDLProfile ψ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fdlPhi ψ) := by
  unfold fdlPhi
  exact (d1e_psi_compact hψ).contDiff_convolution_left (ContinuousLinearMap.mul ℝ ℝ) hψ.smooth
    hψ.smooth.continuous.locallyIntegrable

theorem d1e_phi_cont {ψ : Euc d → ℝ} (hψ : IsFDLProfile ψ) : Continuous (fdlPhi ψ) :=
  (d1e_phi_smooth hψ).continuous

/-- `φ(0) = ∫ ψ² > 0`. -/
theorem d1e_phi_zero_pos {ψ : Euc d → ℝ} (hψ : IsFDLProfile ψ) : 0 < fdlPhi ψ 0 := by
  have hcont : Continuous (fun t : Euc d => ψ t * ψ t) := hψ.smooth.continuous.mul hψ.smooth.continuous
  have hcs : HasCompactSupport (fun t : Euc d => ψ t * ψ t) := (d1e_psi_compact hψ).mul_right
  have hint : Integrable (fun t : Euc d => ψ t * ψ t) :=
    hcont.integrable_of_hasCompactSupport hcs
  have hsq : fdlPhi ψ 0 = ∫ t : Euc d, ψ t * ψ t := by
    unfold fdlPhi
    rw [convolution_def]
    congr 1
    funext t
    simp only [ContinuousLinearMap.mul_apply', zero_sub]
    rw [hψ.radial (-t) t (norm_neg t)]
  rw [hsq, integral_pos_iff_support_of_nonneg (fun t => mul_self_nonneg _) hint]
  refine lt_of_lt_of_le (Metric.measure_ball_pos volume (0 : Euc d) (by norm_num : (0 : ℝ) < 1 / 4))
    (measure_mono ?_)
  intro t ht
  have hpos : 0 < ψ t := hψ.pos t (by simpa using ht)
  show t ∈ Function.support (fun t : Euc d => ψ t * ψ t)
  simp only [Function.mem_support]
  exact (mul_self_pos.2 hpos.ne').ne'

/-- `φ` is bounded. -/
theorem d1e_phi_bdd {ψ : Euc d → ℝ} (hψ : IsFDLProfile ψ) : ∃ M : ℝ, ∀ y, ‖fdlPhi ψ y‖ ≤ M := by
  have hcs : HasCompactSupport (fdlPhi ψ) := by
    refine HasCompactSupport.intro (isCompact_closedBall (0 : Euc d) 1) (fun y hy => ?_)
    refine d1e_phi_zero_of_norm hψ ?_
    exact (not_le.mp (fun h => hy (mem_closedBall_zero_iff.2 h))).le
  exact (d1e_phi_cont hψ).bounded_above_of_compact_support hcs

/-- `φ` is Lipschitz at `0` on the unit ball. -/
theorem d1e_phi_lip {ψ : Euc d → ℝ} (hψ : IsFDLProfile ψ) :
    ∃ L : ℝ, ∀ y : Euc d, ‖y‖ ≤ 1 → ‖fdlPhi ψ y - fdlPhi ψ 0‖ ≤ L * ‖y‖ := by
  have hsm := d1e_phi_smooth hψ
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : Euc d) 1).exists_bound_of_continuousOn
    (f := fun y => fderiv ℝ (fdlPhi ψ) y)
    ((hsm.continuous_fderiv (by simp)).continuousOn)
  refine ⟨max C 0, fun y hy => ?_⟩
  have h0 : (0 : Euc d) ∈ Metric.closedBall (0 : Euc d) 1 := Metric.mem_closedBall_self zero_le_one
  have hy' : y ∈ Metric.closedBall (0 : Euc d) 1 := mem_closedBall_zero_iff.2 hy
  have := (convex_closedBall (0 : Euc d) 1).norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ)
    (f := fdlPhi ψ) (C := max C 0)
    (fun x _ => (hsm.differentiable (by simp)) x)
    (fun x hx => le_trans (hC x hx) (le_max_left _ _)) h0 hy'
  simpa [sub_zero] using this

/-- Pointwise form of the integrand of `IsFDLConst` for `t > 0` and a unit vector `e`:
`t^{d-s} φ_t(x) / t = t^{-s-1} φ((‖x‖/t) e)` (radiality of `φ`). -/
theorem d1e_integrand_eq {ψ : Euc d → ℝ} (hψ : IsFDLProfile ψ) {s t : ℝ} (x e : Euc d)
    (he : ‖e‖ = 1) (ht : 0 < t) :
    t ^ ((d : ℝ) - s) * fdlPhiScale ψ t x / t = t ^ (-s - 1) * fdlPhi ψ ((‖x‖ / t) • e) := by
  unfold fdlPhiScale
  have hn1 : ‖t⁻¹ • x‖ = ‖x‖ / t := by
    rw [norm_smul, norm_inv, Real.norm_of_nonneg ht.le, div_eq_inv_mul]
  have hn2 : ‖(‖x‖ / t) • e‖ = ‖x‖ / t := by
    rw [norm_smul, he, mul_one, Real.norm_of_nonneg (div_nonneg (norm_nonneg x) ht.le)]
  have hφ : fdlPhi ψ (t⁻¹ • x) = fdlPhi ψ ((‖x‖ / t) • e) :=
    d1e_phi_radial hψ (by rw [hn1, hn2])
  rw [hφ]
  have hd : t ^ ((d : ℝ) - s) = t ^ d * t ^ (-s) := by
    rw [sub_eq_add_neg, Real.rpow_add ht, Real.rpow_natCast]
  rw [hd, Real.rpow_sub_one ht.ne']
  have htd : t ^ d ≠ 0 := pow_ne_zero _ ht.ne'
  field_simp

/-- Rewriting the `s = 0` integrand. -/
theorem d1e_integrand_eq_zero {ψ : Euc d → ℝ} (hψ : IsFDLProfile ψ) (x e : Euc d)
    (he : ‖e‖ = 1) {t : ℝ} (ht : 0 < t) :
    t ^ ((d : ℝ) - 0) * fdlPhiScale ψ t x / t = t⁻¹ * fdlPhi ψ ((‖x‖ / t) • e) := by
  rw [d1e_integrand_eq hψ x e he ht, show (-(0:ℝ) - 1) = -1 by ring, Real.rpow_neg_one]

/-- One-dimensional change of variables `u = r/t` on `(0,∞)` for the `s > 0` integrand. -/
theorem d1e_subst_pos (P : ℝ → ℝ) {r s : ℝ} (hr : 0 < r)
    (hint : IntegrableOn (fun u : ℝ => u ^ (s - 1) * P u) (Ioi 0)) :
    IntegrableOn (fun t : ℝ => t ^ (-s - 1) * P (r / t)) (Ioi 0) ∧
      ∫ t in Ioi (0 : ℝ), t ^ (-s - 1) * P (r / t) =
        r ^ (-s) * ∫ u in Ioi (0 : ℝ), u ^ (s - 1) * P u := by
  have hderiv : ∀ t ∈ Ioi (0 : ℝ),
      HasDerivWithinAt (fun t : ℝ => r * t⁻¹) (r * -(t ^ 2)⁻¹) (Ioi 0) t := fun t ht =>
    ((hasDerivAt_inv (ne_of_gt (show (0 : ℝ) < t from ht))).const_mul r).hasDerivWithinAt
  have hinj : InjOn (fun t : ℝ => r * t⁻¹) (Ioi 0) := by
    intro a _ b _ hab
    simpa [hr.ne'] using hab
  have himage : (fun t : ℝ => r * t⁻¹) '' Ioi 0 = Ioi 0 := by
    ext u
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact mul_pos hr (inv_pos.2 ht)
    · intro hu
      refine ⟨r * u⁻¹, mul_pos hr (inv_pos.2 hu), ?_⟩
      have hu' : u ≠ 0 := ne_of_gt hu
      field_simp
  set H : ℝ → ℝ := fun u => r ^ (-s) * (u ^ (s - 1) * P u) with hH
  have hHint : IntegrableOn H (Ioi 0) := hint.const_mul (r ^ (-s))
  have hsub := integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi hderiv hinj H
  have hsub2 := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hderiv hinj H
  rw [himage] at hsub hsub2
  have hpt : EqOn (fun t : ℝ => |r * -(t ^ 2)⁻¹| • H (r * t⁻¹))
      (fun t : ℝ => t ^ (-s - 1) * P (r / t)) (Ioi 0) := by
    intro t ht
    have ht' : (0 : ℝ) < t := ht
    simp only [hH, smul_eq_mul]
    have habs : |r * -(t ^ 2)⁻¹| = r * (t ^ 2)⁻¹ := by
      rw [mul_neg, abs_neg, abs_of_pos (mul_pos hr (inv_pos.2 (pow_pos ht' 2)))]
    rw [habs, div_eq_mul_inv]
    have e1 : (r * t⁻¹) ^ (s - 1) = r ^ (s - 1) * (t ^ (s - 1))⁻¹ := by
      rw [Real.mul_rpow hr.le (inv_nonneg.2 ht'.le), Real.inv_rpow ht'.le]
    have e2 : r ^ (-s) * r ^ (s - 1) = r⁻¹ := by
      rw [← Real.rpow_add hr, show -s + (s - 1) = -1 by ring, Real.rpow_neg_one]
    have e3 : t ^ (-s - 1) = (t ^ (s - 1))⁻¹ * (t ^ 2)⁻¹ := by
      rw [show -s - 1 = -(s - 1) - 2 by ring, Real.rpow_sub ht', Real.rpow_neg ht'.le,
        show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      rw [div_eq_mul_inv]
    rw [e1, e3]
    calc r * (t ^ 2)⁻¹ * (r ^ (-s) * (r ^ (s - 1) * (t ^ (s - 1))⁻¹ * P (r * t⁻¹)))
        = r * (t ^ 2)⁻¹ * ((r ^ (-s) * r ^ (s - 1)) * ((t ^ (s - 1))⁻¹ * P (r * t⁻¹))) := by
          ring
      _ = (t ^ (s - 1))⁻¹ * (t ^ 2)⁻¹ * P (r * t⁻¹) := by
          rw [e2]
          field_simp
  have hG : IntegrableOn (fun t : ℝ => t ^ (-s - 1) * P (r / t)) (Ioi 0) :=
    (hsub.1 hHint).congr_fun hpt measurableSet_Ioi
  refine ⟨hG, ?_⟩
  rw [← setIntegral_congr_fun measurableSet_Ioi hpt, ← hsub2]
  exact integral_const_mul (r ^ (-s)) (fun u => u ^ (s - 1) * P u)

/-- Integrability of `u^{s-1} P(u)` on `(0,∞)` for `s > 0` (`P` continuous, bounded, zero on `[1,∞)`). -/
theorem d1e_oneD_int_pos {P : ℝ → ℝ} (hPc : Continuous P) (hP1 : ∀ u, 1 ≤ u → P u = 0)
    {M : ℝ} (hM : ∀ u, ‖P u‖ ≤ M) {s : ℝ} (hs : 0 < s) :
    IntegrableOn (fun u : ℝ => u ^ (s - 1) * P u) (Ioi 0) := by
  have hI1 : IntegrableOn (fun u : ℝ => u ^ (s - 1) * P u) (Ioc 0 1) := by
    have hpow : IntegrableOn (fun u : ℝ => u ^ (s - 1)) (Ioc 0 1) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).1
        (intervalIntegral.intervalIntegrable_rpow' (by linarith))
    refine Integrable.mono' (hpow.const_mul M) ?_ ?_
    · exact (by fun_prop : Measurable fun u : ℝ => u ^ (s - 1) * P u).aestronglyMeasurable
    · refine ae_restrict_of_forall_mem measurableSet_Ioc (fun u hu => ?_)
      rw [norm_mul, Real.norm_of_nonneg (Real.rpow_nonneg hu.1.le _), mul_comm (u ^ (s - 1))]
      exact mul_le_mul_of_nonneg_right (hM u) (Real.rpow_nonneg hu.1.le _)
  have hI2 : IntegrableOn (fun u : ℝ => u ^ (s - 1) * P u) (Ioi 1) := by
    refine (integrableOn_zero (μ := (volume : Measure ℝ)) (s := Ioi (1 : ℝ))).congr_fun
      (fun u hu => ?_) measurableSet_Ioi
    simp only [hP1 u (le_of_lt hu), mul_zero]
  have := hI1.union hI2
  rwa [Ioc_union_Ioi_eq_Ioi zero_le_one] at this

/-- Positivity of `∫_{(0,∞)} u^{s-1} P(u)` for `s > 0` when `P ≥ 0` and `P(0) > 0`. -/
theorem d1e_oneD_val_pos {P : ℝ → ℝ} (hPc : Continuous P) (hPnn : ∀ u, 0 ≤ P u) (hP0 : 0 < P 0)
    {s : ℝ} (hint : IntegrableOn (fun u : ℝ => u ^ (s - 1) * P u) (Ioi 0)) :
    0 < ∫ u in Ioi (0 : ℝ), u ^ (s - 1) * P u := by
  rw [setIntegral_pos_iff_support_of_nonneg_ae
    (ae_restrict_of_forall_mem measurableSet_Ioi
      (fun u hu => mul_nonneg (Real.rpow_nonneg (le_of_lt hu) _) (hPnn u))) hint]
  obtain ⟨ε, hε, hεP⟩ : ∃ ε > 0, ∀ y : ℝ, dist y 0 < ε → 0 < P y :=
    Metric.eventually_nhds_iff.1 ((hPc.tendsto 0).eventually (lt_mem_nhds hP0))
  refine lt_of_lt_of_le (?_ : 0 < volume (Ioo (0 : ℝ) ε)) (measure_mono ?_)
  · rw [Real.volume_Ioo]
    exact ENNReal.ofReal_pos.2 (by linarith)
  · intro u hu
    have hu0 : 0 < u := hu.1
    have huε : u < ε := hu.2
    refine ⟨Function.mem_support.2 ?_, hu0⟩
    have hpos : 0 < P u := hεP u (by rw [Real.dist_eq, sub_zero, abs_of_pos hu0]; exact huε)
    exact (mul_pos (Real.rpow_pos_of_pos hu0 _) hpos).ne'

/-- The `s = 0` one-dimensional statement: the renormalised integral `∫_{(0,R]} t⁻¹ P(r/t)` equals
`P(0) log R + Q - P(0) log r + o(1)` for a constant `Q` depending only on `P`. -/
theorem d1e_oneD_zero {P : ℝ → ℝ} (hPc : Continuous P) (hP1 : ∀ u, 1 ≤ u → P u = 0)
    (hM : ∃ M : ℝ, ∀ u, ‖P u‖ ≤ M) (hL : ∃ L : ℝ, ∀ u : ℝ, ‖u‖ ≤ 1 → ‖P u - P 0‖ ≤ L * ‖u‖) :
    ∃ Q : ℝ,
      (∀ r : ℝ, 0 < r → ∀ R : ℝ, 0 < R →
        IntegrableOn (fun t : ℝ => t⁻¹ * P (r / t)) (Ioc 0 R)) ∧
      ∀ r : ℝ, 0 < r → Tendsto (fun R : ℝ => (∫ t in Ioc (0 : ℝ) R, t⁻¹ * P (r / t))
        - P 0 * Real.log R) atTop (𝓝 (Q - P 0 * Real.log r)) := by
  obtain ⟨M, hM⟩ := hM
  obtain ⟨L, hL⟩ := hL
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM 0)
  have hq_bdd : ∀ u : ℝ, 0 < u → u ≤ 1 → ‖(P u - P 0) / u‖ ≤ L := by
    intro u hu0 hu1
    rw [norm_div, Real.norm_of_nonneg hu0.le, div_le_iff₀ hu0]
    have := hL u (by rw [Real.norm_of_nonneg hu0.le]; exact hu1)
    rw [Real.norm_of_nonneg hu0.le] at this
    exact this
  have hq_meas : Measurable fun u : ℝ => (P u - P 0) / u := by fun_prop
  have hq_int : ∀ c : ℝ, 0 < c → c ≤ 1 →
      IntervalIntegrable (fun u : ℝ => (P u - P 0) / u) volume 0 c := by
    intro c hc0 hc1
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hc0.le]
    refine Measure.integrableOn_of_bounded (M := L) measure_Ioc_lt_top.ne
      hq_meas.aestronglyMeasurable ?_
    exact ae_restrict_of_forall_mem measurableSet_Ioc (fun u hu => hq_bdd u hu.1 (le_trans hu.2 hc1))
  set Q : ℝ := ∫ u in (0 : ℝ)..1, (P u - P 0) / u with hQ
  have hsmall : ∀ a : ℝ, 0 < a → a ≤ 1 →
      ‖∫ u in (0 : ℝ)..a, (P u - P 0) / u‖ ≤ L * a := by
    intro a ha0 ha1
    have hb : ∀ u ∈ Set.uIoc (0 : ℝ) a, ‖(P u - P 0) / u‖ ≤ L := by
      intro u hu
      rw [Set.uIoc_of_le ha0.le] at hu
      exact hq_bdd u hu.1 (le_trans hu.2 ha1)
    have h := intervalIntegral.norm_integral_le_of_norm_le_const hb
    rw [sub_zero, abs_of_pos ha0] at h
    exact h
  have hsplit : ∀ a : ℝ, 0 < a → a ≤ 1 →
      ∫ u in a..1, (P u - P 0) / u = Q - ∫ u in (0 : ℝ)..a, (P u - P 0) / u := by
    intro a ha0 ha1
    rw [hQ]
    exact (intervalIntegral.integral_interval_sub_left (hq_int 1 one_pos le_rfl)
      (hq_int a ha0 ha1)).symm
  have hsub01 : ∀ a : ℝ, 0 < a → a ≤ 1 → uIcc a 1 ⊆ uIcc (0 : ℝ) 1 := by
    intro a ha0 ha1
    exact Set.uIcc_subset_uIcc (Set.mem_uIcc.2 (Or.inl ⟨ha0.le, ha1⟩))
      (Set.mem_uIcc.2 (Or.inl ⟨zero_le_one, le_rfl⟩))
  have hkey : ∀ a : ℝ, 0 < a → a ≤ 1 →
      ∫ u in a..1, P u / u = (∫ u in a..1, (P u - P 0) / u) - P 0 * Real.log a := by
    intro a ha0 ha1
    have hcongr : ∫ u in a..1, P u / u = ∫ u in a..1, ((P u - P 0) / u + P 0 * u⁻¹) :=
      intervalIntegral.integral_congr (fun u _ => by ring)
    have h1 : IntervalIntegrable (fun u : ℝ => (P u - P 0) / u) volume a 1 :=
      (hq_int 1 one_pos le_rfl).mono_set (hsub01 a ha0 ha1)
    have h2 : IntervalIntegrable (fun u : ℝ => P 0 * u⁻¹) volume a 1 := by
      refine IntervalIntegrable.const_mul ?_ (P 0)
      refine intervalIntegral.intervalIntegrable_inv (fun x hx => ?_) continuousOn_id
      rw [uIcc_of_le ha1] at hx
      exact (lt_of_lt_of_le ha0 hx.1).ne'
    rw [hcongr, intervalIntegral.integral_add h1 h2, intervalIntegral.integral_const_mul,
      integral_inv_of_pos ha0 one_pos, one_div, Real.log_inv]
    ring
  -- substitution `u = r/t` on `[r, R]`
  have hF : ∀ r : ℝ, 0 < r → ∀ R : ℝ, r < R →
      ∫ t in Ioc (0 : ℝ) R, t⁻¹ * P (r / t) = ∫ u in (r / R)..1, P u / u := by
    intro r hr R hrR
    have hR0 : 0 < R := lt_trans hr hrR
    have h1 : ∫ t in Ioc (0 : ℝ) R, t⁻¹ * P (r / t) = ∫ t in Ioc r R, t⁻¹ * P (r / t) := by
      apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioc
      · exact Ioc_subset_Ioc hr.le le_rfl
      · intro t ht
        have ht' : t ≤ r := by
          by_contra hcon
          exact ht.2 ⟨not_le.mp hcon, ht.1.2⟩
        have hpos : 0 < t := ht.1.1
        have hP : P (r / t) = 0 := hP1 _ ((one_le_div hpos).2 ht')
        simp [hP]
    have hxpos : ∀ x ∈ uIcc r R, 0 < x := fun x hx => by
      rw [uIcc_of_le hrR.le] at hx
      exact lt_of_lt_of_le hr hx.1
    have hgc : ContinuousOn (fun u : ℝ => -(P u / u)) (Ioi 0) :=
      (hPc.continuousOn.div continuousOn_id (fun u hu => ne_of_gt hu)).neg
    have hcomp := intervalIntegral.integral_comp_mul_deriv' (a := r) (b := R)
      (f := fun t : ℝ => r * t⁻¹) (f' := fun t : ℝ => r * -(t ^ 2)⁻¹)
      (g := fun u : ℝ => -(P u / u))
      (fun x hx => ((hasDerivAt_inv (ne_of_gt (hxpos x hx))).const_mul r))
      (ContinuousOn.mul continuousOn_const (ContinuousOn.neg (ContinuousOn.inv₀
        ((continuous_pow 2).continuousOn) (fun x hx => pow_ne_zero 2 (hxpos x hx).ne'))))
      (hgc.mono (by
        rintro _ ⟨x, hx, rfl⟩
        exact mul_pos hr (inv_pos.2 (hxpos x hx))))
    have hLHS : ∫ t in r..R, t⁻¹ * P (r / t) =
        ∫ t in r..R, ((fun u : ℝ => -(P u / u)) ∘ (fun t : ℝ => r * t⁻¹)) t *
          (r * -(t ^ 2)⁻¹) := by
      refine intervalIntegral.integral_congr (fun x hx => ?_)
      have hx0 : 0 < x := hxpos x hx
      simp only [Function.comp_apply]
      rw [show r / x = r * x⁻¹ from div_eq_mul_inv r x]
      field_simp
    rw [h1, ← intervalIntegral.integral_of_le hrR.le, hLHS, hcomp, mul_inv_cancel₀ hr.ne',
      ← div_eq_mul_inv, intervalIntegral.integral_neg, intervalIntegral.integral_symm (r / R) 1,
      neg_neg]
  refine ⟨Q, ?_, ?_⟩
  · intro r hr R _
    refine Measure.integrableOn_of_bounded (M := M * r⁻¹) measure_Ioc_lt_top.ne
      (by fun_prop : Measurable fun t : ℝ => t⁻¹ * P (r / t)).aestronglyMeasurable ?_
    refine ae_restrict_of_forall_mem measurableSet_Ioc (fun t ht => ?_)
    rcases le_total t r with htr | htr
    · have hP : P (r / t) = 0 := hP1 _ ((one_le_div ht.1).2 htr)
      rw [hP, mul_zero, norm_zero]
      exact mul_nonneg hM0 (inv_nonneg.2 hr.le)
    · rw [norm_mul, Real.norm_of_nonneg (inv_nonneg.2 ht.1.le), mul_comm M]
      exact mul_le_mul (inv_anti₀ hr htr) (hM _) (norm_nonneg _) (inv_nonneg.2 hr.le)
  · intro r hr
    have hlim : Tendsto (fun R : ℝ => ∫ u in (0 : ℝ)..(r / R), (P u - P 0) / u) atTop (𝓝 0) := by
      refine squeeze_zero_norm' (a := fun R : ℝ => L * (r / R)) ?_ ?_
      · filter_upwards [eventually_gt_atTop r] with R hR
        have hR0 : 0 < R := lt_trans hr hR
        have ha0 : 0 < r / R := div_pos hr hR0
        have ha1 : r / R ≤ 1 := by rw [div_le_one hR0]; exact hR.le
        exact hsmall (r / R) ha0 ha1
      · have := ((tendsto_const_nhds (x := r)).div_atTop tendsto_id).const_mul L
        simpa using this
    have hev : ∀ᶠ R : ℝ in atTop, (∫ t in Ioc (0 : ℝ) R, t⁻¹ * P (r / t)) - P 0 * Real.log R
        = (Q - P 0 * Real.log r) - ∫ u in (0 : ℝ)..(r / R), (P u - P 0) / u := by
      filter_upwards [eventually_gt_atTop r] with R hR
      have hR0 : 0 < R := lt_trans hr hR
      have ha0 : 0 < r / R := div_pos hr hR0
      have ha1 : r / R ≤ 1 := by rw [div_le_one hR0]; exact hR.le
      rw [hF r hr R hR, hkey (r / R) ha0 ha1, hsplit (r / R) ha0 ha1, Real.log_div hr.ne' hR0.ne']
      ring
    have hfin : Tendsto (fun R : ℝ => (Q - P 0 * Real.log r)
        - ∫ u in (0 : ℝ)..(r / R), (P u - P 0) / u) atTop (𝓝 ((Q - P 0 * Real.log r) - 0)) :=
      tendsto_const_nhds.sub hlim
    rw [sub_zero] at hfin
    exact Tendsto.congr' (Filter.EventuallyEq.symm hev) hfin

/-- A fixed unit vector of `ℝ^d` (needs `1 ≤ d`). -/
theorem d1e_unit (hd : 1 ≤ d) : ∃ e : Euc d, ‖e‖ = 1 :=
  ⟨EuclideanSpace.single (⟨0, hd⟩ : Fin d) (1 : ℝ), by simp⟩

/-- Lemma D.1, Euclidean clause for `0 < s` (helper `d1e_pos`).  There is `b > 0` such that, for every
`x ≠ 0`, the integral `∫_0^∞ t^{d-s} φ_t(x) dt/t` converges absolutely and `g(x) = b` times it. -/
theorem d1e_pos (hd : 1 ≤ d) {s : ℝ} (_hs0 : 0 ≤ s) (_hsd : s < d) {ψ : Euc d → ℝ}
    (hψ : IsFDLProfile ψ) (hs : 0 < s) :
    ∃ b : ℝ, 0 < b ∧ ∀ x : Euc d, x ≠ 0 →
      IntegrableOn (fun t : ℝ => t ^ ((d : ℝ) - s) * fdlPhiScale ψ t x / t) (Set.Ioi 0) ∧
      Whole.rieszKernel d s x =
        b * ∫ t in Set.Ioi (0 : ℝ), t ^ ((d : ℝ) - s) * fdlPhiScale ψ t x / t := by
  obtain ⟨e, he⟩ := d1e_unit hd
  set P : ℝ → ℝ := fun u => fdlPhi ψ (u • e) with hP
  have hPc : Continuous P := (d1e_phi_cont hψ).comp (continuous_id.smul continuous_const)
  have hPnn : ∀ u, 0 ≤ P u := fun u => d1e_phi_nonneg hψ _
  have hP1 : ∀ u, 1 ≤ u → P u = 0 := fun u hu => by
    refine d1e_phi_zero_of_norm hψ ?_
    rw [norm_smul, he, mul_one, Real.norm_of_nonneg (by linarith)]
    exact hu
  have hP0eq : P 0 = fdlPhi ψ 0 := by
    show fdlPhi ψ (0 • e) = _
    rw [zero_smul]
  have hP0 : 0 < P 0 := by rw [hP0eq]; exact d1e_phi_zero_pos hψ
  obtain ⟨M, hM⟩ := d1e_phi_bdd hψ
  have hPM : ∀ u, ‖P u‖ ≤ M := fun u => hM _
  have hint := d1e_oneD_int_pos hPc hP1 hPM hs
  have hpos := d1e_oneD_val_pos hPc hPnn hP0 hint
  refine ⟨(∫ u in Set.Ioi (0 : ℝ), u ^ (s - 1) * P u)⁻¹, inv_pos.2 hpos, fun x hx => ?_⟩
  have hr : 0 < ‖x‖ := norm_pos_iff.2 hx
  have hG : Set.EqOn (fun t : ℝ => t ^ ((d : ℝ) - s) * fdlPhiScale ψ t x / t)
      (fun t : ℝ => t ^ (-s - 1) * P (‖x‖ / t)) (Set.Ioi 0) :=
    fun t ht => d1e_integrand_eq hψ x e he ht
  obtain ⟨hint2, hval⟩ := d1e_subst_pos P hr hint
  have hint3 : IntegrableOn (fun t : ℝ => t ^ ((d : ℝ) - s) * fdlPhiScale ψ t x / t) (Set.Ioi 0) :=
    hint2.congr_fun hG.symm measurableSet_Ioi
  refine ⟨hint3, ?_⟩
  rw [setIntegral_congr_fun measurableSet_Ioi hG, hval]
  have hne : (∫ u in Set.Ioi (0 : ℝ), u ^ (s - 1) * P u) ≠ 0 := hpos.ne'
  unfold Whole.rieszKernel
  simp only [hs.ne', ite_false]
  field_simp

/-- Lemma D.1, renormalised Euclidean clause for `s = 0` (helper `d1e_zero`).  With
`b = 1/φ(0)` (so that `b φ(0) = 1`) there is `C` such that for every `x ≠ 0` the truncated integrals
`∫_{(0,R]} t^{d} φ_t(x) dt/t - φ(0) log R` converge to `(g(x) - C)/b`, `g(x) = -log|x|`. -/
theorem d1e_zero (hd : 1 ≤ d) {s : ℝ} (_hs0 : 0 ≤ s) (_hsd : s < d) {ψ : Euc d → ℝ}
    (hψ : IsFDLProfile ψ) (hs : s = 0) :
    ∃ b : ℝ, 0 < b ∧ b * fdlPhi ψ 0 = 1 ∧ ∃ C : ℝ, ∀ x : Euc d, x ≠ 0 →
      (∀ R : ℝ, 0 < R →
        IntegrableOn (fun t : ℝ => t ^ ((d : ℝ) - s) * fdlPhiScale ψ t x / t) (Set.Ioc 0 R)) ∧
      Tendsto (fun R : ℝ =>
          (∫ t in Set.Ioc (0 : ℝ) R, t ^ ((d : ℝ) - s) * fdlPhiScale ψ t x / t)
            - fdlPhi ψ 0 * Real.log R) atTop
        (𝓝 ((Whole.rieszKernel d s x - C) / b)) := by
  subst hs
  obtain ⟨e, he⟩ := d1e_unit hd
  set P : ℝ → ℝ := fun u => fdlPhi ψ (u • e) with hP
  have hPc : Continuous P := (d1e_phi_cont hψ).comp (continuous_id.smul continuous_const)
  have hP1 : ∀ u, 1 ≤ u → P u = 0 := fun u hu => by
    refine d1e_phi_zero_of_norm hψ ?_
    rw [norm_smul, he, mul_one, Real.norm_of_nonneg (by linarith)]
    exact hu
  have hP0eq : P 0 = fdlPhi ψ 0 := by
    show fdlPhi ψ (0 • e) = _
    rw [zero_smul]
  have hP0 : 0 < P 0 := by rw [hP0eq]; exact d1e_phi_zero_pos hψ
  have hne : P 0 ≠ 0 := hP0.ne'
  obtain ⟨M, hM⟩ := d1e_phi_bdd hψ
  have hPM : ∃ M : ℝ, ∀ u, ‖P u‖ ≤ M := ⟨M, fun u => hM _⟩
  obtain ⟨L, hLφ⟩ := d1e_phi_lip hψ
  have hLP : ∃ L : ℝ, ∀ u : ℝ, ‖u‖ ≤ 1 → ‖P u - P 0‖ ≤ L * ‖u‖ := by
    refine ⟨L, fun u hu => ?_⟩
    have h1 := hLφ (u • e) (by rw [norm_smul, he, mul_one]; exact hu)
    rw [norm_smul, he, mul_one] at h1
    show ‖fdlPhi ψ (u • e) - fdlPhi ψ (0 • e)‖ ≤ _
    rw [zero_smul]
    exact h1
  obtain ⟨Q, hint, hlim⟩ := d1e_oneD_zero hPc hP1 hPM hLP
  refine ⟨(P 0)⁻¹, inv_pos.2 hP0, ?_, -(Q / P 0), fun x hx => ?_⟩
  · rw [← hP0eq]
    exact inv_mul_cancel₀ hne
  have hr : 0 < ‖x‖ := norm_pos_iff.2 hx
  have hG : ∀ R : ℝ, ∫ t in Set.Ioc (0 : ℝ) R, t ^ ((d : ℝ) - 0) * fdlPhiScale ψ t x / t =
      ∫ t in Set.Ioc (0 : ℝ) R, t⁻¹ * P (‖x‖ / t) := fun R =>
    setIntegral_congr_fun measurableSet_Ioc
      (fun t ht => d1e_integrand_eq_zero hψ x e he ht.1)
  refine ⟨fun R hR => ?_, ?_⟩
  · have hE : Set.EqOn (fun t : ℝ => t ^ ((d : ℝ) - 0) * fdlPhiScale ψ t x / t)
        (fun t : ℝ => t⁻¹ * P (‖x‖ / t)) (Set.Ioc 0 R) :=
      fun t ht => d1e_integrand_eq_zero hψ x e he ht.1
    exact (hint _ hr R hR).congr_fun hE.symm measurableSet_Ioc
  · have hlimval : (Whole.rieszKernel d 0 x - -(Q / P 0)) / (P 0)⁻¹ = Q - P 0 * Real.log ‖x‖ := by
      rw [show Whole.rieszKernel d 0 x = -Real.log ‖x‖ from by
        unfold Whole.rieszKernel; simp]
      field_simp
      ring
    rw [hlimval, ← hP0eq]
    refine Tendsto.congr (fun R => ?_) (hlim ‖x‖ hr)
    rw [hG R]

end HRS.MC.D1E
