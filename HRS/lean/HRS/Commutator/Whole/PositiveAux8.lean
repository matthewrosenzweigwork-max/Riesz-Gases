import HRS.Commutator.Whole.PositiveAux7

/-!
# Helpers for `Positive.lean` (packet `CMX-POS`), part H

The quadratic form of `g_1` on finite compactly supported signed measures.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform ContDiff

namespace HRS.Commutator.Whole

open HRS HRS.Whole

variable {d : ℕ} {s : ℝ}

lemma g1_mix_pos (hs : 0 < s) (hs2 : s < 2 * (d : ℝ) + 4) (z : Euc d) :
    g1 s z = ∫ t, (cPhi d s * t ^ (-s - 1)) * phi (t⁻¹ • z) ∂(volume.restrict (Set.Ioi (1:ℝ))) := by
  rw [g1_repr_pos hs hs2, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
  have ht0 : 0 < t := lt_trans one_pos ht
  rw [phi_smul_eq ht0]; ring

lemma g1Hat_mix (s : ℝ) (ξ : Euc d) :
    g1Hat s ξ = ∫ t, (cPhi d s * t ^ (-s - 1)) * (t ^ d * phiHatR d (t * ‖ξ‖))
      ∂(volume.restrict (Set.Ioi (1:ℝ))) := by
  rw [g1Hat_eq, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
  have ht0 : 0 < t := lt_trans one_pos ht
  have : t ^ (-s - 1) * t ^ d = t ^ ((d : ℝ) - s - 1) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add ht0]; congr 1; ring
  calc cPhi d s * (t ^ ((d : ℝ) - s - 1) * phiHatR d (t * ‖ξ‖))
      = cPhi d s * ((t ^ (-s - 1) * t ^ d) * phiHatR d (t * ‖ξ‖)) := by rw [this]
    _ = _ := by ring

lemma integrableOn_Ioi_one_rpow {a : ℝ} (ha : a < -1) :
    IntegrableOn (fun t : ℝ => t ^ a) (Set.Ioi 1) := integrableOn_Ioi_rpow_of_lt ha one_pos

lemma measurable_g1_mix_pos (hs : 0 < s) (hs2 : s < 2 * (d : ℝ) + 4) : Measurable (g1 s : Euc d → ℝ) := by
  have e : (g1 s : Euc d → ℝ) = fun z => ∫ t, (cPhi d s * t ^ (-s - 1)) * phi (t⁻¹ • z)
      ∂(volume.restrict (Set.Ioi (1:ℝ))) := funext (g1_mix_pos hs hs2)
  rw [e]
  have hF : Measurable (fun q : Euc d × ℝ => (cPhi d s * q.2 ^ (-s - 1)) * phi (q.2⁻¹ • q.1)) := by
    have := continuous_phi (d := d)
    fun_prop
  exact (hF.stronglyMeasurable.integral_prod_right (ν := volume.restrict (Set.Ioi (1:ℝ)))).measurable

lemma abs_g1_le_pos (hs : 0 < s) (hs2 : s < 2 * (d : ℝ) + 4) (z : Euc d) : |g1 s z| ≤ cPhi d s / s := by
  have hcp := cPhi_pos d hs.le hs2
  rw [g1_mix_pos hs hs2]
  have hI : IntegrableOn (fun t : ℝ => cPhi d s * t ^ (-s - 1)) (Set.Ioi 1) :=
    (integrableOn_Ioi_one_rpow (by linarith)).const_mul _
  have h1 := norm_integral_le_of_norm_le (μ := volume.restrict (Set.Ioi (1:ℝ)))
    (f := fun t => (cPhi d s * t ^ (-s - 1)) * phi (t⁻¹ • z)) (g := fun t => cPhi d s * t ^ (-s - 1)) hI
    (by
      filter_upwards [self_mem_ae_restrict (measurableSet_Ioi (a := (1:ℝ)))] with t ht
      have ht0 : 0 < t := lt_trans one_pos ht
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity)]
      exact mul_le_of_le_one_right (by positivity) (abs_phi_le_one _))
  rw [Real.norm_eq_abs] at h1
  refine h1.trans (le_of_eq ?_)
  rw [integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) one_pos]
  have : -s - 1 + 1 = -s := by ring
  rw [this, Real.one_rpow]
  field_simp


theorem quadForm_g1_pos (hs : 0 < s) (hsd : s < (d : ℝ) - 2) (σ : SMeas d) (hf : σ.IsFinite) :
    Integrable (fun ξ : Euc d => g1Hat s ξ * ‖σ.fourier ξ‖ ^ 2) ∧
      kerEnergy (g1 s) σ = ∫ ξ, g1Hat s ξ * ‖σ.fourier ξ‖ ^ 2 := by
  have hs2 : s < 2 * (d : ℝ) + 4 := by linarith [(Nat.cast_nonneg d : (0:ℝ) ≤ d)]
  have hcp := cPhi_pos d hs.le hs2
  obtain ⟨m, h, hr⟩ := σ.exists_repr hf
  haveI := hr.fin
  set ν : Measure ℝ := volume.restrict (Set.Ioi (1:ℝ)) with hν
  set c : ℝ → ℝ := fun t => cPhi d s * t ^ (-s - 1) with hc
  have hcm : Measurable c := by unfold c; fun_prop
  have hν0 : ∀ᵐ t ∂ν, 0 < t := by
    filter_upwards [self_mem_ae_restrict (measurableSet_Ioi (a := (1:ℝ)))] with t ht using lt_trans one_pos ht
  have hc0 : ∀ᵐ t ∂ν, 0 ≤ c t := by
    filter_upwards [hν0] with t ht
    exact mul_nonneg hcp.le (Real.rpow_nonneg ht.le _)
  have hint : Integrable (fun t => c t * ∫ p : Euc d × Euc d, phi (t⁻¹ • (p.1 - p.2)) ∂(m.prod m)) ν := by
    have h2 : Integrable (fun t : ℝ => (m.real Set.univ * m.real Set.univ) * c t) ν :=
      (((integrableOn_Ioi_one_rpow (a := -s - 1) (by linarith)).const_mul (cPhi d s)).const_mul
        (m.real Set.univ * m.real Set.univ)).congr (Filter.Eventually.of_forall fun t => by simp only [c])
    refine h2.mono' ((hcm.mul (measurable_pair_int m)).aestronglyMeasurable) ?_
    filter_upwards [hν0] with t ht
    have hnn : 0 ≤ ∫ p : Euc d × Euc d, phi (t⁻¹ • (p.1 - p.2)) ∂(m.prod m) :=
      integral_nonneg fun p => phi_nonneg _
    have hcn : 0 ≤ c t := mul_nonneg hcp.le (Real.rpow_nonneg ht.le _)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hcn hnn)]
    calc c t * ∫ p : Euc d × Euc d, phi (t⁻¹ • (p.1 - p.2)) ∂(m.prod m)
        ≤ c t * (m.real Set.univ * m.real Set.univ) := mul_le_mul_of_nonneg_left (int_pair_phi_le_univ m t) hcn
      _ = _ := by ring
  obtain ⟨hI, hE⟩ := QFgen hr.meas hr.bd hν0 hcm hc0 hint (H := g1 s) (fun z => g1_mix_pos hs hs2 z)
  have hW : ∀ ξ : Euc d, (∫ t, c t * (t ^ d * phiHatR d (t * ‖ξ‖)) ∂ν) = g1Hat s ξ := fun ξ => (g1Hat_mix s ξ).symm
  simp_rw [hW] at hI hE
  have hfn : ∀ ξ : Euc d, ‖σ.fourier ξ‖ ^ 2 = cosT m h ξ ^ 2 + sinT m h ξ ^ 2 :=
    fun ξ => hr.norm_fourier_sq ξ
  simp_rw [hfn]
  refine ⟨hI, ?_⟩
  rw [← hE]
  have hbd := abs_g1_le_pos hs hs2 (d := d)
  refine kerEnergy_eq hr (g1 s) (measurable_g1_mix_pos hs hs2) ?_ ((cPhi d s / s) * m.real Set.univ) ?_
  · refine Filter.Eventually.of_forall fun x => ?_
    refine Integrable.mono' (integrable_const (cPhi d s / s)) ?_ (Filter.Eventually.of_forall fun y => ?_)
    · exact ((measurable_g1_mix_pos hs hs2).comp (by fun_prop : Measurable (fun y : Euc d => x - y))).aestronglyMeasurable
    · rw [Real.norm_eq_abs]; exact hbd _
  · refine Filter.Eventually.of_forall fun x => ?_
    have := norm_integral_le_of_norm_le_const (μ := m) (C := cPhi d s / s)
      (f := fun y => |g1 s (x - y)|) (Filter.Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs, abs_abs]; exact hbd _)
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun y => abs_nonneg _)] at this
    linarith [this]


lemma g1_mix_zero (hs : s = 0) (z : Euc d) :
    g1 s z = g1Zero d s + ∫ t, t⁻¹ * (phi (t⁻¹ • z) - 1) ∂(volume.restrict (Set.Ioi (1:ℝ))) := by
  rw [g1_repr_zero hs]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
  have ht0 : 0 < t := lt_trans one_pos ht
  rw [phi_smul_eq ht0]; ring

lemma abs_k_le {t : ℝ} (ht : 0 < t) (z : Euc d) :
    |phi (t⁻¹ • z) - 1| ≤ ((d : ℝ) + 2) * ‖z‖ ^ 2 * t ^ (-2 : ℝ) := by
  have h1 := one_sub_phiR_le (d := d) (‖z‖ / t)
  have h2 := phiR_le_one (d := d) (‖z‖ / t)
  rw [phi_smul_eq ht, abs_of_nonpos (by linarith)]
  have : ((d : ℝ) + 2) * (‖z‖ / t) ^ 2 = ((d : ℝ) + 2) * ‖z‖ ^ 2 * t ^ (-2 : ℝ) := by
    rw [Real.rpow_neg ht.le, show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]
    field_simp
  linarith

lemma abs_Imix_le (z : Euc d) :
    |∫ t, t⁻¹ * (phi (t⁻¹ • z) - 1) ∂(volume.restrict (Set.Ioi (1:ℝ)))| ≤ ((d : ℝ) + 2) * ‖z‖ ^ 2 / 2 := by
  have hI : IntegrableOn (fun t : ℝ => ((d : ℝ) + 2) * ‖z‖ ^ 2 * t ^ (-3 : ℝ)) (Set.Ioi 1) :=
    (integrableOn_Ioi_one_rpow (a := -3) (by norm_num)).const_mul _
  have h1 := norm_integral_le_of_norm_le (μ := volume.restrict (Set.Ioi (1:ℝ)))
    (f := fun t => t⁻¹ * (phi (t⁻¹ • z) - 1)) (g := fun t => ((d : ℝ) + 2) * ‖z‖ ^ 2 * t ^ (-3 : ℝ)) hI
    (by
      filter_upwards [self_mem_ae_restrict (measurableSet_Ioi (a := (1:ℝ)))] with t ht
      have ht0 : 0 < t := lt_trans one_pos ht
      rw [Real.norm_eq_abs, abs_mul, abs_inv, abs_of_pos ht0]
      have := abs_k_le ht0 z
      have e : t ^ (-3 : ℝ) = t⁻¹ * t ^ (-2 : ℝ) := by
        rw [← Real.rpow_neg_one, ← Real.rpow_add ht0]; norm_num
      rw [e]
      calc t⁻¹ * |phi (t⁻¹ • z) - 1| ≤ t⁻¹ * (((d : ℝ) + 2) * ‖z‖ ^ 2 * t ^ (-2 : ℝ)) :=
            mul_le_mul_of_nonneg_left this (by positivity)
        _ = _ := by ring)
  rw [Real.norm_eq_abs] at h1
  refine h1.trans (le_of_eq ?_)
  rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num) one_pos]
  norm_num
  ring

lemma measurable_g1_mix_zero (hs : s = 0) : Measurable (g1 s : Euc d → ℝ) := by
  have e : (g1 s : Euc d → ℝ) = fun z => g1Zero d s + ∫ t, t⁻¹ * (phi (t⁻¹ • z) - 1)
      ∂(volume.restrict (Set.Ioi (1:ℝ))) := funext (g1_mix_zero hs)
  rw [e]
  have hF : Measurable (fun q : Euc d × ℝ => q.2⁻¹ * (phi (q.2⁻¹ • q.1) - 1)) := by
    have := continuous_phi (d := d)
    fun_prop
  exact measurable_const.add (hF.stronglyMeasurable.integral_prod_right (ν := volume.restrict (Set.Ioi (1:ℝ)))).measurable

lemma ae_ball_of {m : Measure (Euc d)} {R : ℝ} (hR : m (closedBall (0 : Euc d) R)ᶜ = 0) :
    ∀ᵐ x ∂m, ‖x‖ ≤ R := by
  rw [ae_iff]
  have : {x : Euc d | ¬ ‖x‖ ≤ R} = (closedBall (0 : Euc d) R)ᶜ := by
    ext x; simp
  rw [this]; exact hR

lemma ae_pair_close {m : Measure (Euc d)} [IsFiniteMeasure m] {R : ℝ}
    (hR : m (closedBall (0 : Euc d) R)ᶜ = 0) : ∀ᵐ p ∂(m.prod m), ‖p.1 - p.2‖ ≤ 2 * R := by
  rw [ae_iff]
  have hsub : {p : Euc d × Euc d | ¬ ‖p.1 - p.2‖ ≤ 2 * R} ⊆
      ((closedBall (0 : Euc d) R)ᶜ ×ˢ (Set.univ : Set (Euc d))) ∪
        ((Set.univ : Set (Euc d)) ×ˢ (closedBall (0 : Euc d) R)ᶜ) := by
    intro p hp
    have hp' : 2 * R < ‖p.1 - p.2‖ := not_le.1 hp
    by_contra hcon
    simp only [Set.mem_union, Set.mem_prod, Set.mem_compl_iff, Metric.mem_closedBall, dist_zero_right,
      Set.mem_univ, and_true, true_and, not_or, not_not] at hcon
    have := norm_sub_le p.1 p.2
    linarith [hcon.1, hcon.2, hp']
  refine measure_mono_null hsub (measure_union_null ?_ ?_)
  · rw [Measure.prod_prod, hR, zero_mul]
  · rw [Measure.prod_prod, hR, mul_zero]


theorem quadForm_g1_zero (hs : s = 0) (hsd : s < (d : ℝ) - 2) (σ : SMeas d) (hf : σ.IsFinite)
    (hc : σ.CompactSupp) (hmass : σ.mass = 0) :
    Integrable (fun ξ : Euc d => g1Hat s ξ * ‖σ.fourier ξ‖ ^ 2) ∧
      kerEnergy (g1 s) σ = ∫ ξ, g1Hat s ξ * ‖σ.fourier ξ‖ ^ 2 := by
  have hcp : cPhi d s = 1 := by subst hs; simp [cPhi]
  obtain ⟨m, h, hr⟩ := σ.exists_repr hf
  haveI := hr.fin
  obtain ⟨R, hRp, hRn⟩ := hc
  have hR : m (closedBall (0 : Euc d) R)ᶜ = 0 := by
    rw [hr.eq_add]; simp [hRp, hRn]
  have hmassh : ∫ x, h x ∂m = 0 := by
    have := hr.int_eq (fun _ => 1) (integrable_const _)
    unfold SMeas.mass at hmass
    rw [this] at hmass
    simpa using hmass
  set ν : Measure ℝ := volume.restrict (Set.Ioi (1:ℝ)) with hν
  set c : ℝ → ℝ := fun t => t⁻¹ with hc
  have hcm : Measurable c := by unfold c; fun_prop
  set k : ℝ → Euc d → ℝ := fun t z => phi (t⁻¹ • z) - 1 with hk
  have hkm : Measurable (fun q : ℝ × Euc d => k q.1 q.2) := by
    have := continuous_phi (d := d)
    unfold k; fun_prop
  have hkb : ∀ t z, |k t z| ≤ 1 := by
    intro t z
    simp only [k]
    have h1 := phiR_pos (d := d) ‖t⁻¹ • z‖
    have h2 := phiR_le_one (d := d) ‖t⁻¹ • z‖
    show |phiR d ‖t⁻¹ • z‖ - 1| ≤ 1
    rw [abs_le]; constructor <;> linarith
  have hν0 : ∀ᵐ t ∂ν, 0 < t := by
    filter_upwards [self_mem_ae_restrict (measurableSet_Ioi (a := (1:ℝ)))] with t ht using lt_trans one_pos ht
  set Mm : ℝ := m.real Set.univ with hMm
  have hint : Integrable (fun t => |c t| * ∫ p : Euc d × Euc d, |k t (p.1 - p.2)| ∂(m.prod m)) ν := by
    have h2 : Integrable (fun t : ℝ => (((d : ℝ) + 2) * (2 * R) ^ 2 * (Mm * Mm)) * t ^ (-3 : ℝ)) ν :=
      (integrableOn_Ioi_one_rpow (a := -3) (by norm_num)).const_mul _
    have hmeasF : Measurable (fun q : ℝ × (Euc d × Euc d) => |k q.1 (q.2.1 - q.2.2)|) := by
      have := hkm.comp (by fun_prop : Measurable (fun q : ℝ × (Euc d × Euc d) => (q.1, q.2.1 - q.2.2)))
      exact this.abs
    have hmt : Measurable (fun t : ℝ => ∫ p : Euc d × Euc d, |k t (p.1 - p.2)| ∂(m.prod m)) :=
      (hmeasF.stronglyMeasurable.integral_prod_right' (ν := m.prod m)).measurable
    refine h2.mono' ((hcm.abs.mul hmt).aestronglyMeasurable) ?_
    filter_upwards [hν0] with t ht
    have hb := norm_integral_le_of_norm_le_const (μ := m.prod m)
      (C := ((d : ℝ) + 2) * (2 * R) ^ 2 * t ^ (-2 : ℝ))
      (f := fun p : Euc d × Euc d => |k t (p.1 - p.2)|) (by
        filter_upwards [ae_pair_close hR] with p hp
        rw [Real.norm_eq_abs, abs_abs]
        refine (abs_k_le ht (p.1 - p.2)).trans ?_
        have hn : ‖p.1 - p.2‖ ^ 2 ≤ (2 * R) ^ 2 := by
          have := norm_nonneg (p.1 - p.2)
          exact pow_le_pow_left₀ this hp 2
        have : 0 ≤ t ^ (-2 : ℝ) := by positivity
        have h3 : (0:ℝ) ≤ (d : ℝ) + 2 := by positivity
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hn h3) this)
    rw [prod_real_univ] at hb
    rw [Real.norm_eq_abs] at hb ⊢
    have hcn : |c t| = t⁻¹ := by simp only [c]; rw [abs_of_pos (inv_pos.2 ht)]
    have hInn : 0 ≤ ∫ p : Euc d × Euc d, |k t (p.1 - p.2)| ∂(m.prod m) := integral_nonneg fun p => abs_nonneg _
    rw [abs_of_nonneg (mul_nonneg (abs_nonneg _) hInn), hcn]
    rw [abs_of_nonneg hInn] at hb
    have e : t ^ (-3 : ℝ) = t⁻¹ * t ^ (-2 : ℝ) := by
      rw [← Real.rpow_neg_one, ← Real.rpow_add ht]; norm_num
    rw [e]
    calc t⁻¹ * ∫ p : Euc d × Euc d, |k t (p.1 - p.2)| ∂(m.prod m)
        ≤ t⁻¹ * (((d : ℝ) + 2) * (2 * R) ^ 2 * t ^ (-2 : ℝ) * (Mm * Mm)) :=
          mul_le_mul_of_nonneg_left hb (by positivity)
      _ = _ := by ring
  obtain ⟨hI, hE⟩ := MIXgen hr.meas hr.bd hcm k hkm hkb hint
  have hhint : Integrable h m := by
    refine Integrable.mono' (integrable_const (1:ℝ)) hr.meas.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs]; exact hr.bd x
  have hphiint : ∀ (t : ℝ) (x : Euc d), Integrable (fun y : Euc d => h y * phi (t⁻¹ • (x - y))) m := by
    intro t x
    have hm : Measurable (fun y : Euc d => h y * phi (t⁻¹ • (x - y))) := by
      have := continuous_phi (d := d)
      have := hr.meas
      fun_prop
    refine Integrable.mono' (integrable_const (1:ℝ)) hm.aestronglyMeasurable (Filter.Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    calc |h y| * |phi (t⁻¹ • (x - y))| ≤ 1 * 1 := mul_le_mul (hr.bd y) (abs_phi_le_one _) (abs_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  have hPk : ∀ t : ℝ, ∫ x, h x * ∫ y, h y * k t (x - y) ∂m ∂m =
      ∫ x, h x * ∫ y, h y * phi (t⁻¹ • (x - y)) ∂m ∂m := by
    intro t
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only
    congr 1
    have e : ∀ y : Euc d, h y * k t (x - y) = h y * phi (t⁻¹ • (x - y)) - h y := by
      intro y; simp only [k]; ring
    simp_rw [e]
    rw [integral_sub (hphiint t x) hhint, hmassh, sub_zero]
  have hQ : ∀ᵐ t ∂ν, c t * (∫ x, h x * ∫ y, h y * k t (x - y) ∂m ∂m) =
      c t * (∫ ξ : Euc d, (t ^ d * phiHatR d (t * ‖ξ‖)) * (cosT m h ξ ^ 2 + sinT m h ξ ^ 2)) := by
    filter_upwards [hν0] with t ht
    rw [hPk t, QT hr.meas hr.bd ht]
  have hc0 : ∀ᵐ t ∂ν, 0 ≤ c t := by
    filter_upwards [hν0] with t ht
    exact (inv_pos.2 ht).le
  have hI' := hI.congr hQ
  obtain ⟨hT1, hT2⟩ := TF hr.meas hr.bd hν0 hcm hc0 hI'
  have hW : ∀ ξ : Euc d, (∫ t, c t * (t ^ d * phiHatR d (t * ‖ξ‖)) ∂ν) = g1Hat s ξ := by
    intro ξ
    rw [g1Hat_eq, hcp, one_mul]
    refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    have ht0 : 0 < t := lt_trans one_pos ht
    have : t ⁻¹ * t ^ d = t ^ ((d : ℝ) - s - 1) := by
      rw [hs, ← Real.rpow_natCast, ← Real.rpow_neg_one, ← Real.rpow_add ht0]; congr 1; ring
    simp only [c]
    rw [← this]; ring
  simp_rw [hW] at hT1 hT2
  have hfn : ∀ ξ : Euc d, ‖σ.fourier ξ‖ ^ 2 = cosT m h ξ ^ 2 + sinT m h ξ ^ 2 :=
    fun ξ => hr.norm_fourier_sq ξ
  simp_rw [hfn]
  refine ⟨hT1, ?_⟩
  rw [hT2, ← integral_congr_ae hQ, ← hE]
  set Bg : ℝ := |g1Zero d s| + ((d : ℝ) + 2) * (2 * R) ^ 2 / 2 with hBg
  have hg1bd : ∀ x y : Euc d, ‖x‖ ≤ R → ‖y‖ ≤ R → |g1 s (x - y)| ≤ Bg := by
    intro x y hx hy
    rw [g1_mix_zero hs]
    refine (abs_add_le _ _).trans ?_
    have h1 := abs_Imix_le (d := d) (x - y)
    have hn : ‖x - y‖ ^ 2 ≤ (2 * R) ^ 2 := by
      have := norm_sub_le x y
      exact pow_le_pow_left₀ (norm_nonneg _) (by linarith) 2
    have h3 : (0:ℝ) ≤ (d : ℝ) + 2 := by positivity
    have : ((d : ℝ) + 2) * ‖x - y‖ ^ 2 / 2 ≤ ((d : ℝ) + 2) * (2 * R) ^ 2 / 2 := by
      have := mul_le_mul_of_nonneg_left hn h3
      linarith
    rw [hBg]; linarith
  have hBg0 : 0 ≤ Bg := by rw [hBg]; positivity
  have hmeasg := measurable_g1_mix_zero (d := d) hs
  have hEint : ∀ᵐ x ∂m, Integrable (fun y => g1 s (x - y)) m := by
    filter_upwards [ae_ball_of hR] with x hx
    refine Integrable.mono' (integrable_const Bg)
      (hmeasg.comp (by fun_prop : Measurable (fun y : Euc d => x - y))).aestronglyMeasurable ?_
    filter_upwards [ae_ball_of hR] with y hy
    rw [Real.norm_eq_abs]; exact hg1bd x y hx hy
  have hBint : ∀ᵐ x ∂m, ∫ y, |g1 s (x - y)| ∂m ≤ Bg * Mm := by
    filter_upwards [ae_ball_of hR] with x hx
    have := norm_integral_le_of_norm_le_const (μ := m) (C := Bg)
      (f := fun y => |g1 s (x - y)|) (by
        filter_upwards [ae_ball_of hR] with y hy
        rw [Real.norm_eq_abs, abs_abs]; exact hg1bd x y hx hy)
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun y => abs_nonneg _)] at this
    linarith [this]
  rw [kerEnergy_eq hr (g1 s) hmeasg hEint (Bg * Mm) hBint]
  refine integral_congr_ae ?_
  filter_upwards [ae_ball_of hR] with x hx
  congr 1
  -- inner identity
  have hIint : Integrable (fun y : Euc d => h y * ∫ t, c t * k t (x - y) ∂ν) m := by
    have hI' : Measurable (fun y : Euc d => ∫ t, c t * k t (x - y) ∂ν) := by
      have hF : Measurable (fun q : Euc d × ℝ => c q.2 * k q.2 (x - q.1)) := by
        have := hkm.comp (by fun_prop : Measurable (fun q : Euc d × ℝ => (q.2, x - q.1)))
        exact (hcm.comp measurable_snd).mul this
      exact (hF.stronglyMeasurable.integral_prod_right (ν := ν)).measurable
    refine Integrable.mono' (integrable_const (((d : ℝ) + 2) * (2 * R) ^ 2 / 2))
      ((hr.meas.mul hI').aestronglyMeasurable) ?_
    filter_upwards [ae_ball_of hR] with y hy
    rw [Real.norm_eq_abs, abs_mul]
    have h1 := abs_Imix_le (d := d) (x - y)
    have hn : ‖x - y‖ ^ 2 ≤ (2 * R) ^ 2 := by
      have := norm_sub_le x y
      exact pow_le_pow_left₀ (norm_nonneg _) (by linarith) 2
    have h3 : (0:ℝ) ≤ (d : ℝ) + 2 := by positivity
    have h4 : |∫ t, c t * k t (x - y) ∂ν| ≤ ((d : ℝ) + 2) * (2 * R) ^ 2 / 2 := by
      have := mul_le_mul_of_nonneg_left hn h3
      calc _ ≤ ((d : ℝ) + 2) * ‖x - y‖ ^ 2 / 2 := h1
        _ ≤ _ := by linarith
    calc |h y| * |∫ t, c t * k t (x - y) ∂ν| ≤ 1 * (((d : ℝ) + 2) * (2 * R) ^ 2 / 2) :=
          mul_le_mul (hr.bd y) h4 (abs_nonneg _) zero_le_one
      _ = _ := one_mul _
  have e : ∀ y : Euc d, h y * g1 s (x - y) = g1Zero d s * h y + h y * ∫ t, c t * k t (x - y) ∂ν := by
    intro y
    rw [g1_mix_zero hs]
    simp only [c, k]
    ring
  simp_rw [e]
  rw [integral_add (hhint.const_mul _) hIint, integral_const_mul, hmassh, mul_zero, zero_add]

end HRS.Commutator.Whole
