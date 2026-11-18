import HRS.Commutator.Whole.PositiveAux6

/-!
# Helpers for `Positive.lean` (packet `CMX-POS`), part G

Fubini in the scale variable for general bounded kernels, and the quadratic forms of `f_1`, `g_1`.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform ContDiff

namespace HRS.Commutator.Whole

open HRS HRS.Whole

variable {d : ℕ} {s : ℝ}

/-- Fubini in the scale variable on the physical side, for a bounded family of kernels. -/
lemma MIXgen {m : Measure (Euc d)} [IsFiniteMeasure m] {h : Euc d → ℝ} (hh : Measurable h)
    (hb : ∀ x, |h x| ≤ 1) {ν : Measure ℝ} [SFinite ν] {c : ℝ → ℝ} (hc : Measurable c)
    (k : ℝ → Euc d → ℝ) (hk : Measurable (fun q : ℝ × Euc d => k q.1 q.2))
    (hkb : ∀ t z, |k t z| ≤ 1)
    (hint : Integrable (fun t => |c t| * ∫ p : Euc d × Euc d, |k t (p.1 - p.2)| ∂(m.prod m)) ν) :
    Integrable (fun t => c t * (∫ x, h x * ∫ y, h y * k t (x - y) ∂m ∂m)) ν ∧
    ∫ x, h x * ∫ y, h y * (∫ t, c t * k t (x - y) ∂ν) ∂m ∂m =
      ∫ t, c t * (∫ x, h x * ∫ y, h y * k t (x - y) ∂m ∂m) ∂ν := by
  have hkm : Measurable (fun q : (Euc d × Euc d) × ℝ => k q.2 (q.1.1 - q.1.2)) :=
    hk.comp (by fun_prop : Measurable (fun q : (Euc d × Euc d) × ℝ => (q.2, q.1.1 - q.1.2)))
  have hcm : Measurable (fun q : (Euc d × Euc d) × ℝ => c q.2) := hc.comp measurable_snd
  let Gabs : (Euc d × Euc d) × ℝ → ℝ := fun q => c q.2 * k q.2 (q.1.1 - q.1.2)
  have hGabsm : Measurable Gabs := hcm.mul hkm
  have hGabs : Integrable Gabs ((m.prod m).prod ν) := by
    rw [integrable_prod_iff' hGabsm.aestronglyMeasurable]
    refine ⟨?_, ?_⟩
    · refine Filter.Eventually.of_forall fun t => ?_
      refine Integrable.mono' (integrable_const |c t|) ?_ (Filter.Eventually.of_forall fun p => ?_)
      · exact (hGabsm.comp (by fun_prop : Measurable (fun p : Euc d × Euc d => (p, t)))).aestronglyMeasurable
      · simp only [Gabs]
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_of_le_one_right (abs_nonneg _) (hkb _ _)
    · refine hint.congr (Filter.Eventually.of_forall fun t => ?_)
      simp only [Gabs]
      have : ∀ p : Euc d × Euc d, ‖c t * k t (p.1 - p.2)‖ = |c t| * |k t (p.1 - p.2)| := by
        intro p; rw [Real.norm_eq_abs, abs_mul]
      simp_rw [this]
      rw [integral_const_mul]
  let G : (Euc d × Euc d) × ℝ → ℝ := fun q => h q.1.1 * h q.1.2 * Gabs q
  have hGm : Measurable G := by
    have h1 : Measurable (fun q : (Euc d × Euc d) × ℝ => h q.1.1) := hh.comp (measurable_fst.comp measurable_fst)
    have h2 : Measurable (fun q : (Euc d × Euc d) × ℝ => h q.1.2) := hh.comp (measurable_snd.comp measurable_fst)
    exact (h1.mul h2).mul hGabsm
  have hGi : Integrable G ((m.prod m).prod ν) := by
    refine hGabs.norm.mono' hGm.aestronglyMeasurable (Filter.Eventually.of_forall fun q => ?_)
    simp only [G]
    rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    have := mul_le_mul (mul_le_mul (hb q.1.1) (hb q.1.2) (abs_nonneg _) zero_le_one)
      (le_refl ‖Gabs q‖) (norm_nonneg _) (by norm_num : (0:ℝ) ≤ 1 * 1)
    simpa using this
  have hJ : Integrable (fun p : Euc d × Euc d => ∫ t, G (p, t) ∂ν) (m.prod m) := hGi.integral_prod_left
  have hslice : ∀ t : ℝ, Integrable (fun p : Euc d × Euc d => h p.1 * h p.2 * k t (p.1 - p.2)) (m.prod m) := by
    intro t
    have hm : Measurable (fun p : Euc d × Euc d => h p.1 * h p.2 * k t (p.1 - p.2)) := by
      have := hk.comp (by fun_prop : Measurable (fun p : Euc d × Euc d => (t, p.1 - p.2)))
      exact ((hh.comp measurable_fst).mul (hh.comp measurable_snd)).mul this
    refine Integrable.mono' (integrable_const (1:ℝ)) hm.aestronglyMeasurable (Filter.Eventually.of_forall fun p => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_mul]
    calc |h p.1| * |h p.2| * |k t (p.1 - p.2)| ≤ 1 * 1 * 1 :=
          mul_le_mul (mul_le_mul (hb _) (hb _) (abs_nonneg _) zero_le_one) (hkb _ _) (abs_nonneg _) (by norm_num)
      _ = 1 := by norm_num
  have e1 : ∫ x, h x * ∫ y, h y * (∫ t, c t * k t (x - y) ∂ν) ∂m ∂m =
      ∫ p : Euc d × Euc d, ∫ t, G (p, t) ∂ν ∂(m.prod m) := by
    rw [integral_prod _ hJ]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [G, Gabs]
    rw [integral_const_mul]
    ring
  have e3 : ∀ t : ℝ, ∫ p : Euc d × Euc d, G (p, t) ∂(m.prod m) =
      c t * (∫ x, h x * ∫ y, h y * k t (x - y) ∂m ∂m) := by
    intro t
    have e2 : ∀ p : Euc d × Euc d, G (p, t) = c t * (h p.1 * h p.2 * k t (p.1 - p.2)) := by
      intro p; simp only [G, Gabs]; ring
    simp_rw [e2]
    rw [integral_const_mul, integral_prod _ (hslice t)]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only; ring
  refine ⟨?_, ?_⟩
  · exact hGi.integral_prod_right.congr (Filter.Eventually.of_forall e3)
  · rw [e1, integral_integral_swap hGi]
    exact integral_congr_ae (Filter.Eventually.of_forall e3)


lemma BddCptDensity.integrable {ρ : Euc d → ℝ} (hρ : BddCptDensity ρ) : Integrable ρ := by
  obtain ⟨B, hB⟩ := hρ.bdd
  have hc : IsCompact (tsupport ρ) := hρ.cpt
  have h1 : Integrable ((tsupport ρ).indicator (fun _ : Euc d => B)) :=
    (integrable_indicator_iff hc.isClosed.measurableSet).2 (integrableOn_const hc.measure_lt_top.ne)
  refine h1.mono' hρ.measurable.aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
  by_cases hx : x ∈ tsupport ρ
  · rw [Set.indicator_of_mem hx]; exact (Real.norm_eq_abs _).le.trans (hB x)
  · have : ρ x = 0 := image_eq_zero_of_notMem_tsupport hx
    rw [this, Set.indicator_of_notMem hx]; simp

lemma ofDensity_finite {ρ : Euc d → ℝ} (hρ : BddCptDensity ρ) : (SMeas.ofDensity ρ).IsFinite := by
  have hi := hρ.integrable
  refine ⟨?_, ?_⟩
  · exact isFiniteMeasure_withDensity_ofReal hi.2
  · exact isFiniteMeasure_withDensity_ofReal hi.neg.2

lemma ofDensity_le {ρ : Euc d → ℝ} (hρ : BddCptDensity ρ) :
    ∃ B : ℝ, 0 ≤ B ∧ (SMeas.ofDensity ρ).pos + (SMeas.ofDensity ρ).neg ≤
      ENNReal.ofReal B • (volume : Measure (Euc d)) := by
  obtain ⟨B, hB⟩ := hρ.bdd
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  refine ⟨B, hB0, ?_⟩
  unfold SMeas.ofDensity
  simp only
  rw [← withDensity_add_left (hρ.measurable.ennreal_ofReal) (fun x => ENNReal.ofReal (-ρ x))]
  rw [← withDensity_const (ENNReal.ofReal B)]
  refine withDensity_mono (Filter.Eventually.of_forall fun x => ?_)
  simp only [Pi.add_apply]
  rcases le_total 0 (ρ x) with h | h
  · rw [ENNReal.ofReal_of_nonpos (by linarith : -ρ x ≤ 0), add_zero]
    exact ENNReal.ofReal_le_ofReal ((le_abs_self _).trans (hB x))
  · rw [ENNReal.ofReal_of_nonpos h, zero_add]
    exact ENNReal.ofReal_le_ofReal ((neg_le_abs _).trans (hB x))


lemma phi_nonneg (x : Euc d) : 0 ≤ phi x := (phiR_pos _).le

lemma measurable_phi : Measurable (phi : Euc d → ℝ) := continuous_phi.measurable

lemma prod_real_univ (m : Measure (Euc d)) [IsFiniteMeasure m] :
    (m.prod m).real Set.univ = m.real Set.univ * m.real Set.univ := by
  simp only [Measure.real]
  rw [← Set.univ_prod_univ, Measure.prod_prod, ENNReal.toReal_mul]

lemma int_pair_phi_le_univ (m : Measure (Euc d)) [IsFiniteMeasure m] (t : ℝ) :
    ∫ p : Euc d × Euc d, phi (t⁻¹ • (p.1 - p.2)) ∂(m.prod m) ≤ m.real Set.univ * m.real Set.univ := by
  have := norm_integral_le_of_norm_le_const (μ := m.prod m) (C := 1)
    (f := fun p : Euc d × Euc d => phi (t⁻¹ • (p.1 - p.2)))
    (Filter.Eventually.of_forall fun p => by
      rw [Real.norm_eq_abs]; exact abs_phi_le_one _)
  rw [prod_real_univ] at this
  calc _ ≤ ‖∫ p : Euc d × Euc d, phi (t⁻¹ • (p.1 - p.2)) ∂(m.prod m)‖ := Real.le_norm_self _
    _ ≤ _ := by simpa using this

lemma integrable_phi_pair (m : Measure (Euc d)) [IsFiniteMeasure m] (t : ℝ) :
    Integrable (fun p : Euc d × Euc d => phi (t⁻¹ • (p.1 - p.2))) (m.prod m) := by
  refine Integrable.mono' (integrable_const (1:ℝ)) ?_ (Filter.Eventually.of_forall fun p => ?_)
  · exact (by have := continuous_phi (d := d); fun_prop :
      Measurable (fun p : Euc d × Euc d => phi (t⁻¹ • (p.1 - p.2)))).aestronglyMeasurable
  · rw [Real.norm_eq_abs]; exact abs_phi_le_one _

lemma int_phi_translate (t : ℝ) (ht : 0 < t) (x : Euc d) :
    ∫ y : Euc d, phi (t⁻¹ • (x - y)) = t ^ d * ∫ y : Euc d, phi y := by
  have h1 : ∫ y : Euc d, phi (t⁻¹ • (x - y)) = ∫ y : Euc d, phi (t⁻¹ • y) :=
    integral_sub_left_eq_self (fun y : Euc d => phi (t⁻¹ • y)) volume x
  rw [h1, Measure.integral_comp_inv_smul_of_nonneg volume (fun y : Euc d => phi y) ht.le]
  simp

lemma int_pair_phi_le_dens (m : Measure (Euc d)) [IsFiniteMeasure m] {B : ℝ} (hB : 0 ≤ B)
    (hm : m ≤ ENNReal.ofReal B • (volume : Measure (Euc d))) {t : ℝ} (ht : 0 < t) :
    ∫ p : Euc d × Euc d, phi (t⁻¹ • (p.1 - p.2)) ∂(m.prod m) ≤
      m.real Set.univ * (B * (t ^ d * ∫ y : Euc d, phi y)) := by
  rw [integral_prod _ (integrable_phi_pair m t)]
  have hinner : ∀ x : Euc d, ∫ y, phi (t⁻¹ • (x - y)) ∂m ≤ B * (t ^ d * ∫ y : Euc d, phi y) := by
    intro x
    have hint : Integrable (fun y : Euc d => phi (t⁻¹ • (x - y))) := by
      have := (integrable_phi (d := d)).comp_smul (R := t⁻¹) (inv_ne_zero ht.ne')
      exact (this.comp_sub_left x)
    calc ∫ y, phi (t⁻¹ • (x - y)) ∂m ≤ ∫ y, phi (t⁻¹ • (x - y)) ∂(ENNReal.ofReal B • (volume : Measure (Euc d))) :=
          integral_mono_measure hm (Filter.Eventually.of_forall fun y => phi_nonneg _)
            (hint.smul_measure ENNReal.ofReal_ne_top)
      _ = B * ∫ y, phi (t⁻¹ • (x - y)) := by
          rw [integral_smul_measure, ENNReal.toReal_ofReal hB, smul_eq_mul]
      _ = _ := by rw [int_phi_translate t ht]
  have := norm_integral_le_of_norm_le_const (μ := m) (C := B * (t ^ d * ∫ y : Euc d, phi y))
    (f := fun x => ∫ y, phi (t⁻¹ • (x - y)) ∂m) (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun y => phi_nonneg _)]
      exact hinner x)
  calc _ ≤ ‖∫ x, ∫ y, phi (t⁻¹ • (x - y)) ∂m ∂m‖ := Real.le_norm_self _
    _ ≤ _ := by rw [mul_comm]; exact this


lemma phi_smul_eq {t : ℝ} (ht : 0 < t) (z : Euc d) : phi (t⁻¹ • z) = phiR d (‖z‖ / t) := by
  rw [phi_eq, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos ht, inv_mul_eq_div]

lemma fTrunc_mix (s : ℝ) (z : Euc d) :
    fTrunc s 1 z = ∫ t, (cPhi d s * t ^ (-s - 1)) * phi (t⁻¹ • z) ∂(volume.restrict (Set.Ioc (0:ℝ) 1)) := by
  rw [fTrunc_eq, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioc (fun t ht => ?_)
  rw [phi_smul_eq ht.1]; ring

lemma f1Hat_mix (s : ℝ) (ξ : Euc d) :
    f1Hat s ξ = ∫ t, (cPhi d s * t ^ (-s - 1)) * (t ^ d * phiHatR d (t * ‖ξ‖))
      ∂(volume.restrict (Set.Ioc (0:ℝ) 1)) := by
  rw [f1Hat_eq, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioc (fun t ht => ?_)
  have ht0 : 0 < t := ht.1
  have : t ^ (-s - 1) * t ^ d = t ^ ((d : ℝ) - s - 1) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add ht0]; congr 1; ring
  calc cPhi d s * (t ^ ((d : ℝ) - s - 1) * phiHatR d (t * ‖ξ‖))
      = cPhi d s * ((t ^ (-s - 1) * t ^ d) * phiHatR d (t * ‖ξ‖)) := by rw [this]
    _ = _ := by ring

lemma measurable_pair_int (m : Measure (Euc d)) [IsFiniteMeasure m] :
    Measurable (fun t : ℝ => ∫ p : Euc d × Euc d, phi (t⁻¹ • (p.1 - p.2)) ∂(m.prod m)) := by
  have hF : Measurable (fun q : ℝ × (Euc d × Euc d) => phi (q.1⁻¹ • (q.2.1 - q.2.2))) := by
    have := continuous_phi (d := d)
    fun_prop
  exact (hF.stronglyMeasurable.integral_prod_right' (ν := m.prod m)).measurable

theorem quadForm_f1_aux (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) (ρ : Euc d → ℝ)
    (hρ : BddCptDensity ρ) :
    Integrable (fun ξ : Euc d => f1Hat s ξ * ‖(SMeas.ofDensity ρ).fourier ξ‖ ^ 2) ∧
      kerEnergy (fTrunc s 1) (SMeas.ofDensity ρ) =
        ∫ ξ, f1Hat s ξ * ‖(SMeas.ofDensity ρ).fourier ξ‖ ^ 2 := by
  have hs2 : s < 2 * (d : ℝ) + 4 := by linarith [(Nat.cast_nonneg d : (0:ℝ) ≤ d)]
  have hcp := cPhi_pos d hs0 hs2
  obtain ⟨m, h, hr⟩ := (SMeas.ofDensity ρ).exists_repr (ofDensity_finite hρ)
  haveI := hr.fin
  obtain ⟨B, hB0, hle⟩ := ofDensity_le hρ
  have hmle : m ≤ ENNReal.ofReal B • (volume : Measure (Euc d)) := by rw [hr.eq_add]; exact hle
  set ν : Measure ℝ := volume.restrict (Set.Ioc (0:ℝ) 1) with hν
  set c : ℝ → ℝ := fun t => cPhi d s * t ^ (-s - 1) with hc
  have hcm : Measurable c := by unfold c; fun_prop
  have hν0 : ∀ᵐ t ∂ν, 0 < t := by
    filter_upwards [self_mem_ae_restrict (measurableSet_Ioc (a := (0:ℝ)) (b := 1))] with t ht using ht.1
  have hc0 : ∀ᵐ t ∂ν, 0 ≤ c t := by
    filter_upwards [hν0] with t ht
    exact mul_nonneg hcp.le (Real.rpow_nonneg ht.le _)
  have hint : Integrable (fun t => c t * ∫ p : Euc d × Euc d, phi (t⁻¹ • (p.1 - p.2)) ∂(m.prod m)) ν := by
    set K : ℝ := m.real Set.univ * (B * ∫ y : Euc d, phi y) with hK
    have h1 : IntegrableOn (fun t : ℝ => t ^ ((d : ℝ) - s - 1)) (Set.Ioc 0 1) := by
      have := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1) (r := (d : ℝ) - s - 1)
        (by linarith))
      exact (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).1 this
    have h2 : Integrable (fun t : ℝ => (cPhi d s * K) * t ^ ((d : ℝ) - s - 1)) ν := h1.const_mul _
    refine h2.mono' ?_ ?_
    · exact (hcm.mul (measurable_pair_int m)).aestronglyMeasurable
    · filter_upwards [hν0] with t ht
      have hnn : 0 ≤ ∫ p : Euc d × Euc d, phi (t⁻¹ • (p.1 - p.2)) ∂(m.prod m) :=
        integral_nonneg fun p => phi_nonneg _
      have hb := int_pair_phi_le_dens m hB0 hmle ht
      have hcn : 0 ≤ c t := mul_nonneg hcp.le (Real.rpow_nonneg ht.le _)
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hcn hnn)]
      have e : t ^ ((d : ℝ) - s - 1) = t ^ (-s - 1) * t ^ d := by
        rw [← Real.rpow_natCast, ← Real.rpow_add ht]; congr 1; ring
      calc c t * ∫ p : Euc d × Euc d, phi (t⁻¹ • (p.1 - p.2)) ∂(m.prod m)
          ≤ c t * (m.real Set.univ * (B * (t ^ d * ∫ y : Euc d, phi y))) :=
            mul_le_mul_of_nonneg_left hb hcn
        _ = (cPhi d s * K) * t ^ ((d : ℝ) - s - 1) := by
            rw [e]; simp only [c, hK]; ring
  obtain ⟨hI, hE⟩ := QFgen hr.meas hr.bd hν0 hcm hc0 hint (H := fTrunc s 1) (fun z => fTrunc_mix s z)
  have hW : ∀ ξ : Euc d, (∫ t, c t * (t ^ d * phiHatR d (t * ‖ξ‖)) ∂ν) = f1Hat s ξ := fun ξ => (f1Hat_mix s ξ).symm
  simp_rw [hW] at hI hE
  have hfn : ∀ ξ : Euc d, ‖(SMeas.ofDensity ρ).fourier ξ‖ ^ 2 = cosT m h ξ ^ 2 + sinT m h ξ ^ 2 :=
    fun ξ => hr.norm_fourier_sq ξ
  simp_rw [hfn]
  refine ⟨hI, ?_⟩
  rw [← hE]
  -- identify the energy
  have hfint := (fTrunc_integrable_aux (d := d) (s := s) (by linarith [(Nat.cast_nonneg d : (0:ℝ) ≤ d)])).1
  refine kerEnergy_eq hr (fTrunc s 1) measurable_fTrunc ?_ (B * ∫ y : Euc d, |fTrunc s 1 y|) ?_
  · refine Filter.Eventually.of_forall fun x => ?_
    have := (hfint.comp_sub_left x).smul_measure (c := ENNReal.ofReal B) ENNReal.ofReal_ne_top
    exact this.mono_measure hmle
  · refine Filter.Eventually.of_forall fun x => ?_
    have hi : Integrable (fun y : Euc d => |fTrunc s 1 (x - y)|) := (hfint.comp_sub_left x).abs
    calc ∫ y, |fTrunc s 1 (x - y)| ∂m
        ≤ ∫ y, |fTrunc s 1 (x - y)| ∂(ENNReal.ofReal B • (volume : Measure (Euc d))) :=
          integral_mono_measure hmle (Filter.Eventually.of_forall fun y => abs_nonneg _)
            (hi.smul_measure ENNReal.ofReal_ne_top)
      _ = B * ∫ y : Euc d, |fTrunc s 1 (x - y)| := by
          rw [integral_smul_measure, ENNReal.toReal_ofReal hB0, smul_eq_mul]
      _ = B * ∫ y : Euc d, |fTrunc s 1 y| := by
          rw [integral_sub_left_eq_self (fun y : Euc d => |fTrunc s 1 y|) volume x]

end HRS.Commutator.Whole
