import HRS.Whole.Static
import HRS.Equilibrium.PoleCavity

/-!
# Packet Q34, helper file 1: radial integrals on `ℝ^d`
-/

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace HRS.Whole.Q34

variable {d : ℕ}

/-- Polar coordinates in `ℝ^d` for nonnegative measurable functions (lintegral form). -/
theorem lintegral_polar (hd : 1 ≤ d) (g : Euc d → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻ y, g y ∂(volume : Measure (Euc d)) =
      ∫⁻ ω : sphere (0 : Euc d) 1, (∫⁻ t in Ioi (0 : ℝ),
        ENNReal.ofReal (t ^ (d - 1)) * g (t • (ω : Euc d)))
        ∂(volume : Measure (Euc d)).toSphere := by
  have : Nontrivial (Euc d) := Module.nontrivial_of_finrank_pos (R := ℝ) (by simp; omega)
  have hfr : Module.finrank ℝ (Euc d) = d := by simp
  calc ∫⁻ y, g y ∂(volume : Measure (Euc d))
      = ∫⁻ x : ({(0 : Euc d)}ᶜ : Set (Euc d)), g x.1 ∂((volume : Measure (Euc d)).comap (↑)) := by
        rw [lintegral_subtype_comap (measurableSet_singleton _).compl, restrict_compl_singleton]
    _ = ∫⁻ p : sphere (0 : Euc d) 1 × Ioi (0 : ℝ), g (p.2.1 • (p.1 : Euc d))
          ∂((volume : Measure (Euc d)).toSphere.prod
            (Measure.volumeIoiPow (Module.finrank ℝ (Euc d) - 1))) := by
        have := (Measure.measurePreserving_homeomorphUnitSphereProd
          (volume : Measure (Euc d))).lintegral_comp_emb
          (Homeomorph.measurableEmbedding _)
          (fun p : sphere (0 : Euc d) 1 × Ioi (0 : ℝ) => g (p.2.1 • (p.1 : Euc d)))
        rw [← this]
        refine lintegral_congr fun x => ?_
        simp only [homeomorphUnitSphereProd_apply_snd_coe, homeomorphUnitSphereProd_apply_fst_coe]
        have hn : 0 < ‖x.1‖ := norm_pos_iff.2 x.2
        rw [smul_smul, mul_inv_cancel₀ hn.ne', one_smul]
    _ = _ := by
        rw [lintegral_prod]
        · refine lintegral_congr fun ω => ?_
          simp only [Measure.volumeIoiPow, hfr]
          rw [lintegral_withDensity_eq_lintegral_mul]
          · exact lintegral_subtype_comap (μ := (volume : Measure ℝ)) measurableSet_Ioi
              (fun r : ℝ => ENNReal.ofReal (r ^ (d - 1)) * g (r • (ω : Euc d)))
          · exact (measurable_subtype_coe.pow_const _).ennreal_ofReal
          · exact hg.comp (measurable_subtype_coe.smul_const _)
        · exact (hg.comp ((measurable_subtype_coe.comp measurable_snd).smul
            (measurable_subtype_coe.comp measurable_fst))).aemeasurable

theorem sphereArea_eq (hd : 1 ≤ d) :
    ENNReal.ofReal (sphereArea d) = (d : ℝ≥0∞) * volume (ball (0 : Euc d) 1) := by
  have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  rw [EuclideanSpace.volume_ball]
  simp only [ENNReal.ofReal_one, one_pow, one_mul, Fintype.card_fin]
  have hd0 : (0:ℝ) < d := by exact_mod_cast hd
  have hG : Real.Gamma ((d : ℝ) / 2 + 1) = (d : ℝ) / 2 * Real.Gamma ((d : ℝ) / 2) :=
    Real.Gamma_add_one (by positivity)
  have hGp : 0 < Real.Gamma ((d : ℝ) / 2) := Real.Gamma_pos_of_pos (by positivity)
  have hs : Real.sqrt Real.pi ^ d = Real.pi ^ ((d : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul Real.pi_pos.le]
    congr 1; ring
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  unfold sphereArea
  rw [hG, hs]
  have hp : 0 < Real.pi ^ ((d : ℝ) / 2) := by positivity
  field_simp


/-- Radial integrals over `ℝ^d`. -/
theorem lintegral_radial (hd : 1 ≤ d) (φ : ℝ → ℝ≥0∞) (hφ : Measurable φ) :
    ∫⁻ x : Euc d, φ ‖x‖ = ENNReal.ofReal (sphereArea d) *
      ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (r ^ (d - 1)) * φ r := by
  have hm : Measurable (fun x : Euc d => φ ‖x‖) := hφ.comp measurable_norm
  rw [lintegral_polar hd _ hm]
  have : ∀ ω : sphere (0 : Euc d) 1, (∫⁻ t in Ioi (0 : ℝ),
      ENNReal.ofReal (t ^ (d - 1)) * φ ‖t • (ω : Euc d)‖) =
      ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (r ^ (d - 1)) * φ r := by
    intro ω
    refine setLIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have h1 : ‖(ω : Euc d)‖ = 1 := by simp
    rw [norm_smul, h1, mul_one, Real.norm_eq_abs, abs_of_pos ht]
  simp_rw [this]
  rw [lintegral_const]
  have hfr : Module.finrank ℝ (Euc d) = d := by simp
  have : Nontrivial (Euc d) := Module.nontrivial_of_finrank_pos (R := ℝ) (by simp; omega)
  rw [sphereArea_eq hd, Measure.toSphere_apply_univ, hfr, mul_comm]

theorem lintegral_radial_set (hd : 1 ≤ d) (S : Set ℝ) (hS : MeasurableSet S) (φ : ℝ → ℝ≥0∞)
    (hφ : Measurable φ) :
    ∫⁻ x in {x : Euc d | ‖x‖ ∈ S}, φ ‖x‖ = ENNReal.ofReal (sphereArea d) *
      ∫⁻ r in Ioi (0 : ℝ) ∩ S, ENNReal.ofReal (r ^ (d - 1)) * φ r := by
  have hSm : MeasurableSet {x : Euc d | ‖x‖ ∈ S} := measurable_norm hS
  rw [← lintegral_indicator hSm]
  have : ∀ x : Euc d, ({x : Euc d | ‖x‖ ∈ S}.indicator (fun x => φ ‖x‖)) x =
      (S.indicator φ) ‖x‖ := by
    intro x
    by_cases h : ‖x‖ ∈ S <;> simp [indicator, h]
  simp_rw [this]
  rw [lintegral_radial hd _ (hφ.indicator hS)]
  congr 1
  have h2 : ∀ r : ℝ, ENNReal.ofReal (r ^ (d - 1)) * (S.indicator φ) r =
      S.indicator (fun r => ENNReal.ofReal (r ^ (d - 1)) * φ r) r := by
    intro r
    by_cases h : r ∈ S <;> simp [indicator, h]
  simp_rw [h2]
  rw [lintegral_indicator hS, Measure.restrict_restrict hS, inter_comm]


theorem lintegral_ball_rpow (hd : 1 ≤ d) {a r : ℝ} (hr : 0 < r) (ha : a < d) :
    ∫⁻ z in ball (0 : Euc d) r, ENNReal.ofReal (‖z‖ ^ (-a)) =
      ENNReal.ofReal (sphereArea d * (r ^ ((d : ℝ) - a) / ((d : ℝ) - a))) := by
  have hball : ball (0 : Euc d) r = {x : Euc d | ‖x‖ ∈ Iio r} := by
    ext x; simp
  rw [hball, lintegral_radial_set hd (Iio r) measurableSet_Iio
    (fun t => ENNReal.ofReal (t ^ (-a))) (by fun_prop)]
  have hsA : 0 ≤ sphereArea d := by
    unfold sphereArea
    have : 0 < Real.Gamma ((d : ℝ) / 2) := Real.Gamma_pos_of_pos (by
      have : (0 : ℝ) < d := by exact_mod_cast hd
      positivity)
    positivity
  have hda : 0 < (d : ℝ) - a := by linarith
  have h1 : Ioi (0 : ℝ) ∩ Iio r = Ioo 0 r := by ext; simp
  rw [h1, ENNReal.ofReal_mul hsA]
  congr 1
  have h2 : ∫⁻ t in Ioo (0 : ℝ) r, ENNReal.ofReal (t ^ (d - 1)) * ENNReal.ofReal (t ^ (-a)) =
      ∫⁻ t in Ioc (0 : ℝ) r, ENNReal.ofReal (t ^ ((d : ℝ) - 1 - a)) := by
    rw [← setLIntegral_congr Ioo_ae_eq_Ioc]
    refine setLIntegral_congr_fun measurableSet_Ioo fun t ht => ?_
    have ht0 : 0 < t := ht.1
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    have : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by
      rw [Nat.cast_sub hd]; simp
    rw [← Real.rpow_natCast, this, ← Real.rpow_add ht0]
    congr 1
  rw [h2]
  have hint : IntegrableOn (fun t : ℝ => t ^ ((d : ℝ) - 1 - a)) (Ioc 0 r) := by
    have := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := r)
      (r := (d : ℝ) - 1 - a) (by linarith))
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hr.le).1 this
  rw [← ofReal_integral_eq_lintegral_ofReal hint]
  · congr 1
    rw [← intervalIntegral.integral_of_le hr.le, integral_rpow (Or.inl (by linarith))]
    have : (d : ℝ) - 1 - a + 1 = (d : ℝ) - a := by ring
    rw [this, Real.zero_rpow hda.ne']
    simp
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact Real.rpow_nonneg ht.1.le _

theorem lintegral_compl_rpow (hd : 1 ≤ d) {b r : ℝ} (hr : 0 < r) (hb : (d : ℝ) < b) :
    ∫⁻ z in {z : Euc d | r ≤ ‖z‖}, ENNReal.ofReal (‖z‖ ^ (-b)) =
      ENNReal.ofReal (sphereArea d * (r ^ ((d : ℝ) - b) / (b - (d : ℝ)))) := by
  have hball : {z : Euc d | r ≤ ‖z‖} = {x : Euc d | ‖x‖ ∈ Ici r} := by
    ext x; simp
  rw [hball, lintegral_radial_set hd (Ici r) measurableSet_Ici
    (fun t => ENNReal.ofReal (t ^ (-b))) (by fun_prop)]
  have hsA : 0 ≤ sphereArea d := by
    unfold sphereArea
    have : 0 < Real.Gamma ((d : ℝ) / 2) := Real.Gamma_pos_of_pos (by
      have : (0 : ℝ) < d := by exact_mod_cast hd
      positivity)
    positivity
  have hbd : 0 < b - (d : ℝ) := by linarith
  have h1 : Ioi (0 : ℝ) ∩ Ici r = Ici r := by
    ext t; simp only [mem_inter_iff, mem_Ioi, mem_Ici]
    exact ⟨fun h => h.2, fun h => ⟨hr.trans_le h, h⟩⟩
  rw [h1, ENNReal.ofReal_mul hsA]
  congr 1
  have h2 : ∫⁻ t in Ici r, ENNReal.ofReal (t ^ (d - 1)) * ENNReal.ofReal (t ^ (-b)) =
      ∫⁻ t in Ioi r, ENNReal.ofReal (t ^ ((d : ℝ) - 1 - b)) := by
    rw [← setLIntegral_congr Ioi_ae_eq_Ici]
    refine setLIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have ht0 : 0 < t := hr.trans ht
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    have : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by
      rw [Nat.cast_sub hd]; simp
    rw [← Real.rpow_natCast, this, ← Real.rpow_add ht0]
    congr 1
  rw [h2]
  have hint : IntegrableOn (fun t : ℝ => t ^ ((d : ℝ) - 1 - b)) (Ioi r) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) hr
  rw [← ofReal_integral_eq_lintegral_ofReal hint]
  · congr 1
    rw [integral_Ioi_rpow_of_lt (by linarith) hr]
    have : (d : ℝ) - 1 - b + 1 = (d : ℝ) - b := by ring
    rw [this]
    have : (d : ℝ) - b ≠ 0 := by linarith
    field_simp
    ring
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact Real.rpow_nonneg (hr.trans ht).le _

theorem volume_ball_eq (hd : 1 ≤ d) {r : ℝ} (hr : 0 < r) :
    volume (ball (0 : Euc d) r) = ENNReal.ofReal (sphereArea d * (r ^ d / d)) := by
  have h := lintegral_ball_rpow (d := d) hd (a := 0) hr (by exact_mod_cast hd)
  simp only [neg_zero, Real.rpow_zero, ENNReal.ofReal_one, lintegral_const, Measure.restrict_apply,
    MeasurableSet.univ, univ_inter, one_mul] at h
  rw [h]
  simp [sub_zero]

end HRS.Whole.Q34
