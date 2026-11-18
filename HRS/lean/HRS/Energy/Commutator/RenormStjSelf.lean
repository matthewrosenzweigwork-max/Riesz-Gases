import HRS.Energy.Commutator.RenormStjCharges

/-!
# Route S, packet STJ: self energy of the slice charge, an `l`-independent dominating measure
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators
open HRS.Commutator.Renorm

namespace HRS.Commutator.Stj

variable {d : ℕ}

/-! ### Radial integrals -/

theorem radial_Ioc_integral {α ρ : ℝ} (hd : 1 ≤ d) (hα : -(d : ℝ) < α) (hρ : 0 < ρ) :
    ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ (d - 1)) *
        (if t ≤ ρ then ENNReal.ofReal (t ^ α) else 0) =
      ENNReal.ofReal (ρ ^ ((d : ℝ) + α) / ((d : ℝ) + α)) := by
  have hdα : 0 < (d : ℝ) + α := by linarith
  have h1 : ∀ t ∈ Ioi (0 : ℝ), ENNReal.ofReal (t ^ (d - 1)) *
      (if t ≤ ρ then ENNReal.ofReal (t ^ α) else 0) =
      (Ioc 0 ρ).indicator (fun t => ENNReal.ofReal (t ^ ((d : ℝ) - 1 + α))) t := by
    intro t ht
    have ht0 : 0 < t := ht
    by_cases htρ : t ≤ ρ
    · rw [if_pos htρ, indicator_of_mem (show t ∈ Ioc 0 ρ from ⟨ht0, htρ⟩),
        ← ENNReal.ofReal_mul (pow_nonneg ht0.le _)]
      congr 1
      rw [Real.rpow_add ht0]
      congr 1
      rw [← Real.rpow_natCast]; congr 1; rw [Nat.cast_sub hd]; simp
    · rw [if_neg htρ, indicator_of_notMem (show t ∉ Ioc 0 ρ from fun h => htρ h.2)]; simp
  rw [setLIntegral_congr_fun measurableSet_Ioi h1, lintegral_indicator measurableSet_Ioc,
    Measure.restrict_restrict measurableSet_Ioc]
  have : Ioc 0 ρ ∩ Ioi 0 = Ioc 0 ρ := by
    ext t; simp only [mem_inter_iff, mem_Ioc, mem_Ioi]; tauto
  rw [this]
  have hint : IntervalIntegrable (fun t : ℝ => t ^ ((d : ℝ) - 1 + α)) volume 0 ρ :=
    intervalIntegral.intervalIntegrable_rpow' (by linarith)
  have hint' : IntegrableOn (fun t : ℝ => t ^ ((d : ℝ) - 1 + α)) (Ioc 0 ρ) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hρ.le).mp hint
  rw [← ofReal_integral_eq_lintegral_ofReal hint'
    ((ae_restrict_iff' measurableSet_Ioc).mpr (Filter.Eventually.of_forall fun t ht =>
      Real.rpow_nonneg ht.1.le _))]
  congr 1
  rw [← intervalIntegral.integral_of_le hρ.le, integral_rpow (Or.inl (by linarith))]
  rw [Real.zero_rpow (by linarith : (d : ℝ) - 1 + α + 1 ≠ 0), sub_zero]
  have : (d : ℝ) - 1 + α + 1 = (d : ℝ) + α := by ring
  rw [this]

theorem lintegral_closedBall_rpow (hd : 1 ≤ d) {α ρ : ℝ} (hα : -(d : ℝ) < α) (hρ : 0 < ρ) :
    ∫⁻ w in Metric.closedBall (0 : Euc d) ρ, ENNReal.ofReal (‖w‖ ^ α) =
      (volume : Measure (Euc d)).toSphere univ * ENNReal.ofReal (ρ ^ ((d : ℝ) + α) / ((d : ℝ) + α)) := by
  rw [← lintegral_indicator Metric.isClosed_closedBall.measurableSet]
  have hm : Measurable ((Metric.closedBall (0 : Euc d) ρ).indicator (fun w : Euc d => ENNReal.ofReal (‖w‖ ^ α))) :=
    (ENNReal.measurable_ofReal.comp (measurable_norm.pow_const _)).indicator Metric.isClosed_closedBall.measurableSet
  rw [lintegral_polar_euc hd _ hm]
  have e1 : ∀ ω : Metric.sphere (0 : Euc d) 1,
      (∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ (d - 1)) *
        (Metric.closedBall (0 : Euc d) ρ).indicator (fun w : Euc d => ENNReal.ofReal (‖w‖ ^ α)) (t • (ω : Euc d))) =
      ENNReal.ofReal (ρ ^ ((d : ℝ) + α) / ((d : ℝ) + α)) := by
    intro ω
    rw [← radial_Ioc_integral hd hα hρ]
    have hω : ‖(ω : Euc d)‖ = 1 := by simp
    refine setLIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have ht0 : 0 < t := ht
    have hn : ‖t • (ω : Euc d)‖ = t := by rw [norm_smul, hω, mul_one, Real.norm_eq_abs, abs_of_pos ht0]
    by_cases htρ : t ≤ ρ
    · rw [indicator_of_mem (by simpa [hn] using htρ), hn, if_pos htρ]
    · rw [indicator_of_notMem (by simpa [hn] using htρ), if_neg htρ]
  simp_rw [e1]
  rw [lintegral_const]
  simp [mul_comm]

/-! ### The `l`-independent dominating measure -/

/-- ball part of the slice charge (`l`-independent) -/
def ballT (d : ℕ) (η : ℝ) : Measure (Torus d) :=
  ((volume : Measure (Euc d)).restrict (Metric.closedBall 0 η)).map Torus.mk

/-- sphere part of the slice charge (`l`-independent, total mass `|S^{d-1}|`) -/
def sphT (d : ℕ) (η : ℝ) : Measure (Torus d) :=
  (((volume : Measure (Euc d)).toSphere).map (fun ω : Metric.sphere (0 : Euc d) 1 => η • (ω : Euc d))).map
    Torus.mk

theorem smearT_eq (l η : ℝ) :
    smearT d l η = ENNReal.ofReal (l * yukawa d l η) • ballT d η +
      ENNReal.ofReal (cfl d l η) • sphT d η := by
  unfold smearT smearEuc ballT sphT cfl
  rw [Measure.map_add _ _ Torus.continuous_mk.measurable, Measure.map_smul, Measure.map_smul]
  all_goals exact Torus.continuous_mk.measurable.aemeasurable

/-- the dominating measure `σ_{l,η} ≤ domT η` for all `l > 0` -/
def domT (d : ℕ) (η : ℝ) : Measure (Torus d) :=
  ENNReal.ofReal (1 / (η ^ d * (volume : Measure (Euc d)).real (Metric.ball 0 1))) • ballT d η +
    ENNReal.ofReal (1 / (volume : Measure (Euc d)).toSphere.real univ) • sphT d η

theorem smearT_le_domT (hd : 1 ≤ d) {l η : ℝ} (hl : 0 < l) (hη : 0 < η) (hη2 : η < 1 / 2) :
    smearT d l η ≤ domT d η := by
  rw [smearT_eq]
  unfold domT
  have hω : 0 < (volume : Measure (Euc d)).real (Metric.ball 0 1) := by
    have : Nontrivial (Euc d) := Module.nontrivial_of_finrank_pos (R := ℝ) (by simp; omega)
    rw [measureReal_def]
    exact ENNReal.toReal_pos (Metric.measure_ball_pos _ _ one_pos).ne' measure_ball_lt_top.ne
  have hS : 0 < (volume : Measure (Euc d)).toSphere.real univ := by
    have : Nontrivial (Euc d) := Module.nontrivial_of_finrank_pos (R := ℝ) (by simp; omega)
    have h := SmearAux.kappa_mul hd
    have hk := SmearAux.kappa_pos d hd
    by_contra hc
    push Not at hc
    have h0 : (volume : Measure (Euc d)).toSphere.real univ = 0 := le_antisymm hc measureReal_nonneg
    rw [h0, zero_mul] at h
    exact zero_ne_one h
  have h1 : l * yukawa d l η ≤ 1 / (η ^ d * (volume : Measure (Euc d)).real (Metric.ball 0 1)) := by
    have := ball_coef_le_mass hd hl hη
    have h2 := mass_le_one hd hl hη hη2
    rw [le_div_iff₀ (by positivity)]
    nlinarith [this, h2]
  have h2 : cfl d l η ≤ 1 / (volume : Measure (Euc d)).toSphere.real univ := by
    have := sphere_coef_le hd hl hη
    rw [le_div_iff₀ hS]
    nlinarith [this]
  refine add_le_add ?_ ?_
  · refine fun s => ?_
    simp only [Measure.smul_apply, smul_eq_mul]
    exact mul_le_mul' (ENNReal.ofReal_le_ofReal h1) le_rfl
  · refine fun s => ?_
    simp only [Measure.smul_apply, smul_eq_mul]
    exact mul_le_mul' (ENNReal.ofReal_le_ofReal h2) le_rfl

instance isFiniteMeasure_ballT (d : ℕ) (η : ℝ) : IsFiniteMeasure (ballT d η) := by
  unfold ballT
  haveI : IsFiniteMeasure ((volume : Measure (Euc d)).restrict (Metric.closedBall 0 η)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_closedBall_lt_top⟩
  infer_instance

instance isFiniteMeasure_sphT (d : ℕ) (η : ℝ) : IsFiniteMeasure (sphT d η) := by
  unfold sphT
  infer_instance

instance sFinite_domT (d : ℕ) (η : ℝ) : SFinite (domT d η) := by
  unfold domT
  infer_instance

theorem lintegral_ballT {η : ℝ} {F : Torus d → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ z, F z ∂(ballT d η) = ∫⁻ w in Metric.closedBall (0 : Euc d) η, F (Torus.mk w) :=
  lintegral_map hF Torus.continuous_mk.measurable

theorem lintegral_sphT {η : ℝ} {F : Torus d → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ z, F z ∂(sphT d η) =
      ∫⁻ ω : Metric.sphere (0 : Euc d) 1, F (Torus.mk (η • (ω : Euc d))) ∂((volume : Measure (Euc d)).toSphere) := by
  unfold sphT
  rw [lintegral_map hF Torus.continuous_mk.measurable]
  exact lintegral_map (f := fun a : Euc d => F (Torus.mk a)) (hF.comp Torus.continuous_mk.measurable)
    (EnergyAux.measurable_sphere_smul η)

theorem lintegral_domT {η : ℝ} {F : Torus d → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ z, F z ∂(domT d η) =
      ENNReal.ofReal (1 / (η ^ d * (volume : Measure (Euc d)).real (Metric.ball 0 1))) *
        (∫⁻ w in Metric.closedBall (0 : Euc d) η, F (Torus.mk w)) +
      ENNReal.ofReal (1 / (volume : Measure (Euc d)).toSphere.real univ) *
        ∫⁻ ω : Metric.sphere (0 : Euc d) 1, F (Torus.mk (η • (ω : Euc d))) ∂((volume : Measure (Euc d)).toSphere) := by
  unfold domT
  rw [lintegral_add_measure, lintegral_smul_measure, lintegral_smul_measure, lintegral_ballT hF,
    lintegral_sphT hF]
  simp only [smul_eq_mul]

theorem lintegral_cb_le (hd : 1 ≤ d) {η : ℝ} (hη : 0 < η) (hη8 : η ≤ 1 / 8) {F : Torus d → ℝ≥0∞}
    (hF : Measurable F) :
    ∫⁻ w in Metric.closedBall (0 : Euc d) η, F (Torus.mk w) ≤ ∫⁻ z, F z := by
  set f : Torus d → ℝ≥0∞ := fun z => if KernelGrad.tdist z 0 < 1 / 4 then F z else 0 with hf
  have hfm : Measurable f :=
    Measurable.ite (measurableSet_lt EnergyAux.measurable_tdist_zero measurable_const) hF measurable_const
  have h1 : ∫⁻ z, f z = ∫⁻ w in Metric.ball (0 : Euc d) (1 / 4), f (Torus.mk w) :=
    lintegral_torus_ball (by norm_num) f (fun z hz => by simp only [hf]; rw [if_neg (not_lt.mpr hz)])
  have h2 : ∫⁻ w in Metric.closedBall (0 : Euc d) η, F (Torus.mk w) ≤
      ∫⁻ w in Metric.ball (0 : Euc d) (1 / 4), F (Torus.mk w) :=
    lintegral_mono_set (Metric.closedBall_subset_ball (by linarith))
  have h3 : ∫⁻ w in Metric.ball (0 : Euc d) (1 / 4), F (Torus.mk w) =
      ∫⁻ w in Metric.ball (0 : Euc d) (1 / 4), f (Torus.mk w) := by
    refine setLIntegral_congr_fun Metric.isOpen_ball.measurableSet fun w hw => ?_
    have hw' : ‖w‖ < 1 / 4 := by simpa using hw
    have hy : ∀ i, |w i| ≤ 1 / 2 := fun i => by
      have h1 := PiLp.norm_apply_le w i
      have := (le_of_eq (by simp [Real.norm_eq_abs] : |w i| = ‖w i‖)).trans h1
      linarith
    simp only [hf]
    rw [KernelGrad.tdist_mk hy, if_pos hw']
  rw [← h1] at h3
  refine h2.trans (h3.le.trans ?_)
  exact lintegral_mono fun z => by simp only [hf]; split_ifs <;> simp

theorem Gdom_lt_top (hd : 1 ≤ d) {l η : ℝ} (hl : 0 < l) (hη : 0 < η) (hη8 : η ≤ 1 / 8) :
    ∫⁻ z, ENNReal.ofReal |sliceG d l z| ∂(domT d η) < ⊤ := by
  have hF : Measurable fun z : Torus d => ENNReal.ofReal |sliceG d l z| :=
    ENNReal.measurable_ofReal.comp (EnergyAux.measurable_sliceG l).abs
  rw [lintegral_domT hF]
  refine ENNReal.add_lt_top.mpr ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_, ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_⟩
  · refine lt_of_le_of_lt (lintegral_cb_le hd hη hη8 hF) ?_
    have := (RoughKernel.integrable_sliceG (d := d) hl.le).hasFiniteIntegral
    unfold HasFiniteIntegral at this
    have e : ∀ z : Torus d, ENNReal.ofReal |sliceG d l z| = ‖sliceG d l z‖ₑ := fun z => by
      rw [← Real.norm_eq_abs, ofReal_norm]
    simp only [e]
    exact this
  · obtain ⟨B, hB⟩ := EnergyAux.sliceG_bdd_away (d := d) hl.le (half_pos hη)
    have hbd : ∀ ω : Metric.sphere (0 : Euc d) 1, ENNReal.ofReal |sliceG d l (Torus.mk (η • (ω : Euc d)))| ≤
        ENNReal.ofReal B := by
      intro ω
      refine ENNReal.ofReal_le_ofReal (hB _ ?_)
      have hn : ‖η • (ω : Euc d)‖ = η := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hη]
        have : ‖(ω : Euc d)‖ = 1 := by simpa using ω.2
        rw [this, mul_one]
      have hy : ∀ i, |(η • (ω : Euc d)) i| ≤ 1 / 2 := fun i => by
        have h1 := PiLp.norm_apply_le (η • (ω : Euc d)) i
        have := (le_of_eq (by simp [Real.norm_eq_abs] : |(η • (ω : Euc d)) i| = ‖(η • (ω : Euc d)) i‖)).trans h1
        rw [hn] at this
        linarith
      rw [KernelGrad.tdist_mk hy, hn]
      linarith
    refine lt_of_le_of_lt (lintegral_mono hbd) ?_
    rw [lintegral_const]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)

theorem integrable_G_smearT (hd : 1 ≤ d) {l η : ℝ} (hl : 0 < l) (hη : 0 < η) (hη2 : η < 1 / 2) :
    Integrable (sliceGfull d l) (smearT d l η) :=
  (lintegral_ofReal_ne_top_iff_integrable (EnergyAux.measurable_sliceGfull l).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => EnergyAux.sliceGfull_nonneg hl x)).mp
    (EnergyAux.lintegral_smearT_g_lt_top hd hl hη hη2).ne

theorem Self_le (hd : 1 ≤ d) {l η : ℝ} (hl : 0 < l) (hη : 0 < η) (hη2 : η < 1 / 2) :
    Self d l η ≤ ∫ x, |sliceG d l x| ∂(smearT d l η) + ∫ z : Torus d, fTrunc d l η z := by
  set σ := smearT d l η with hσ
  haveI : IsFiniteMeasure σ := (smearT_structure hd hl hη hη2).1
  have hGi := integrable_G_smearT hd hl hη hη2
  have h0 : ∀ᵐ x ∂σ, x ≠ 0 := by
    rw [ae_iff]; simpa using EnergyAux.smearT_singleton_zero hd hη hη2
  have hfd : ∀ x, 0 ≤ fTrunc d l η x := fun x => le_max_right _ _
  have hfle : ∀ᵐ x ∂σ, fTrunc d l η x ≤ sliceGfull d l x := by
    filter_upwards [h0] with x hx
    have := EnergyAux.g_sub_f_pos hd hl hη hx
    linarith
  have hfi : Integrable (fTrunc d l η) σ := by
    refine Integrable.mono' hGi (EnergyAux.measurable_fTrunc l η).aestronglyMeasurable ?_
    filter_upwards [hfle] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (hfd x)]; exact hx
  have hinner : ∀ᵐ x ∂σ, ∫ y, sliceGfull d l (x - y) ∂σ = sliceGfull d l x - fTrunc d l η x := by
    filter_upwards [h0] with x hx
    exact sliceGfull_conv_smear hd hl hη hη2 x hx
  have hdbl : ∫ x, ∫ y, sliceGfull d l (x - y) ∂σ ∂σ =
      ∫ x, sliceGfull d l x ∂σ - ∫ x, fTrunc d l η x ∂σ := by
    rw [integral_congr_ae hinner, integral_sub hGi hfi]
  have hGi' : Integrable (sliceG d l) σ := by
    have := hGi.sub (integrable_const (1 / l))
    refine this.congr (Filter.Eventually.of_forall fun x => ?_)
    simp [sliceGfull]
  have hGsplit : ∫ x, sliceGfull d l x ∂σ = ∫ x, sliceG d l x ∂σ + (mass d l η) / l := by
    have e : ∀ x, sliceGfull d l x = sliceG d l x + 1 / l := fun x => rfl
    simp_rw [e]
    rw [integral_add hGi' (integrable_const _), integral_const]
    simp only [smul_eq_mul]
    rw [show σ.real univ = mass d l η from rfl]
    ring
  have hm := smearT_real_univ hd hl hη hη2
  have hmass : mass d l η = 1 - l * ∫ z : Torus d, fTrunc d l η z := hm
  have hF0 : 0 ≤ ∫ z : Torus d, fTrunc d l η z := integral_nonneg hfd
  have hm0 := mass_nonneg d l η
  have hm1 := mass_le_one hd hl hη hη2
  have habs : ∫ x, sliceG d l x ∂σ ≤ ∫ x, |sliceG d l x| ∂σ :=
    integral_mono hGi' hGi'.abs fun x => le_abs_self _
  have hfs : 0 ≤ ∫ x, fTrunc d l η x ∂σ := integral_nonneg hfd
  unfold Self
  rw [hdbl, hGsplit]
  have key : mass d l η / l - mass d l η ^ 2 / l = mass d l η * ∫ z : Torus d, fTrunc d l η z := by
    rw [hmass]; field_simp; ring
  have h2 : mass d l η * ∫ z : Torus d, fTrunc d l η z ≤ ∫ z : Torus d, fTrunc d l η z := by
    nlinarith
  linarith

theorem ball_real_pos (hd : 1 ≤ d) : 0 < (volume : Measure (Euc d)).real (Metric.ball 0 1) := by
  have : Nontrivial (Euc d) := Module.nontrivial_of_finrank_pos (R := ℝ) (by simp; omega)
  rw [measureReal_def]
  exact ENNReal.toReal_pos (Metric.measure_ball_pos _ _ one_pos).ne' measure_ball_lt_top.ne

theorem sphere_real_pos (hd : 1 ≤ d) : 0 < (volume : Measure (Euc d)).toSphere.real univ := by
  have h := SmearAux.kappa_mul hd
  by_contra hc
  push Not at hc
  have h0 : (volume : Measure (Euc d)).toSphere.real univ = 0 := le_antisymm hc measureReal_nonneg
  rw [h0, zero_mul] at h
  exact zero_ne_one h

theorem domT_zero (hd : 1 ≤ d) {η : ℝ} (hη : 0 < η) (hη2 : η < 1 / 2) : domT d η {0} = 0 := by
  have : Nontrivial (Euc d) := Module.nontrivial_of_finrank_pos (R := ℝ) (by simp; omega)
  have hms : MeasurableSet ({0} : Set (Torus d)) := measurableSet_singleton _
  have hF : Measurable (({0} : Set (Torus d)).indicator (fun _ => (1 : ℝ≥0∞))) :=
    measurable_const.indicator hms
  have h0 : ∫⁻ x, ({0} : Set (Torus d)).indicator (fun _ => (1 : ℝ≥0∞)) x ∂(domT d η) = domT d η {0} := by
    rw [lintegral_indicator hms]; simp
  rw [← h0, lintegral_domT hF]
  have h1 : (∫⁻ w in Metric.closedBall (0 : Euc d) η,
      ({0} : Set (Torus d)).indicator (fun _ => (1 : ℝ≥0∞)) (Torus.mk w)) = 0 := by
    refine le_antisymm ?_ bot_le
    calc _ ≤ ∫⁻ w in Metric.closedBall (0 : Euc d) η, ({0} : Set (Euc d)).indicator (fun _ => (1 : ℝ≥0∞)) w := by
          refine setLIntegral_mono' Metric.isClosed_closedBall.measurableSet fun w hwb => ?_
          by_cases hw : Torus.mk w = 0
          · have hwn : ‖w‖ ≤ η := by simpa using hwb
            have := EnergyAux.mk_eq_zero_of_norm_lt_one hw (by linarith)
            subst this
            show ({0} : Set (Torus d)).indicator (fun _ => (1 : ℝ≥0∞)) (Torus.mk 0) ≤
              ({0} : Set (Euc d)).indicator (fun _ => (1 : ℝ≥0∞)) 0
            rw [hw, Set.indicator_of_mem (Set.mem_singleton _), Set.indicator_of_mem (Set.mem_singleton _)]
          · simp [hw]
      _ ≤ ∫⁻ w, ({0} : Set (Euc d)).indicator (fun _ => (1 : ℝ≥0∞)) w := setLIntegral_le_lintegral _ _
      _ = 0 := by
          rw [lintegral_indicator (measurableSet_singleton _)]
          simp
  have h2 : (∫⁻ ω : Metric.sphere (0 : Euc d) 1,
      ({0} : Set (Torus d)).indicator (fun _ => (1 : ℝ≥0∞)) (Torus.mk (η • (ω : Euc d)))
        ∂((volume : Measure (Euc d)).toSphere)) = 0 := by
    have : ∀ ω : Metric.sphere (0 : Euc d) 1,
        ({0} : Set (Torus d)).indicator (fun _ => (1 : ℝ≥0∞)) (Torus.mk (η • (ω : Euc d))) = 0 := by
      intro ω
      have hn : ‖η • (ω : Euc d)‖ = η := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hη]
        have : ‖(ω : Euc d)‖ = 1 := by simpa using ω.2
        rw [this, mul_one]
      by_cases hz : Torus.mk (η • (ω : Euc d)) = 0
      · exfalso
        have := EnergyAux.mk_eq_zero_of_norm_lt_one hz (by rw [hn]; linarith)
        rw [this] at hn
        simp at hn
        linarith
      · simp [hz]
    simp [this]
  rw [h1, h2]; simp

theorem Self_le_dom (hd : 1 ≤ d) {l η : ℝ} (hl : 0 < l) (hη : 0 < η) (hη8 : η ≤ 1 / 8) :
    Self d l η ≤ (∫⁻ z, ENNReal.ofReal |sliceG d l z| ∂(domT d η)).toReal + ∫ z : Torus d, fTrunc d l η z := by
  have hη2 : η < 1 / 2 := by linarith
  refine (Self_le hd hl hη hη2).trans ?_
  refine add_le_add ?_ le_rfl
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun x => abs_nonneg _)
    (EnergyAux.measurable_sliceG l).abs.aestronglyMeasurable]
  exact ENNReal.toReal_mono (Gdom_lt_top hd hl hη hη8).ne
    (lintegral_mono' (smearT_le_domT hd hl hη hη2) le_rfl)

theorem Gdom_integral (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 < s) (hs : (d : ℝ) - 2 < s) (hsd : s < d) {c : ℝ}
    (hc : 0 < c)
    (hker : ∀ x : Torus d, x ≠ 0 →
      periodicRiesz d s x = c * ∫ l in Ioi (0 : ℝ), l ^ (-bexp d s) * sliceG d l x) :
    ∃ CU : ℝ, 0 ≤ CU ∧ ∀ η : ℝ, 0 < η → η ≤ 1 / 8 →
      ∫⁻ l in Ioi (0 : ℝ), ENNReal.ofReal (l ^ (-bexp d s)) *
          ∫⁻ z, ENNReal.ofReal |sliceG d l z| ∂(domT d η) ≤
        ENNReal.ofReal (CU * (η ^ (-s) + 1)) := by
  obtain ⟨CT, hCT0, hCT⟩ := Theta_bound hd hs0.le hs hsd hc hker
  have hω := ball_real_pos hd
  have hS := sphere_real_pos hd
  have hdr : (0 : ℝ) < d := by exact_mod_cast hd
  set ω := (volume : Measure (Euc d)).real (Metric.ball 0 1) with hωdef
  set S := (volume : Measure (Euc d)).toSphere.real univ with hSdef
  have hds : 0 < (d : ℝ) - s := by linarith
  refine ⟨S / (c * ω * ((d : ℝ) - s)) + c⁻¹ + 2 * CT, by positivity, fun η hη hη8 => ?_⟩
  have hη2 : η < 1 / 2 := by linarith
  have hsc : ∀ r : ℝ, selfScale d s r = r ^ (-s) := fun r => by unfold selfScale; rw [if_neg hs0.ne']
  -- Tonelli
  have hK : Measurable (Function.uncurry fun (l : ℝ) (z : Torus d) => ENNReal.ofReal |sliceG d l z|) :=
    ENNReal.measurable_ofReal.comp (measurable_sliceG_uncurry d).abs
  have hK2 : Measurable (Function.uncurry fun (l : ℝ) (z : Torus d) =>
      ENNReal.ofReal (l ^ (-bexp d s)) * ENNReal.ofReal |sliceG d l z|) :=
    (ENNReal.measurable_ofReal.comp (measurable_fst.pow_const _)).mul hK
  have hswap : ∫⁻ l in Ioi (0 : ℝ), ENNReal.ofReal (l ^ (-bexp d s)) *
      ∫⁻ z, ENNReal.ofReal |sliceG d l z| ∂(domT d η) =
      ∫⁻ z, (∫⁻ l in Ioi (0 : ℝ), ENNReal.ofReal (l ^ (-bexp d s)) * ENNReal.ofReal |sliceG d l z|) ∂(domT d η) := by
    have e : ∀ l : ℝ, ENNReal.ofReal (l ^ (-bexp d s)) * ∫⁻ z, ENNReal.ofReal |sliceG d l z| ∂(domT d η) =
        ∫⁻ z, ENNReal.ofReal (l ^ (-bexp d s)) * ENNReal.ofReal |sliceG d l z| ∂(domT d η) := fun l =>
      (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm
    simp_rw [e]
    exact lintegral_lintegral_swap hK2.aemeasurable
  rw [hswap]
  have hae : ∀ᵐ z ∂(domT d η), z ≠ 0 := by
    rw [ae_iff]; simpa using domT_zero hd hη hη2
  have hstep : ∫⁻ z, (∫⁻ l in Ioi (0 : ℝ), ENNReal.ofReal (l ^ (-bexp d s)) * ENNReal.ofReal |sliceG d l z|) ∂(domT d η) ≤
      ∫⁻ z, ENNReal.ofReal (c⁻¹ * (KernelGrad.tdist z 0) ^ (-s) + CT) ∂(domT d η) := by
    refine lintegral_mono_ae (hae.mono fun z hz => ?_)
    obtain ⟨hI, hJ⟩ := hCT z hz
    have e : ∀ l ∈ Ioi (0 : ℝ), ENNReal.ofReal (l ^ (-bexp d s)) * ENNReal.ofReal |sliceG d l z| =
        ENNReal.ofReal (l ^ (-bexp d s) * |sliceG d l z|) := fun l hl =>
      (ENNReal.ofReal_mul (Real.rpow_nonneg (le_of_lt (show (0 : ℝ) < l from hl)) _)).symm
    rw [setLIntegral_congr_fun measurableSet_Ioi e,
      ← ofReal_integral_eq_lintegral_ofReal hI
        ((ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun l hl =>
          mul_nonneg (Real.rpow_nonneg (le_of_lt (show (0 : ℝ) < l from hl)) _) (abs_nonneg _)))]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [hsc] at hJ
    exact hJ
  refine hstep.trans ?_
  have hF : Measurable fun z : Torus d => ENNReal.ofReal (c⁻¹ * (KernelGrad.tdist z 0) ^ (-s) + CT) :=
    ENNReal.measurable_ofReal.comp
      ((measurable_const.mul (EnergyAux.measurable_tdist_zero.pow_const _)).add measurable_const)
  rw [lintegral_domT hF]
  -- the ball part
  have htd : ∀ w ∈ Metric.closedBall (0 : Euc d) η, KernelGrad.tdist (Torus.mk w) 0 = ‖w‖ := by
    intro w hw
    have hwn : ‖w‖ ≤ η := by simpa using hw
    have hy : ∀ i, |w i| ≤ 1 / 2 := fun i => by
      have h1 := PiLp.norm_apply_le w i
      have := (le_of_eq (by simp [Real.norm_eq_abs] : |w i| = ‖w i‖)).trans h1
      linarith
    exact KernelGrad.tdist_mk hy
  have hball : ∫⁻ w in Metric.closedBall (0 : Euc d) η, ENNReal.ofReal (c⁻¹ * (KernelGrad.tdist (Torus.mk w) 0) ^ (-s) + CT) ≤
      ENNReal.ofReal (c⁻¹ * (S * (η ^ ((d : ℝ) + -s) / ((d : ℝ) + -s))) + CT * (η ^ d * ω)) := by
    have h1 : ∫⁻ w in Metric.closedBall (0 : Euc d) η, ENNReal.ofReal (c⁻¹ * (KernelGrad.tdist (Torus.mk w) 0) ^ (-s) + CT) =
        ∫⁻ w in Metric.closedBall (0 : Euc d) η, ENNReal.ofReal (c⁻¹ * ‖w‖ ^ (-s) + CT) :=
      setLIntegral_congr_fun Metric.isClosed_closedBall.measurableSet fun w hw => by rw [htd w hw]
    rw [h1]
    have h2 : ∀ w : Euc d, ENNReal.ofReal (c⁻¹ * ‖w‖ ^ (-s) + CT) ≤
        ENNReal.ofReal c⁻¹ * ENNReal.ofReal (‖w‖ ^ (-s)) + ENNReal.ofReal CT := fun w => by
      refine (ENNReal.ofReal_add_le).trans ?_
      rw [ENNReal.ofReal_mul (inv_nonneg.mpr hc.le)]
    refine (lintegral_mono h2).trans ?_
    have hm1 : Measurable fun w : Euc d => ENNReal.ofReal c⁻¹ * ENNReal.ofReal (‖w‖ ^ (-s)) :=
      measurable_const.mul (ENNReal.measurable_ofReal.comp (measurable_norm.pow_const _))
    rw [lintegral_add_left hm1, lintegral_const_mul (f := fun w : Euc d => ENNReal.ofReal (‖w‖ ^ (-s))) _ (ENNReal.measurable_ofReal.comp (measurable_norm.pow_const _)),
      lintegral_closedBall_rpow hd (by linarith) hη, setLIntegral_const]
    have hvol : (volume : Measure (Euc d)) (Metric.closedBall 0 η) = ENNReal.ofReal (η ^ d * ω) := by
      have : Nontrivial (Euc d) := Module.nontrivial_of_finrank_pos (R := ℝ) (by simp; omega)
      rw [Measure.addHaar_closedBall _ _ hη.le, ENNReal.ofReal_mul (by positivity), hωdef, measureReal_def,
        ENNReal.ofReal_toReal measure_ball_lt_top.ne]
      simp
    rw [hvol]
    have hSE : (volume : Measure (Euc d)).toSphere univ = ENNReal.ofReal S := by
      rw [hSdef, measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]
    rw [hSE]
    have hpos1 : 0 < η ^ ((d : ℝ) + -s) / ((d : ℝ) + -s) := by
      have : 0 < (d : ℝ) + -s := by linarith
      positivity
    have hn1 : 0 ≤ c⁻¹ * (S * (η ^ ((d : ℝ) + -s) / ((d : ℝ) + -s))) := by positivity
    have hn2 : 0 ≤ CT * (η ^ d * ω) := by positivity
    refine le_of_eq ?_
    rw [ENNReal.ofReal_add hn1 hn2, ENNReal.ofReal_mul (inv_nonneg.mpr hc.le), ENNReal.ofReal_mul hS.le,
      ENNReal.ofReal_mul hCT0]
  -- the sphere part
  have hsph : ∫⁻ ω' : Metric.sphere (0 : Euc d) 1, ENNReal.ofReal (c⁻¹ * (KernelGrad.tdist (Torus.mk (η • (ω' : Euc d))) 0) ^ (-s) + CT)
      ∂((volume : Measure (Euc d)).toSphere) = ENNReal.ofReal (c⁻¹ * η ^ (-s) + CT) * ENNReal.ofReal S := by
    have hconst : ∀ ω' : Metric.sphere (0 : Euc d) 1,
        ENNReal.ofReal (c⁻¹ * (KernelGrad.tdist (Torus.mk (η • (ω' : Euc d))) 0) ^ (-s) + CT) =
        ENNReal.ofReal (c⁻¹ * η ^ (-s) + CT) := by
      intro ω'
      have hn : ‖η • (ω' : Euc d)‖ = η := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hη]
        have : ‖(ω' : Euc d)‖ = 1 := by simpa using ω'.2
        rw [this, mul_one]
      have hy : ∀ i, |(η • (ω' : Euc d)) i| ≤ 1 / 2 := fun i => by
        have h1 := PiLp.norm_apply_le (η • (ω' : Euc d)) i
        have := (le_of_eq (by simp [Real.norm_eq_abs] : |(η • (ω' : Euc d)) i| = ‖(η • (ω' : Euc d)) i‖)).trans h1
        rw [hn] at this
        linarith
      rw [KernelGrad.tdist_mk hy, hn]
    simp_rw [hconst]
    rw [lintegral_const]
    have hSE : (volume : Measure (Euc d)).toSphere univ = ENNReal.ofReal S := by
      rw [hSdef, measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]
    rw [hSE]
  rw [hsph]
  have hc1 : ENNReal.ofReal (1 / (η ^ d * ω)) * ENNReal.ofReal (c⁻¹ * (S * (η ^ ((d : ℝ) + -s) / ((d : ℝ) + -s))) +
      CT * (η ^ d * ω)) = ENNReal.ofReal (S / (c * ω * ((d : ℝ) - s)) * η ^ (-s) + CT) := by
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    have hpow : η ^ ((d : ℝ) + -s) = η ^ d * η ^ (-s) := by
      rw [Real.rpow_add hη, Real.rpow_natCast]
    rw [hpow]
    have hηd : 0 < η ^ d := pow_pos hη d
    have hds' : (d : ℝ) + -s = (d : ℝ) - s := by ring
    rw [hds']
    field_simp
  have hc2 : ENNReal.ofReal (1 / S) * (ENNReal.ofReal (c⁻¹ * η ^ (-s) + CT) * ENNReal.ofReal S) =
      ENNReal.ofReal (c⁻¹ * η ^ (-s) + CT) := by
    rw [mul_comm (ENNReal.ofReal (c⁻¹ * η ^ (-s) + CT)), ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
    have : 1 / S * S = 1 := by field_simp
    rw [this, ENNReal.ofReal_one, one_mul]
  calc ENNReal.ofReal (1 / (η ^ d * ω)) * (∫⁻ w in Metric.closedBall (0 : Euc d) η,
        ENNReal.ofReal (c⁻¹ * (KernelGrad.tdist (Torus.mk w) 0) ^ (-s) + CT)) +
        ENNReal.ofReal (1 / S) * (ENNReal.ofReal (c⁻¹ * η ^ (-s) + CT) * ENNReal.ofReal S)
      ≤ ENNReal.ofReal (1 / (η ^ d * ω)) * ENNReal.ofReal (c⁻¹ * (S * (η ^ ((d : ℝ) + -s) / ((d : ℝ) + -s))) +
          CT * (η ^ d * ω)) + ENNReal.ofReal (1 / S) * (ENNReal.ofReal (c⁻¹ * η ^ (-s) + CT) * ENNReal.ofReal S) :=
        add_le_add (mul_le_mul' le_rfl hball) le_rfl
    _ = ENNReal.ofReal (S / (c * ω * ((d : ℝ) - s)) * η ^ (-s) + CT) + ENNReal.ofReal (c⁻¹ * η ^ (-s) + CT) := by
        rw [hc1, hc2]
    _ ≤ ENNReal.ofReal ((S / (c * ω * ((d : ℝ) - s)) + c⁻¹ + 2 * CT) * (η ^ (-s) + 1)) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        refine ENNReal.ofReal_le_ofReal ?_
        have hp : 0 ≤ η ^ (-s) := Real.rpow_nonneg hη.le _
        have hA : 0 ≤ S / (c * ω * ((d : ℝ) - s)) := by positivity
        nlinarith [mul_nonneg hA hp, mul_nonneg (inv_nonneg.mpr hc.le) hp, mul_nonneg hCT0 hp, inv_nonneg.mpr hc.le]

end HRS.Commutator.Stj
