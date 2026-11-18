import HRS.Commutator.Whole.ApproxAux2

/-!
# Density approximation (packet CMX-APPROX, helpers, part 3)

Helpers carry the prefix `cmxSA_`.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform ContDiff

namespace HRS.Commutator.Whole

open HRS HRS.Whole

variable {d : ℕ} {s : ℝ}

/-- `{|x| ≤ m, |ρ x| ≤ m}`. -/
def cmxSA_S (ρ : Euc d → ℝ) (m : ℕ) : Set (Euc d) := {x | ‖x‖ ≤ m ∧ |ρ x| ≤ m}

/-- `ρ̃_m = ρ 1_{|x|≤m, |ρ|≤m}`. -/
def cmxSA_trunc (ρ : Euc d → ℝ) (m : ℕ) : Euc d → ℝ := (cmxSA_S ρ m).indicator ρ

lemma cmxSA_S_meas {ρ : Euc d → ℝ} (hρ : Measurable ρ) (m : ℕ) : MeasurableSet (cmxSA_S ρ m) :=
  (measurableSet_le measurable_norm measurable_const).inter
    (measurableSet_le hρ.abs measurable_const)

lemma cmxSA_trunc_meas {ρ : Euc d → ℝ} (hρ : Measurable ρ) (m : ℕ) :
    Measurable (cmxSA_trunc ρ m) := hρ.indicator (cmxSA_S_meas hρ m)

lemma cmxSA_trunc_abs_le (ρ : Euc d → ℝ) (m : ℕ) (x : Euc d) :
    |cmxSA_trunc ρ m x| ≤ |ρ x| := by
  unfold cmxSA_trunc
  by_cases hx : x ∈ cmxSA_S ρ m
  · rw [Set.indicator_of_mem hx]
  · rw [Set.indicator_of_notMem hx]; simp

lemma cmxSA_trunc_abs_le_m (ρ : Euc d → ℝ) (m : ℕ) (x : Euc d) :
    |cmxSA_trunc ρ m x| ≤ m := by
  unfold cmxSA_trunc
  by_cases hx : x ∈ cmxSA_S ρ m
  · rw [Set.indicator_of_mem hx]; exact hx.2
  · rw [Set.indicator_of_notMem hx]; simp

lemma cmxSA_trunc_zero (ρ : Euc d → ℝ) (m : ℕ) (x : Euc d) (hx : (m : ℝ) < ‖x‖) :
    cmxSA_trunc ρ m x = 0 := by
  unfold cmxSA_trunc
  rw [Set.indicator_of_notMem]
  intro h; exact absurd h.1 (not_le.2 hx)

lemma cmxSA_trunc_eventually (ρ : Euc d → ℝ) (x : Euc d) :
    ∀ᶠ m : ℕ in atTop, cmxSA_trunc ρ m x = ρ x := by
  filter_upwards [tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop (max ‖x‖ |ρ x|))]
    with m hm
  unfold cmxSA_trunc
  rw [Set.indicator_of_mem]
  exact ⟨le_trans (le_max_left _ _) hm, le_trans (le_max_right _ _) hm⟩

lemma cmxSA_trunc_tendsto (ρ : Euc d → ℝ) (x : Euc d) :
    Tendsto (fun m : ℕ => cmxSA_trunc ρ m x) atTop (𝓝 (ρ x)) :=
  tendsto_const_nhds.congr' ((cmxSA_trunc_eventually ρ x).mono fun m hm => hm.symm)

/-- the masses `c_m` -/
def cmxSA_c (ρ : Euc d → ℝ) (m : ℕ) : ℝ := ∫ x, cmxSA_trunc ρ m x

lemma cmxSA_c_tendsto {ρ : Euc d → ℝ} (hρ : Measurable ρ) (h1 : Integrable ρ)
    (hmass : ∫ x, ρ x = 1) : Tendsto (cmxSA_c ρ) atTop (𝓝 1) := by
  rw [← hmass]
  refine tendsto_integral_of_dominated_convergence (fun x => ‖ρ x‖)
    (fun m => (cmxSA_trunc_meas hρ m).aestronglyMeasurable) h1.norm
    (fun m => Filter.Eventually.of_forall fun x => ?_)
    (Filter.Eventually.of_forall fun x => cmxSA_trunc_tendsto ρ x)
  simpa only [Real.norm_eq_abs] using cmxSA_trunc_abs_le ρ m x

/-- a fixed bounded compactly supported density of mass one -/
def cmxSA_rho0 (d : ℕ) : Euc d → ℝ :=
  (ball (0 : Euc d) 1).indicator (fun _ => (volume (ball (0 : Euc d) 1)).toReal⁻¹)

lemma cmxSA_rho0_bdd (hd : 1 ≤ d) : BddCptDensity (cmxSA_rho0 d) := by
  haveI : NeZero d := ⟨by omega⟩
  haveI : Nontrivial (Euc d) := by
    haveI : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
    infer_instance
  have hpos : 0 < (volume (ball (0 : Euc d) 1)).toReal :=
    ENNReal.toReal_pos (measure_ball_pos _ _ one_pos).ne' measure_ball_lt_top.ne
  refine ⟨measurable_const.indicator measurableSet_ball, ⟨(volume (ball (0 : Euc d) 1)).toReal⁻¹, ?_⟩,
    ?_, ?_⟩
  · intro x
    unfold cmxSA_rho0
    by_cases hx : x ∈ ball (0 : Euc d) 1
    · rw [Set.indicator_of_mem hx, abs_of_pos (inv_pos.2 hpos)]
    · rw [Set.indicator_of_notMem hx]; simp [hpos.le]
  · refine HasCompactSupport.intro (isCompact_closedBall (0 : Euc d) 1) fun x hx => ?_
    unfold cmxSA_rho0
    rw [Set.indicator_of_notMem]
    intro h; exact hx (ball_subset_closedBall h)
  · unfold cmxSA_rho0
    rw [integral_indicator measurableSet_ball, setIntegral_const]
    simp only [Measure.real, smul_eq_mul]
    exact mul_inv_cancel₀ hpos.ne'

/-- the approximating densities -/
def cmxSA_rhom (ρ : Euc d → ℝ) (d' : ℕ) (m : ℕ) : Euc d → ℝ :=
  if 1 / 2 ≤ cmxSA_c ρ m then (cmxSA_c ρ m)⁻¹ • cmxSA_trunc ρ m else cmxSA_rho0 d

lemma cmxSA_rhom_bdd {ρ : Euc d → ℝ} (hd : 1 ≤ d) (hρ : Measurable ρ) (m : ℕ) :
    BddCptDensity (cmxSA_rhom ρ d m) := by
  unfold cmxSA_rhom
  split_ifs with h
  · have hc : 0 < cmxSA_c ρ m := by linarith
    refine ⟨(cmxSA_trunc_meas hρ m).const_smul _, ⟨2 * m, fun x => ?_⟩, ?_, ?_⟩
    · simp only [Pi.smul_apply, smul_eq_mul, abs_mul, abs_inv, abs_of_pos hc]
      have h2 : (cmxSA_c ρ m)⁻¹ ≤ 2 := by
        rw [inv_le_comm₀ hc (by norm_num)]; linarith
      have := cmxSA_trunc_abs_le_m ρ m x
      exact mul_le_mul h2 this (abs_nonneg _) (by norm_num)
    · refine HasCompactSupport.intro (isCompact_closedBall (0 : Euc d) m) fun x hx => ?_
      have : (m : ℝ) < ‖x‖ := by simpa using hx
      simp [cmxSA_trunc_zero ρ m x this]
    · simp only [Pi.smul_apply, smul_eq_mul]
      rw [integral_const_mul]
      have : ∫ x, cmxSA_trunc ρ m x = cmxSA_c ρ m := rfl
      rw [this, inv_mul_cancel₀ hc.ne']
  · exact cmxSA_rho0_bdd hd

lemma cmxSA_c_eventually {ρ : Euc d → ℝ} (hρ : Measurable ρ) (h1 : Integrable ρ)
    (hmass : ∫ x, ρ x = 1) : ∀ᶠ m : ℕ in atTop, 1 / 2 ≤ cmxSA_c ρ m := by
  have := (cmxSA_c_tendsto hρ h1 hmass).eventually (lt_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1))
  exact this.mono fun m hm => hm.le

lemma cmxSA_rhom_tendsto {ρ : Euc d → ℝ} (hρ : Measurable ρ) (h1 : Integrable ρ)
    (hmass : ∫ x, ρ x = 1) (x : Euc d) :
    Tendsto (fun m : ℕ => cmxSA_rhom ρ d m x) atTop (𝓝 (ρ x)) := by
  have hc := cmxSA_c_tendsto hρ h1 hmass
  have := (hc.inv₀ one_ne_zero).mul (cmxSA_trunc_tendsto ρ x)
  simp only [inv_one, one_mul] at this
  refine this.congr' ?_
  filter_upwards [cmxSA_c_eventually hρ h1 hmass] with m hm
  unfold cmxSA_rhom
  rw [if_pos hm]; rfl

lemma cmxSA_rhom_dom {ρ : Euc d → ℝ} (hρ : Measurable ρ) (h1 : Integrable ρ)
    (hmass : ∫ x, ρ x = 1) : ∀ᶠ m : ℕ in atTop, ∀ x, |cmxSA_rhom ρ d m x| ≤ 2 * |ρ x| := by
  filter_upwards [cmxSA_c_eventually hρ h1 hmass] with m hm x
  have hc : 0 < cmxSA_c ρ m := by linarith
  unfold cmxSA_rhom
  rw [if_pos hm]
  simp only [Pi.smul_apply, smul_eq_mul, abs_mul, abs_inv, abs_of_pos hc]
  have h2 : (cmxSA_c ρ m)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ hc (by norm_num)]; linarith
  calc (cmxSA_c ρ m)⁻¹ * |cmxSA_trunc ρ m x| ≤ 2 * |ρ x| :=
        mul_le_mul h2 (cmxSA_trunc_abs_le ρ m x) (abs_nonneg _) (by norm_num)

lemma cmxSA_eLpNorm_trunc_tendsto {ρ : Euc d → ℝ} (hρ : Measurable ρ) (p : ℝ≥0∞) :
    Tendsto (fun m : ℕ => eLpNorm (cmxSA_trunc ρ m) p volume) atTop (𝓝 (eLpNorm ρ p volume)) := by
  refine tendsto_of_le_liminf_of_limsup_le ?_ ?_
  · exact Lp.eLpNorm_lim_le_liminf_eLpNorm (fun m => (cmxSA_trunc_meas hρ m).aestronglyMeasurable)
      ρ hρ.aestronglyMeasurable (Filter.Eventually.of_forall fun x => cmxSA_trunc_tendsto ρ x)
  · refine limsup_le_of_le (by isBoundedDefault) (Filter.Eventually.of_forall fun m => ?_)
    refine eLpNorm_mono (cmxSA_trunc_meas hρ m).aestronglyMeasurable fun x => ?_
    simpa only [Real.norm_eq_abs] using cmxSA_trunc_abs_le ρ m x

lemma cmxSA_normE_rhom_tendsto {ρ : Euc d → ℝ} (hρ : Measurable ρ) (h1 : Integrable ρ)
    (hmass : ∫ x, ρ x = 1) (p : ℝ≥0∞) (hp : MemLp ρ p volume) :
    Tendsto (fun m : ℕ => normE p (cmxSA_rhom ρ d m)) atTop (𝓝 (normE p ρ)) := by
  have hc := cmxSA_c_tendsto hρ h1 hmass
  have hE := cmxSA_eLpNorm_trunc_tendsto hρ p
  have hcinv : Tendsto (fun m => ENNReal.ofReal ((cmxSA_c ρ m)⁻¹)) atTop (𝓝 1) := by
    have := ENNReal.tendsto_ofReal (hc.inv₀ one_ne_zero)
    simpa using this
  have hmul := ENNReal.Tendsto.mul hcinv (Or.inl one_ne_zero) hE (Or.inr ENNReal.one_ne_top)
  rw [one_mul] at hmul
  have hmul' : Tendsto (fun m : ℕ => eLpNorm (cmxSA_rhom ρ d m) p volume) atTop
      (𝓝 (eLpNorm ρ p volume)) := by
    refine hmul.congr' ?_
    filter_upwards [cmxSA_c_eventually hρ h1 hmass] with m hm
    have hc0 : 0 < cmxSA_c ρ m := by linarith
    unfold cmxSA_rhom
    rw [if_pos hm, eLpNorm_const_smul, Real.enorm_eq_ofReal (inv_pos.2 hc0).le]
  exact (ENNReal.tendsto_toReal hp.eLpNorm_lt_top.ne).comp hmul'

theorem cmxSA_density_approx (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) (p : ℝ≥0∞)
    (hp : ENNReal.ofReal ((d : ℝ) / (d - s)) < p) (ρ : Euc d → ℝ) (h1 : Integrable ρ)
    (hpρ : MemLp ρ p volume) (hmass : ∫ x, ρ x = 1) (hlog : s = 0 → LogIntegrable ρ) :
    ∃ ρm : ℕ → Euc d → ℝ, (∀ m, BddCptDensity (ρm m)) ∧
      Tendsto (fun m => normE p (ρm m)) atTop (𝓝 (normE p ρ)) ∧
      ∀ (N : ℕ) (X : Fin N → Euc d) (v : Euc d → Euc d) (L : ℝ≥0), LipschitzWith L v →
        Tendsto (fun m => modEnergy s X (ρm m)) atTop (𝓝 (modEnergy s X ρ)) ∧
        Tendsto (fun m => commA s X (ρm m) v) atTop (𝓝 (commA s X ρ v)) := by
  set ρ' : Euc d → ℝ := hpρ.aestronglyMeasurable.mk ρ with hρ'
  have hae : ρ =ᵐ[volume] ρ' := hpρ.aestronglyMeasurable.ae_eq_mk
  have hmeas : Measurable ρ' := hpρ.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have h1' : Integrable ρ' := h1.congr hae
  have hp' : MemLp ρ' p volume := hpρ.ae_eq hae
  have hmass' : ∫ x, ρ' x = 1 := by rw [← integral_congr_ae hae, hmass]
  have hW : Integrable (fun x => cmxSA_W s x * ρ' x) := by
    by_cases hs : s = 0
    · subst hs
      exact cmxSA_logMoment ρ' hmeas h1' (cmxSA_logIntegrable_congr hae (hlog rfl))
    · simp only [cmxSA_W, hs, if_false, zero_mul]
      exact integrable_zero _ _ _
  refine ⟨cmxSA_rhom ρ' d, fun m => cmxSA_rhom_bdd (by omega) hmeas m, ?_, ?_⟩
  · have := cmxSA_normE_rhom_tendsto hmeas h1' hmass' p hp'
    have e : normE p ρ' = normE p ρ := by
      unfold normE; rw [eLpNorm_congr_ae hae.symm]
    rwa [e] at this
  · intro N X v L hv
    have hE := cmxSA_energy_all_meas hd hs0 hsd p hp ρ' hmeas h1' hp' hW
    have hC := cmxSA_comm_integrable_meas hd hs0 hsd p hp ρ' hmeas h1' hp' hv X
    have hpt := cmxSA_rhom_tendsto hmeas h1' hmass'
    have hdom := cmxSA_rhom_dom hmeas h1' hmass'
    have hrm : ∀ m, Measurable (cmxSA_rhom ρ' d m) := fun m =>
      (cmxSA_rhom_bdd (by omega) hmeas m).measurable
    constructor
    · have := cmxSA_pairGen_tendsto (fun x y => kern s (x - y))
        ((cmxSA_kern_measurable s).comp (measurable_fst.sub measurable_snd)) X ρ'
        (fun i => hE.1 (X i)) hE.2 _ hrm hpt hdom
      have h2 : pairGen (fun x y => kern s (x - y)) X ρ' =
          pairGen (fun x y => kern s (x - y)) X ρ := cmxSA_pairGen_congr _ X hae.symm
      rw [h2] at this
      exact this.const_mul (1 / 2)
    · have := cmxSA_pairGen_tendsto (commKer (kernGrad s) v)
        (cmxSA_commKer_measurable s hv.continuous.measurable) X ρ' hC.1 hC.2 _ hrm hpt hdom
      have h2 : pairGen (commKer (kernGrad s) v) X ρ' =
          pairGen (commKer (kernGrad s) v) X ρ := cmxSA_pairGen_congr _ X hae.symm
      rw [h2] at this
      exact this

end HRS.Commutator.Whole
