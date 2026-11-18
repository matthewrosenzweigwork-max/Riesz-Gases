import HRS.MS.S21G2_S15aR

/-!
# S21G2 S15a -- exponential tilt of a weakly convergent family with uniformly integrable weights (R26-T3.S15a)

CONTRACT DEFECT (minimal repair applied).  The skeleton conclusion `TendstoInDistribution Y atTop Y' (fun N => tilt (P N) (V N))
(tilt P' V')` needs instances `IsProbabilityMeasure (tilt ..)` that cannot be synthesised in a statement (the tilt is a probability
measure only because of the hypotheses).  Repair, no hypothesis weakened: `r26t3_tilt_isProb` produces the instances; the
conclusion is stated (a) without instances as the bounded-continuous-test convergence (`r26t3_tilt_limit`), together with the
first two conjuncts of the skeleton, and (b) as the literal `TendstoInDistribution` with the two instances as binders
(`r26t3_tilt_limit_inDist`).  Helper names carry the prefix `s21g2_s15a_`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators BoundedContinuousFunction

namespace HRS.MS.R26T3

def r26t3_tilt {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (V : Ω → ℝ) : Measure Ω :=
  (ENNReal.ofReal (∫ ω, Real.exp (-V ω) ∂P))⁻¹ •
    P.withDensity (fun ω => ENNReal.ofReal (Real.exp (-V ω)))

section Tilt

variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] {V : Ω → ℝ}

theorem s21g2_s15a_Z_pos (hV : AEMeasurable V P) (hi : Integrable (fun ω => Real.exp (-V ω)) P) :
    0 < ∫ ω, Real.exp (-V ω) ∂P := integral_exp_pos hi

theorem r26t3_tilt_integral (hV : AEMeasurable V P) (hi : Integrable (fun ω => Real.exp (-V ω)) P)
    (g : Ω → ℝ) : ∫ ω, g ω ∂(r26t3_tilt P V) =
      (∫ ω, Real.exp (-V ω) ∂P)⁻¹ * ∫ ω, g ω * Real.exp (-V ω) ∂P := by
  have hZ := s21g2_s15a_Z_pos P hV hi
  unfold r26t3_tilt
  rw [integral_smul_measure, integral_withDensity_eq_integral_toReal_smul₀
    (by fun_prop : AEMeasurable (fun ω => ENNReal.ofReal (Real.exp (-V ω))) P)
    (ae_of_all _ fun ω => ENNReal.ofReal_lt_top)]
  rw [ENNReal.toReal_inv, ENNReal.toReal_ofReal hZ.le]
  simp only [smul_eq_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le]
  congr 1
  exact integral_congr_ae (ae_of_all _ fun ω => mul_comm _ _)

theorem r26t3_tilt_isProb (hV : AEMeasurable V P) (hi : Integrable (fun ω => Real.exp (-V ω)) P) :
    IsProbabilityMeasure (r26t3_tilt P V) := by
  have hZ := s21g2_s15a_Z_pos P hV hi
  refine ⟨?_⟩
  unfold r26t3_tilt
  rw [Measure.smul_apply, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun ω => (Real.exp_pos _).le)]
  exact ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.2 hZ).ne' ENNReal.ofReal_ne_top

end Tilt


section Lim

theorem s21g2_s15a_int1 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {V : Ω → ℝ} (hV : AEMeasurable V P) {r : ℝ} (hr : 1 ≤ r)
    (hi : Integrable (fun ω => Real.exp (-r * V ω)) P) :
    Integrable (fun ω => Real.exp (-V ω)) P :=
  (hi.add (integrable_const (1 : ℝ))).mono'
    (Real.measurable_exp.comp_aemeasurable hV.neg).aestronglyMeasurable
    (ae_of_all _ fun ω => by
      rw [Real.norm_of_nonneg (Real.exp_pos _).le]
      have := s21g2_s15a_exp_le hr (V ω)
      simp only [Pi.add_apply]; linarith)

theorem s21g2_s15a_psi_int {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {V : Ω → ℝ} (hV : AEMeasurable V P) {L : ℝ} (hL : 0 ≤ L) :
    Integrable (fun ω => s21g2_s15a_psi L (V ω)) P :=
  (integrable_const L).mono'
    ((s21g2_s15a_psi_cont L).measurable.comp_aemeasurable hV).aestronglyMeasurable
    (ae_of_all _ fun ω => by
      rw [Real.norm_of_nonneg (s21g2_s15a_psi_nonneg hL _)]; exact s21g2_s15a_psi_le_L _ _)

theorem s21g2_s15a_psi_int_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {V : Ω → ℝ} (hV : AEMeasurable V P) {L r C : ℝ} (hL : 0 ≤ L) (hr : 1 ≤ r)
    (hi : Integrable (fun ω => Real.exp (-r * V ω)) P) (hb : ∫ ω, Real.exp (-r * V ω) ∂P ≤ C) :
    ∫ ω, s21g2_s15a_psi L (V ω) ∂P ≤ 1 + C := by
  have h1 : ∫ ω, s21g2_s15a_psi L (V ω) ∂P ≤ ∫ ω, (1 + Real.exp (-r * V ω)) ∂P :=
    integral_mono (s21g2_s15a_psi_int hV hL) ((integrable_const 1).add hi) fun ω =>
      (s21g2_s15a_psi_le _ _).trans (s21g2_s15a_exp_le hr _)
  rw [integral_add (integrable_const 1) hi] at h1
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at h1
  linarith

theorem s21g2_s15a_diff_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : Type*} [NormedAddCommGroup B] [MeasurableSpace B] [BorelSpace B]
    {Y : Ω → B} {V : Ω → ℝ} (hY : AEMeasurable Y P) (hV : AEMeasurable V P)
    (hE : Integrable (fun ω => Real.exp (-V ω)) P) {g : B → ℝ} (hg : Continuous g) {c L : ℝ}
    (hc : ∀ y, ‖g y‖ ≤ c) (hL : 0 ≤ L) :
    |(∫ ω, g (Y ω) * Real.exp (-V ω) ∂P) - ∫ ω, g (Y ω) * s21g2_s15a_psi L (V ω) ∂P| ≤
      c * ∫ ω, (Real.exp (-V ω) - s21g2_s15a_psi L (V ω)) ∂P := by
  have hgY : AEStronglyMeasurable (fun ω => g (Y ω)) P :=
    (hg.measurable.comp_aemeasurable hY).aestronglyMeasurable
  have i1 : Integrable (fun ω => g (Y ω) * Real.exp (-V ω)) P :=
    hE.bdd_mul hgY (ae_of_all _ fun ω => hc _)
  have i2 : Integrable (fun ω => g (Y ω) * s21g2_s15a_psi L (V ω)) P :=
    (s21g2_s15a_psi_int hV hL).bdd_mul hgY (ae_of_all _ fun ω => hc _)
  have i3 : Integrable (fun ω => Real.exp (-V ω) - s21g2_s15a_psi L (V ω)) P :=
    hE.sub (s21g2_s15a_psi_int hV hL)
  rw [← integral_sub i1 i2, ← integral_const_mul]
  refine (abs_integral_le_integral_abs).trans (integral_mono (i1.sub i2).abs (i3.const_mul c) fun ω => ?_)
  have h0 : 0 ≤ Real.exp (-V ω) - s21g2_s15a_psi L (V ω) := sub_nonneg.2 (s21g2_s15a_psi_le _ _)
  have : g (Y ω) * Real.exp (-V ω) - g (Y ω) * s21g2_s15a_psi L (V ω) =
      g (Y ω) * (Real.exp (-V ω) - s21g2_s15a_psi L (V ω)) := by ring
  simp only [this, abs_mul, abs_of_nonneg h0]
  exact mul_le_mul_of_nonneg_right (by simpa using hc (Y ω)) h0

theorem s21g2_s15a_tail_int {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {V : Ω → ℝ} (hV : AEMeasurable V P) (hE : Integrable (fun ω => Real.exp (-V ω)) P) {L r : ℝ}
    (hL : 0 < L) (hr : 1 < r) (hi : Integrable (fun ω => Real.exp (-r * V ω)) P) :
    ∫ ω, (Real.exp (-V ω) - s21g2_s15a_psi L (V ω)) ∂P ≤ L ^ (1 - r) * ∫ ω, Real.exp (-r * V ω) ∂P := by
  rw [← integral_const_mul]
  exact integral_mono (hE.sub (s21g2_s15a_psi_int hV hL.le)) (hi.const_mul _)
    fun ω => s21g2_s15a_tail hL hr _

variable {B : Type*} [NormedAddCommGroup B] [MeasurableSpace B] [BorelSpace B]
  [SecondCountableTopology B] [CompleteSpace B]
  {Ω : ℕ → Type} [∀ N, MeasurableSpace (Ω N)]
  {P : ∀ N, Measure (Ω N)} [∀ N, IsProbabilityMeasure (P N)]
  {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
  {Y : ∀ N, Ω N → B} {V : ∀ N, Ω N → ℝ} {Y' : Ω' → B} {V' : Ω' → ℝ}

theorem s21g2_s15a_weak
    (hmeas : (∀ N, AEMeasurable (fun ω => (Y N ω, V N ω)) (P N)) ∧
      AEMeasurable (fun ω => (Y' ω, V' ω)) P')
    (hlim : TendstoInDistribution (fun N ω => (Y N ω, V N ω)) atTop (fun ω => (Y' ω, V' ω)) P P')
    {φ : B × ℝ → ℝ} (hφ : Continuous φ) {c : ℝ} (hc : ∀ p, ‖φ p‖ ≤ c) :
    Tendsto (fun N => ∫ ω, φ (Y N ω, V N ω) ∂P N) atTop (𝓝 (∫ ω, φ (Y' ω, V' ω) ∂P')) := by
  have := (tendstoInDistribution_iff_forall_integral_rclike_tendsto ℝ hmeas.1 hmeas.2).1 hlim
    (BoundedContinuousFunction.ofNormedAddCommGroup φ hφ c hc)
  simpa using this

variable (hmeas : (∀ N, AEMeasurable (fun ω => (Y N ω, V N ω)) (P N)) ∧
      AEMeasurable (fun ω => (Y' ω, V' ω)) P')
  (hlim : TendstoInDistribution (fun N ω => (Y N ω, V N ω)) atTop (fun ω => (Y' ω, V' ω)) P P')
  {r C : ℝ} (hr : 1 < r)
  (hb : ∀ N, ∫ ω, Real.exp (-r * V N ω) ∂P N ≤ C)
  (hi : ∀ N, Integrable (fun ω => Real.exp (-r * V N ω)) (P N))

include hmeas hlim hr hb hi

theorem s21g2_s15a_int_lim : Integrable (fun ω => Real.exp (-V' ω)) P' := by
  have hV' : AEMeasurable V' P' := hmeas.2.snd
  have hle : ∀ n : ℕ, ∫ ω, s21g2_s15a_psi ((n : ℝ) + 1) (V' ω) ∂P' ≤ 1 + C := fun n => by
    refine le_of_tendsto' (s21g2_s15a_weak hmeas hlim
      (φ := fun p => s21g2_s15a_psi ((n : ℝ) + 1) p.2) (c := (n : ℝ) + 1)
      ((s21g2_s15a_psi_cont _).comp continuous_snd) fun p => ?_) fun N => ?_
    · rw [Real.norm_of_nonneg (s21g2_s15a_psi_nonneg (by positivity) _)]
      exact s21g2_s15a_psi_le_L _ _
    · exact s21g2_s15a_psi_int_le (hmeas.1 N).snd (by positivity) hr.le (hi N) (hb N)
  have hmeasF : ∀ n : ℕ, AEMeasurable
      (fun ω => ENNReal.ofReal (s21g2_s15a_psi ((n : ℝ) + 1) (V' ω))) P' := fun n =>
    ((s21g2_s15a_psi_cont _).measurable.comp_aemeasurable hV').ennreal_ofReal
  have hT := lintegral_tendsto_of_tendsto_of_monotone
    (F := fun ω => ENNReal.ofReal (Real.exp (-V' ω))) hmeasF
    (ae_of_all _ fun ω n m hnm => ENNReal.ofReal_le_ofReal (le_min (min_le_left _ _)
      ((min_le_right _ _).trans (by simpa using hnm))))
    (ae_of_all _ fun ω => by
      refine ENNReal.tendsto_ofReal ?_
      refine tendsto_const_nhds.congr' ?_
      obtain ⟨n0, hn0⟩ := exists_nat_ge (Real.exp (-V' ω))
      filter_upwards [eventually_ge_atTop n0] with n hn
      unfold s21g2_s15a_psi
      rw [min_eq_left (hn0.trans ((Nat.cast_le.2 hn).trans (by linarith)))])
  have hfin : ∫⁻ ω, ENNReal.ofReal (Real.exp (-V' ω)) ∂P' ≤ ENNReal.ofReal (1 + C) :=
    le_of_tendsto' hT fun n => by
      rw [← ofReal_integral_eq_lintegral_ofReal (s21g2_s15a_psi_int hV' (by positivity))
        (ae_of_all _ fun ω => s21g2_s15a_psi_nonneg (by positivity) _)]
      exact ENNReal.ofReal_le_ofReal (hle n)
  refine ⟨(Real.measurable_exp.comp_aemeasurable hV'.neg).aestronglyMeasurable, ?_⟩
  simp only [HasFiniteIntegral, Real.enorm_eq_ofReal (Real.exp_pos _).le]
  exact lt_of_le_of_lt hfin ENNReal.ofReal_lt_top

theorem s21g2_s15a_tail_lim :
    Tendsto (fun n : ℕ => ∫ ω, (Real.exp (-V' ω) - s21g2_s15a_psi ((n : ℝ) + 1) (V' ω)) ∂P')
      atTop (𝓝 0) := by
  have hV' : AEMeasurable V' P' := hmeas.2.snd
  have hE := s21g2_s15a_int_lim hmeas hlim hr hb hi
  have := tendsto_integral_of_dominated_convergence (μ := P')
    (F := fun (n : ℕ) ω => Real.exp (-V' ω) - s21g2_s15a_psi ((n : ℝ) + 1) (V' ω))
    (f := fun _ => (0 : ℝ)) (fun ω => Real.exp (-V' ω))
    (fun n => (hE.sub (s21g2_s15a_psi_int hV' (by positivity))).aestronglyMeasurable) hE
    (fun n => ae_of_all _ fun ω => by
      have h0 : 0 ≤ Real.exp (-V' ω) - s21g2_s15a_psi ((n : ℝ) + 1) (V' ω) :=
        sub_nonneg.2 (s21g2_s15a_psi_le _ _)
      rw [Real.norm_of_nonneg h0]
      linarith [s21g2_s15a_psi_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ) + 1) (V' ω)])
    (ae_of_all _ fun ω => by
      obtain ⟨n0, hn0⟩ := exists_nat_ge (Real.exp (-V' ω))
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop n0] with n hn
      unfold s21g2_s15a_psi
      rw [min_eq_left (hn0.trans ((Nat.cast_le.2 hn).trans (by linarith))), sub_self])
  simpa using this

theorem s21g2_s15a_conv {g : B → ℝ} (hg : Continuous g) {c : ℝ} (hc : ∀ y, ‖g y‖ ≤ c) :
    Tendsto (fun N => ∫ ω, g (Y N ω) * Real.exp (-V N ω) ∂P N) atTop
      (𝓝 (∫ ω, g (Y' ω) * Real.exp (-V' ω) ∂P')) := by
  have hV' : AEMeasurable V' P' := hmeas.2.snd
  have hE := s21g2_s15a_int_lim hmeas hlim hr hb hi
  have hC : 0 ≤ C := (integral_nonneg fun ω => (Real.exp_pos _).le).trans (hb 0)
  have hc0 : 0 ≤ c := (norm_nonneg (g 0)).trans (hc 0)
  have hlin : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  have hp : Tendsto (fun n : ℕ => ((n : ℝ) + 1) ^ (1 - r)) atTop (𝓝 0) := by
    have := (tendsto_rpow_neg_atTop (show 0 < r - 1 by linarith)).comp hlin
    simpa [Function.comp_def, neg_sub] using this
  have τ0 : ∀ n : ℕ, 0 ≤ ∫ ω, (Real.exp (-V' ω) - s21g2_s15a_psi ((n : ℝ) + 1) (V' ω)) ∂P' :=
    fun n => integral_nonneg fun ω => sub_nonneg.2 (s21g2_s15a_psi_le _ _)
  refine s21g2_s15a_approx
    (b := fun n N => ∫ ω, g (Y N ω) * s21g2_s15a_psi ((n : ℝ) + 1) (V N ω) ∂P N)
    (b' := fun n => ∫ ω, g (Y' ω) * s21g2_s15a_psi ((n : ℝ) + 1) (V' ω) ∂P')
    (δ := fun n => c * (((n : ℝ) + 1) ^ (1 - r) * C +
      ∫ ω, (Real.exp (-V' ω) - s21g2_s15a_psi ((n : ℝ) + 1) (V' ω)) ∂P')) ?_ ?_ ?_ ?_
  · have := ((hp.mul_const C).add (s21g2_s15a_tail_lim hmeas hlim hr hb hi)).const_mul c
    simpa using this
  · intro n
    refine s21g2_s15a_weak hmeas hlim
      (φ := fun p => g p.1 * s21g2_s15a_psi ((n : ℝ) + 1) p.2) (c := c * ((n : ℝ) + 1))
      ((hg.comp continuous_fst).mul ((s21g2_s15a_psi_cont _).comp continuous_snd)) fun p => ?_
    have h0 := s21g2_s15a_psi_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ) + 1) p.2
    rw [norm_mul, Real.norm_of_nonneg h0]
    exact mul_le_mul (hc _) (s21g2_s15a_psi_le_L _ _) h0 hc0
  · intro n N
    have hVN := (hmeas.1 N).snd
    have hEN := s21g2_s15a_int1 hVN hr.le (hi N)
    refine (s21g2_s15a_diff_le (hmeas.1 N).fst hVN hEN hg hc (by positivity)).trans ?_
    have t1 := s21g2_s15a_tail_int hVN hEN (L := (n : ℝ) + 1) (by positivity) hr (hi N)
    have t2 : ∫ ω, (Real.exp (-V N ω) - s21g2_s15a_psi ((n : ℝ) + 1) (V N ω)) ∂P N ≤
        ((n : ℝ) + 1) ^ (1 - r) * C :=
      t1.trans (mul_le_mul_of_nonneg_left (hb N) (by positivity))
    exact mul_le_mul_of_nonneg_left (by linarith [τ0 n]) hc0
  · intro n
    have hEl := s21g2_s15a_int_lim hmeas hlim hr hb hi
    refine (s21g2_s15a_diff_le hmeas.2.fst hV' hEl hg hc (by positivity)).trans ?_
    exact mul_le_mul_of_nonneg_left (by nlinarith [τ0 n, (by positivity : (0 : ℝ) ≤ ((n : ℝ) + 1) ^ (1 - r))]) hc0

end Lim

theorem r26t3_tilt_limit {B : Type*} [NormedAddCommGroup B] [MeasurableSpace B]
    [BorelSpace B] [SecondCountableTopology B] [CompleteSpace B]
    {Ω : ℕ → Type} [∀ N, MeasurableSpace (Ω N)]
    (P : ∀ N, Measure (Ω N)) [∀ N, IsProbabilityMeasure (P N)]
    {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (Y : ∀ N, Ω N → B) (V : ∀ N, Ω N → ℝ) (Y' : Ω' → B) (V' : Ω' → ℝ)
    (hmeas : (∀ N, AEMeasurable (fun ω => (Y N ω,V N ω)) (P N)) ∧ AEMeasurable (fun ω => (Y' ω,V' ω)) P')
    (hlim : TendstoInDistribution (fun N ω => (Y N ω,V N ω)) atTop (fun ω => (Y' ω,V' ω)) P P')
    (r C : ℝ) (hr : 1<r)
    (hb : ∀ N, ∫ ω, Real.exp (-r*V N ω) ∂P N ≤ C)
    (hi : ∀ N, Integrable (fun ω => Real.exp (-r*V N ω)) (P N)) :
    Integrable (fun ω => Real.exp (-V' ω)) P' ∧
      0<∫ ω, Real.exp (-V' ω) ∂P' ∧
      (∀ N, IsProbabilityMeasure (r26t3_tilt (P N) (V N))) ∧
      IsProbabilityMeasure (r26t3_tilt P' V') ∧
      ∀ g : B →ᵇ ℝ, Tendsto (fun N => ∫ ω, g (Y N ω) ∂(r26t3_tilt (P N) (V N))) atTop
        (𝓝 (∫ ω, g (Y' ω) ∂(r26t3_tilt P' V'))) := by
  have hE := s21g2_s15a_int_lim hmeas hlim hr hb hi
  have hV' : AEMeasurable V' P' := hmeas.2.snd
  have hEN : ∀ N, Integrable (fun ω => Real.exp (-V N ω)) (P N) := fun N =>
    s21g2_s15a_int1 (hmeas.1 N).snd hr.le (hi N)
  have hZ' := s21g2_s15a_Z_pos P' hV' hE
  refine ⟨hE, hZ', fun N => r26t3_tilt_isProb (P N) (hmeas.1 N).snd (hEN N),
    r26t3_tilt_isProb P' hV' hE, fun g => ?_⟩
  have hZ := s21g2_s15a_conv hmeas hlim hr hb hi (g := fun _ => (1 : ℝ)) continuous_const
    (c := 1) (fun _ => by simp)
  simp only [one_mul] at hZ
  have hg := s21g2_s15a_conv hmeas hlim hr hb hi (g := g) g.continuous (c := ‖g‖)
    (fun y => g.norm_coe_le_norm y)
  simp only [r26t3_tilt_integral _ (hmeas.1 _).snd (hEN _), r26t3_tilt_integral P' hV' hE]
  exact (hZ.inv₀ hZ'.ne').mul hg

theorem r26t3_tilt_limit_inDist {B : Type*} [NormedAddCommGroup B] [MeasurableSpace B]
    [BorelSpace B] [SecondCountableTopology B] [CompleteSpace B]
    {Ω : ℕ → Type} [∀ N, MeasurableSpace (Ω N)]
    (P : ∀ N, Measure (Ω N)) [∀ N, IsProbabilityMeasure (P N)]
    {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (Y : ∀ N, Ω N → B) (V : ∀ N, Ω N → ℝ) (Y' : Ω' → B) (V' : Ω' → ℝ)
    (hmeas : (∀ N, AEMeasurable (fun ω => (Y N ω,V N ω)) (P N)) ∧ AEMeasurable (fun ω => (Y' ω,V' ω)) P')
    (hlim : TendstoInDistribution (fun N ω => (Y N ω,V N ω)) atTop (fun ω => (Y' ω,V' ω)) P P')
    (r C : ℝ) (hr : 1<r)
    (hb : ∀ N, ∫ ω, Real.exp (-r*V N ω) ∂P N ≤ C)
    (hi : ∀ N, Integrable (fun ω => Real.exp (-r*V N ω)) (P N))
    [∀ N, IsProbabilityMeasure (r26t3_tilt (P N) (V N))] [IsProbabilityMeasure (r26t3_tilt P' V')] :
    TendstoInDistribution Y atTop Y' (fun N => r26t3_tilt (P N) (V N)) (r26t3_tilt P' V') := by
  obtain ⟨hE, hZ', -, -, hg⟩ := r26t3_tilt_limit P P' Y V Y' V' hmeas hlim r C hr hb hi
  have hac : ∀ {Ω : Type} [MeasurableSpace Ω] (Q : Measure Ω) (W : Ω → ℝ),
      r26t3_tilt Q W ≪ Q := fun Q W => by
    unfold r26t3_tilt
    intro s hs
    simp [withDensity_absolutelyContinuous Q _ hs]
  refine (tendstoInDistribution_iff_forall_integral_rclike_tendsto ℝ
    (fun N => (hmeas.1 N).fst.mono_ac (hac _ _)) (hmeas.2.fst.mono_ac (hac _ _))).2 hg

end HRS.MS.R26T3
