import HRS.MC.E213Defs

/-!
# Packet e213u1 (part b): the window drift bounds `winDrift_near/far/cont/add`

Relocations (`_proof`) of `winDrift_near`, `winDrift_far`, `winDrift_cont`, `winDrift_add` of `HRS.MC.E213Plan`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MC.E213U1

open HRS HRS.Sec7 HRS.Main HRS.Uniform HRS.MC.E213O HRS.MC.E213T HRS.MC.E213Plan

variable {d : ℕ}

/-- The window restriction of a path built by `pathOf` is bounded by any pointwise bound on the window times. -/
theorem u1_winRestr_pathOf_norm_le {m T : ℝ} (a : ℝ) (ha : 0 ≤ a) (g : ℝ → NegSobolev d m) {K : ℝ} (hK : 0 ≤ K)
    (h : ∀ s ∈ Set.Icc (0 : ℝ) T, ‖g (a + s)‖ ≤ K) :
    ‖winRestr a ha (Sec7.pathOf m (a + T) g)‖ ≤ K := by
  classical
  by_cases hc : Continuous fun t : Set.Icc (0 : ℝ) (a + T) => g t
  · have hw : Sec7.pathOf m (a + T) g = (⟨fun t => g t, hc⟩ : C(Set.Icc (0 : ℝ) (a + T), NegSobolev d m)) := by
      unfold Sec7.pathOf
      exact dif_pos hc
    rw [hw]
    refine (ContinuousMap.norm_le _ hK).2 (fun s => ?_)
    have := h s.1 s.2
    exact this
  · have hw : Sec7.pathOf m (a + T) g = 0 := by
      unfold Sec7.pathOf
      exact dif_neg hc
    rw [hw, map_zero, norm_zero]
    exact hK

/-- A pointwise bound on the integrand of the window drift gives a bound by the integral of the weight. -/
theorem u1_winDrift_norm_le {S : PreparedData d} {β₀ m : ℝ} (hE : EdgeworthHyp S β₀ m) (T : ℝ) (a : ℝ) (ha : 0 ≤ a)
    (b : ℝ → NegSobolev d m) (u u' : ℝ) (g : ℝ → ℝ) (hg0 : ∀ v, 0 ≤ g v)
    (hgi : IntegrableOn g (Set.Ioc u u'))
    (hb : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ v ∈ Set.Ioc u (min u' (a + s)),
      ‖Vprop (regime S β₀ hE).D (regime S β₀ hE).ρ m (a + s) v (b v)‖ ≤ g v) :
    ‖winDrift (regime S β₀ hE) m T a ha b u u'‖ ≤ ∫ v in Set.Ioc u u', g v := by
  unfold winDrift driftInc
  refine u1_winRestr_pathOf_norm_le a ha _ (setIntegral_nonneg measurableSet_Ioc fun v _ => hg0 v) (fun s hs => ?_)
  have hsub : Set.Ioc u (min u' (a + s)) ⊆ Set.Ioc u u' := Set.Ioc_subset_Ioc_right (min_le_left _ _)
  calc ‖∫ v in Set.Ioc u (min u' (a + s)), Vprop (regime S β₀ hE).D (regime S β₀ hE).ρ m (a + s) v (b v)‖
      ≤ ∫ v in Set.Ioc u (min u' (a + s)), g v :=
        norm_integral_le_of_norm_le (hgi.mono_set hsub) (by
          filter_upwards [ae_restrict_mem measurableSet_Ioc] with v hv using hb s hs v hv)
    _ ≤ ∫ v in Set.Ioc u u', g v :=
        setIntegral_mono_set hgi (Filter.Eventually.of_forall hg0) (Filter.Eventually.of_forall hsub)

/-- Joint continuity of `(a, x) ↦ L a x` for a uniformly bounded, strongly continuous family of operators. -/
theorem u1_joint_continuous {α X Y : Type*} [TopologicalSpace α] [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] (L : α → X →L[ℝ] Y) (B : ℝ)
    (hL : ∀ x, Continuous fun a => L a x) (hb : ∀ a, ‖L a‖ ≤ B) :
    Continuous fun p : α × X => L p.1 p.2 := by
  rw [continuous_iff_continuousAt]
  rintro ⟨a₀, x₀⟩
  have h1 : Tendsto (fun p : α × X => L p.1 (p.2 - x₀)) (𝓝 (a₀, x₀)) (𝓝 0) := by
    have hg : Tendsto (fun p : α × X => B * ‖p.2 - x₀‖) (𝓝 (a₀, x₀)) (𝓝 0) := by
      have : Tendsto (fun p : α × X => ‖p.2 - x₀‖) (𝓝 (a₀, x₀)) (𝓝 ‖x₀ - x₀‖) :=
        (continuous_snd.sub continuous_const).norm.continuousAt.tendsto
      simpa using this.const_mul B
    exact squeeze_zero_norm (fun p => (L p.1).le_of_opNorm_le (hb p.1) _) hg
  have h2 : Tendsto (fun p : α × X => L p.1 x₀) (𝓝 (a₀, x₀)) (𝓝 (L a₀ x₀)) :=
    ((hL x₀).comp continuous_fst).continuousAt.tendsto
  have := h1.add h2
  simp only [zero_add] at this
  refine this.congr (fun p => ?_)
  simp [← map_add]

/-- The properties of the dual evolution used for the continuity of the window drift. -/
def U1Spec {S : PreparedData d} {β₀ m : ℝ} (hE : EdgeworthHyp S β₀ m) (C c : ℝ)
    (Vev : ℝ → ℝ → NegSobolev d m →L[ℝ] NegSobolev d m) : Prop :=
  (∀ u t : ℝ, 0 ≤ u → u ≤ t → ‖Vev t u‖ ≤ C * Real.exp (-c * (t - u))) ∧
  (∀ u t : ℝ, 0 ≤ u → u ≤ t → ∀ F : NegSobolev d m,
    Vprop (regime S β₀ hE).D (regime S β₀ hE).ρ m t u F = Vev t u F) ∧
  (∀ T : ℝ, 0 ≤ T → ∀ x : NegSobolev d m,
    ContinuousOn (fun p : ℝ × ℝ => Vev p.1 p.2 x) {p : ℝ × ℝ | 0 ≤ p.2 ∧ p.2 ≤ p.1 ∧ p.1 ≤ T})

/-- The strongly continuous bounded dual evolution reproducing `Vprop` (extracted from `adjk_evolution_along_trajectory`). -/
theorem u1_vev {S : PreparedData d} {β₀ m : ℝ} (hE : EdgeworthHyp S β₀ m) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∃ Vev : ℝ → ℝ → NegSobolev d m →L[ℝ] NegSobolev d m, U1Spec hE C c Vev := by
  obtain ⟨Cr, cr, hC, hc, Vev, hdual, hplain, hdec, -⟩ :=
    HRS.AdjK.adjk_evolution_along_trajectory S.hd (HRS.MC.E213A.isSmoothPositiveTrajectory_of_prepared S) m
  have hdual' : IsDualEvolution (HRS.MC.E213A.regimeOfPrepared S β₀ hE).D (HRS.MC.E213A.regimeOfPrepared S β₀ hE).ρ m
      Vev := hdual
  refine ⟨Cr, cr, hC, hc, Vev, hdec, fun u t hu hut F => ?_, fun T hT x => (hplain T hT).2.2 x⟩
  exact HRS.MC.E213D.vprop_eq_vev _ _ m Vev hdual' hu hut F

section Bounds

variable {S : PreparedData d} {β₀ m : ℝ}

theorem u1_norm_nearCoef_embed_le (hE : EdgeworthHyp S β₀ m) (b : ℝ) (bq : ℝ → NegSobolev d (rLvl d)) (v : ℝ) :
    ‖nearCoef b (fun v => NegSobolev.embed m (bq v)) v‖ ≤ Set.indicator (Set.Ici b) (fun v => ‖bq v‖) v := by
  unfold nearCoef
  by_cases h : b ≤ v
  · simp only [h, if_true, Set.indicator_of_mem (Set.mem_Ici.2 h)]
    exact NegSobolev.norm_embed_le m (rLvl_le hE) (bq v)
  · simp [h, Set.indicator_of_notMem (show v ∉ Set.Ici b from h)]

theorem u1_norm_farCoef_embed_le (hE : EdgeworthHyp S β₀ m) (b : ℝ) (bq : ℝ → NegSobolev d (rLvl d)) (v : ℝ) :
    ‖farCoef b (fun v => NegSobolev.embed m (bq v)) v‖ ≤ Set.indicator (Set.Iio b) (fun v => ‖bq v‖) v := by
  unfold farCoef
  by_cases h : v < b
  · simp only [h, if_true, Set.indicator_of_mem (Set.mem_Iio.2 h)]
    exact NegSobolev.norm_embed_le m (rLvl_le hE) (bq v)
  · simp [h, Set.indicator_of_notMem (show v ∉ Set.Iio b from h)]

theorem winDrift_near_proof (hE : EdgeworthHyp S β₀ m) (T : ℝ) (hT : 0 < T) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : ℝ) (ha : 0 ≤ a) (b : ℝ), 0 ≤ b →
      ∀ (bq : ℝ → NegSobolev d (rLvl d)), Measurable (nearCoef 0 bq) →
      IntegrableOn (fun v => ‖bq v‖) (Set.Icc b (a + T)) →
      ∀ u u' : ℝ, 0 ≤ u → u ≤ u' → u' ≤ a + T →
        ‖winDrift (regime S β₀ hE) m T a ha (nearCoef b (fun v => NegSobolev.embed m (bq v))) u u'‖ ≤
          C * ∫ v in Set.Ioc u u' ∩ Set.Ici b, ‖bq v‖ := by
  obtain ⟨C, c, hC, hc, hV⟩ := HRS.MC.E213D.vprop_stable_of_prepared S β₀ hE m
  refine ⟨C, hC, fun a ha b hb bq _ hi u u' hu huu hu' => ?_⟩
  have hint : IntegrableOn (fun v => ‖bq v‖) (Set.Ioc u u' ∩ Set.Ici b) := by
    refine hi.mono_set (fun v hv => ?_)
    exact ⟨hv.2, hv.1.2.trans hu'⟩
  have hgi : IntegrableOn (fun v => C * Set.indicator (Set.Ici b) (fun v => ‖bq v‖) v) (Set.Ioc u u') := by
    refine Integrable.const_mul ?_ C
    rw [integrable_indicator_iff measurableSet_Ici]
    simpa [IntegrableOn, Measure.restrict_restrict measurableSet_Ici, Set.inter_comm] using hint
  have key := u1_winDrift_norm_le hE T a ha (nearCoef b (fun v => NegSobolev.embed m (bq v))) u u'
    (fun v => C * Set.indicator (Set.Ici b) (fun v => ‖bq v‖) v)
    (fun v => mul_nonneg hC.le (Set.indicator_nonneg (fun _ _ => norm_nonneg _) _)) hgi (by
      intro s hs v hv
      have hv0 : 0 ≤ v := hu.trans hv.1.le
      have hvt : v ≤ a + s := hv.2.trans (min_le_right _ _)
      refine (hV v (a + s) hv0 hvt _).trans ?_
      have h1 : Real.exp (-c * (a + s - v)) ≤ 1 :=
        Real.exp_le_one_iff.2 (by nlinarith)
      calc C * Real.exp (-c * (a + s - v)) * ‖nearCoef b (fun v => NegSobolev.embed m (bq v)) v‖
          ≤ C * 1 * ‖nearCoef b (fun v => NegSobolev.embed m (bq v)) v‖ := by gcongr
        _ ≤ C * Set.indicator (Set.Ici b) (fun v => ‖bq v‖) v := by
            rw [mul_one]
            exact mul_le_mul_of_nonneg_left (u1_norm_nearCoef_embed_le hE b bq v) hC.le)
  refine key.trans (le_of_eq ?_)
  rw [integral_const_mul, setIntegral_indicator measurableSet_Ici]

theorem winDrift_far_proof (hE : EdgeworthHyp S β₀ m) (T : ℝ) (hT : 0 < T) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ (a : ℝ) (ha : 0 ≤ a) (b : ℝ), 0 ≤ b →
      ∀ (bq : ℝ → NegSobolev d (rLvl d)), Measurable (nearCoef 0 bq) →
      IntegrableOn (fun v => Real.exp (-c * (a - v)) * ‖bq v‖) (Set.Ioc 0 (min b (a + T))) →
      ∀ u u' : ℝ, 0 ≤ u → u ≤ u' → u' ≤ a + T →
        ‖winDrift (regime S β₀ hE) m T a ha (farCoef b (fun v => NegSobolev.embed m (bq v))) u u'‖ ≤
          C * ∫ v in Set.Ioc u u' ∩ Set.Iio b, Real.exp (-c * (a - v)) * ‖bq v‖ := by
  obtain ⟨C, c, hC, hc, hV⟩ := HRS.MC.E213D.vprop_stable_of_prepared S β₀ hE m
  refine ⟨C, c, hC, hc, fun a ha b hb bq _ hi u u' hu huu hu' => ?_⟩
  have hint : IntegrableOn (fun v => Real.exp (-c * (a - v)) * ‖bq v‖) (Set.Ioc u u' ∩ Set.Iio b) := by
    refine hi.mono_set (fun v hv => ?_)
    exact ⟨hu.trans_lt hv.1.1, le_min (le_of_lt hv.2) (hv.1.2.trans hu')⟩
  have hgi : IntegrableOn (fun v => C * Set.indicator (Set.Iio b)
      (fun v => Real.exp (-c * (a - v)) * ‖bq v‖) v) (Set.Ioc u u') := by
    refine Integrable.const_mul ?_ C
    rw [integrable_indicator_iff measurableSet_Iio]
    simpa [IntegrableOn, Measure.restrict_restrict measurableSet_Iio, Set.inter_comm] using hint
  have key := u1_winDrift_norm_le hE T a ha (farCoef b (fun v => NegSobolev.embed m (bq v))) u u'
    (fun v => C * Set.indicator (Set.Iio b) (fun v => Real.exp (-c * (a - v)) * ‖bq v‖) v)
    (fun v => mul_nonneg hC.le (Set.indicator_nonneg (fun _ _ => by positivity) _)) hgi (by
      intro s hs v hv
      have hv0 : 0 ≤ v := hu.trans hv.1.le
      have hvt : v ≤ a + s := hv.2.trans (min_le_right _ _)
      refine (hV v (a + s) hv0 hvt _).trans ?_
      have h1 : Real.exp (-c * (a + s - v)) ≤ Real.exp (-c * (a - v)) :=
        Real.exp_le_exp.2 (by nlinarith [hs.1])
      by_cases hvb : v < b
      · rw [Set.indicator_of_mem (Set.mem_Iio.2 hvb)]
        calc C * Real.exp (-c * (a + s - v)) * ‖farCoef b (fun v => NegSobolev.embed m (bq v)) v‖
            ≤ C * Real.exp (-c * (a - v)) * ‖bq v‖ := by
              have := NegSobolev.norm_embed_le m (rLvl_le hE) (bq v)
              have h2 : ‖farCoef b (fun v => NegSobolev.embed m (bq v)) v‖ ≤ ‖bq v‖ := by
                unfold farCoef; rw [if_pos hvb]; exact this
              gcongr
          _ = C * (Real.exp (-c * (a - v)) * ‖bq v‖) := by ring
      · have : farCoef b (fun v => NegSobolev.embed m (bq v)) v = 0 := by
          unfold farCoef; rw [if_neg hvb]
        rw [this, norm_zero, mul_zero, Set.indicator_of_notMem (show v ∉ Set.Iio b from hvb), mul_zero])
  refine key.trans (le_of_eq ?_)
  rw [integral_const_mul, setIntegral_indicator measurableSet_Iio]

/-- The clamp of `v` to `[0,t]`. -/
def u1_cl (t v : ℝ) : ℝ := max 0 (min v t)

theorem u1_cl_mem {t : ℝ} (v : ℝ) (ht : 0 ≤ t) : u1_cl t v ∈ Set.Icc (0 : ℝ) t :=
  ⟨le_max_left _ _, max_le ht (min_le_right _ _)⟩

theorem u1_cl_eq {t v : ℝ} (hv : 0 ≤ v) (hvt : v ≤ t) : u1_cl t v = v := by
  simp [u1_cl, min_eq_left hvt, max_eq_right hv]

theorem u1_cl_cont (t : ℝ) : Continuous (u1_cl t) := by
  unfold u1_cl; fun_prop

/-- Joint continuity of the clamped evolution at a fixed time `t ∈ [0,H]`. -/
theorem u1_clamp_joint {S : PreparedData d} {β₀ m : ℝ} {hE : EdgeworthHyp S β₀ m} {C c : ℝ}
    {Vev : ℝ → ℝ → NegSobolev d m →L[ℝ] NegSobolev d m} (hC : 0 < C) (hc : 0 < c) (hsp : U1Spec hE C c Vev)
    {H t : ℝ} (ht0 : 0 ≤ t) (htH : t ≤ H) :
    Continuous fun p : ℝ × NegSobolev d m => Vev t (u1_cl t p.1) p.2 := by
  obtain ⟨hbd, -, hcont⟩ := hsp
  have hH0 : 0 ≤ H := ht0.trans htH
  refine u1_joint_continuous (fun v => Vev t (u1_cl t v)) C (fun x => ?_) (fun v => ?_)
  · have h1 : ContinuousOn (fun w : ℝ => Vev t w x) (Set.Icc 0 t) := by
      refine (hcont H hH0 x).comp (continuous_const.prodMk continuous_id).continuousOn ?_
      intro w hw
      exact ⟨hw.1, hw.2, htH⟩
    exact h1.comp_continuous (u1_cl_cont t) (fun v => u1_cl_mem v ht0)
  · have hm := u1_cl_mem (t := t) v ht0
    refine (hbd _ _ hm.1 hm.2).trans ?_
    have : Real.exp (-c * (t - u1_cl t v)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [hm.2])
    calc C * Real.exp (-c * (t - u1_cl t v)) ≤ C * 1 := by gcongr
      _ = C := mul_one C

/-- The integrand of the drift integral over the fixed domain `Ioc u u'`: the indicator of `{v ≤ t}` of the clamped evolution. -/
def u1_F {m : ℝ} (Vev : ℝ → ℝ → NegSobolev d m →L[ℝ] NegSobolev d m) (f : ℝ → NegSobolev d m) (t v : ℝ) :
    NegSobolev d m :=
  Set.indicator (Set.Iic t) (fun v => Vev t (u1_cl t v) (f v)) v

theorem u1_F_add {m : ℝ} (Vev : ℝ → ℝ → NegSobolev d m →L[ℝ] NegSobolev d m) (f₁ f₂ : ℝ → NegSobolev d m)
    (t v : ℝ) : u1_F Vev (fun v => f₁ v + f₂ v) t v = u1_F Vev f₁ t v + u1_F Vev f₂ t v := by
  unfold u1_F
  by_cases h : v ≤ t
  · simp [Set.indicator_of_mem (Set.mem_Iic.2 h), map_add]
  · simp [Set.indicator_of_notMem (show v ∉ Set.Iic t from h)]

theorem u1_aesm_of_nearCoef {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] {bq : ℝ → E} (hbm : Measurable (nearCoef 0 bq)) {s : Set ℝ}
    (hs : MeasurableSet s) (hs0 : s ⊆ Set.Ici 0) :
    AEStronglyMeasurable bq (volume.restrict s) := by
  refine (hbm.aestronglyMeasurable (μ := volume.restrict s)).congr ?_
  filter_upwards [ae_restrict_mem hs] with v hv
  unfold nearCoef
  rw [if_pos (show (0 : ℝ) ≤ v from hs0 hv)]

/-- Representation and integrability of the drift integrand for `t ∈ [0,a+T]`. -/
theorem u1_Fint {S : PreparedData d} {β₀ m : ℝ} (hE : EdgeworthHyp S β₀ m) {C c : ℝ}
    {Vev : ℝ → ℝ → NegSobolev d m →L[ℝ] NegSobolev d m} (hC : 0 < C) (hc : 0 < c) (hsp : U1Spec hE C c Vev)
    (T a : ℝ) (hT : 0 < T) (ha : 0 ≤ a)
    (bq : ℝ → NegSobolev d (rLvl d)) (hbm : Measurable (nearCoef 0 bq))
    (hbi : IntegrableOn (fun v => ‖bq v‖) (Set.Icc 0 (a + T)))
    (u u' : ℝ) (hu : 0 ≤ u) (hu' : u' ≤ a + T) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) (a + T)) :
    (∫ v in Set.Ioc u (min u' t), Vprop (regime S β₀ hE).D (regime S β₀ hE).ρ m t v (NegSobolev.embed m (bq v)) =
      ∫ v in Set.Ioc u u', u1_F Vev (fun v => HRS.MD.EQInterp.embedCLM (rLvl_le hE) (bq v)) t v) ∧
    Integrable (u1_F Vev (fun v => HRS.MD.EQInterp.embedCLM (rLvl_le hE) (bq v)) t)
      (volume.restrict (Set.Ioc u u')) ∧
    ∀ᵐ v ∂(volume.restrict (Set.Ioc u u')),
      ‖u1_F Vev (fun v => HRS.MD.EQInterp.embedCLM (rLvl_le hE) (bq v)) t v‖ ≤ C * ‖bq v‖ := by
  have hsp' := hsp
  obtain ⟨hbd, heq, -⟩ := hsp
  set ι := HRS.MD.EQInterp.embedCLM (rLvl_le hE) with hι
  set μ : Measure ℝ := volume.restrict (Set.Ioc u u') with hμ
  have hsub : Set.Ioc u u' ⊆ Set.Icc 0 (a + T) := fun v hv => ⟨hu.trans hv.1.le, hv.2.trans hu'⟩
  have hbnd : ∀ᵐ v ∂μ, ‖u1_F Vev (fun v => ι (bq v)) t v‖ ≤ C * ‖bq v‖ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with v hv
    have hv0 : 0 ≤ v := hu.trans hv.1.le
    by_cases hvt : v ≤ t
    · simp only [u1_F, Set.indicator_of_mem (Set.mem_Iic.2 hvt), u1_cl_eq hv0 hvt]
      calc ‖Vev t v (ι (bq v))‖ ≤ ‖Vev t v‖ * ‖ι (bq v)‖ := (Vev t v).le_opNorm _
        _ ≤ (C * Real.exp (-c * (t - v))) * ‖bq v‖ := by
            refine mul_le_mul (hbd _ _ hv0 hvt) ?_ (norm_nonneg _) (by positivity)
            exact NegSobolev.norm_embed_le m (rLvl_le hE) (bq v)
        _ ≤ C * 1 * ‖bq v‖ := by
            have : Real.exp (-c * (t - v)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
            gcongr
        _ = C * ‖bq v‖ := by ring
    · simp only [u1_F, Set.indicator_of_notMem (show v ∉ Set.Iic t from hvt), norm_zero]
      positivity
  refine ⟨?_, ?_, ?_⟩
  · have hset : Set.Ioc u (min u' t) = Set.Ioc u u' ∩ Set.Iic t := by
      ext v; simp only [Set.mem_Ioc, le_min_iff, Set.mem_inter_iff, Set.mem_Iic]; tauto
    simp only [u1_F]
    rw [setIntegral_indicator measurableSet_Iic, ← hset]
    refine setIntegral_congr_fun measurableSet_Ioc (fun v hv => ?_)
    have hv0 : 0 ≤ v := hu.trans hv.1.le
    have hvt : v ≤ t := hv.2.trans (min_le_right _ _)
    simp only [u1_cl_eq hv0 hvt]
    exact heq v t hv0 hvt _
  · have hbm' : AEStronglyMeasurable bq μ :=
      u1_aesm_of_nearCoef hbm measurableSet_Ioc (fun v hv => Set.mem_Ici.2 (hu.trans hv.1.le))
    have hfm : AEStronglyMeasurable (fun v => ι (bq v)) μ := ι.continuous.comp_aestronglyMeasurable hbm'
    have hΦ := u1_clamp_joint hC hc hsp' ht.1 ht.2
    have h1 : AEStronglyMeasurable (fun v => (v, ι (bq v))) μ := aestronglyMeasurable_id.prodMk hfm
    have hm : AEStronglyMeasurable (u1_F Vev (fun v => ι (bq v)) t) μ :=
      (hΦ.comp_aestronglyMeasurable h1).indicator measurableSet_Iic
    have hbint : Integrable (fun v => C * ‖bq v‖) μ := (hbi.mono_set hsub).const_mul C
    exact hbint.mono' hm hbnd
  · exact hbnd

theorem winDrift_cont_proof (hE : EdgeworthHyp S β₀ m) (T : ℝ) (hT : 0 < T) (a : ℝ) (ha : 0 ≤ a)
    (bq : ℝ → NegSobolev d (rLvl d)) (hbm : Measurable (nearCoef 0 bq))
    (hbi : IntegrableOn (fun v => ‖bq v‖) (Set.Icc 0 (a + T)))
    (u u' : ℝ) (hu : 0 ≤ u) (huu : u ≤ u') (hu' : u' ≤ a + T) :
    Continuous fun t : Set.Icc (0 : ℝ) (a + T) =>
      ∫ v in Set.Ioc u (min u' (t : ℝ)),
        Vprop (regime S β₀ hE).D (regime S β₀ hE).ρ m (t : ℝ) v (NegSobolev.embed m (bq v)) := by
  obtain ⟨C, c, hC, hc, Vev, hsp⟩ := u1_vev hE
  have hsp' := hsp
  obtain ⟨hbd, heq, hcont⟩ := hsp
  have hH0 : 0 ≤ a + T := by linarith
  set ι := HRS.MD.EQInterp.embedCLM (rLvl_le hE) with hι
  have hrw : (fun t : Set.Icc (0 : ℝ) (a + T) => ∫ v in Set.Ioc u (min u' (t : ℝ)),
      Vprop (regime S β₀ hE).D (regime S β₀ hE).ρ m (t : ℝ) v (NegSobolev.embed m (bq v))) =
      fun t : Set.Icc (0 : ℝ) (a + T) => ∫ v in Set.Ioc u u', u1_F Vev (fun v => ι (bq v)) (t : ℝ) v := by
    funext t
    exact (u1_Fint hE hC hc hsp' T a hT ha bq hbm hbi u u' hu hu' t t.2).1
  rw [hrw]
  set μ : Measure ℝ := volume.restrict (Set.Ioc u u') with hμ
  have hsub : Set.Ioc u u' ⊆ Set.Icc 0 (a + T) := fun v hv => ⟨hu.trans hv.1.le, hv.2.trans hu'⟩
  have hbint : Integrable (fun v => C * ‖bq v‖) μ := (hbi.mono_set hsub).const_mul C
  refine continuous_iff_continuousAt.2 (fun t₀ => ?_)
  refine continuousAt_of_dominated (bound := fun v => C * ‖bq v‖)
    (Filter.Eventually.of_forall fun t => (u1_Fint hE hC hc hsp' T a hT ha bq hbm hbi u u' hu hu' t t.2).2.1.1)
    (Filter.Eventually.of_forall fun t => (u1_Fint hE hC hc hsp' T a hT ha bq hbm hbi u u' hu hu' t t.2).2.2)
    hbint ?_
  have hne : ∀ᵐ v ∂μ, v ≠ (t₀ : ℝ) := by
    refine ae_restrict_of_ae ?_
    have := (Set.countable_singleton (t₀ : ℝ)).ae_notMem (volume : Measure ℝ)
    filter_upwards [this] with v hv
    simpa using hv
  filter_upwards [ae_restrict_mem measurableSet_Ioc, hne] with v hv hvne
  have hv0 : 0 ≤ v := hu.trans hv.1.le
  rcases lt_or_gt_of_ne hvne with hlt | hgt
  · -- `v < t₀`
    have hs : {t : Set.Icc (0 : ℝ) (a + T) | v < (t : ℝ)} ∈ 𝓝 t₀ :=
      (isOpen_lt continuous_const continuous_subtype_val).mem_nhds hlt
    have hc1 : ContinuousOn (fun t : Set.Icc (0 : ℝ) (a + T) => Vev (t : ℝ) v (ι (bq v)))
        {t : Set.Icc (0 : ℝ) (a + T) | v < (t : ℝ)} := by
      refine (hcont (a + T) hH0 (ι (bq v))).comp
        (continuous_subtype_val.prodMk continuous_const).continuousOn ?_
      intro t ht
      exact ⟨hv0, le_of_lt ht, t.2.2⟩
    refine (hc1.continuousAt hs).congr (Filter.eventuallyEq_of_mem hs (fun t ht => ?_))
    have hvt : v ≤ (t : ℝ) := le_of_lt ht
    simp only [u1_F, Set.indicator_of_mem (Set.mem_Iic.2 hvt), u1_cl_eq hv0 hvt]
  · -- `v > t₀`
    have hs : {t : Set.Icc (0 : ℝ) (a + T) | (t : ℝ) < v} ∈ 𝓝 t₀ :=
      (isOpen_lt continuous_subtype_val continuous_const).mem_nhds hgt
    refine (continuousAt_const (y := (0 : NegSobolev d m))).congr
      (Filter.eventuallyEq_of_mem hs (fun t ht => ?_))
    have hvt : ¬ v ≤ (t : ℝ) := not_le.2 ht
    simp only [u1_F, Set.indicator_of_notMem (show v ∉ Set.Iic (t : ℝ) from hvt)]

theorem winDrift_add_proof (hE : EdgeworthHyp S β₀ m) (T : ℝ) (hT : 0 < T) (a : ℝ) (ha : 0 ≤ a)
    (b₁ b₂ : ℝ → NegSobolev d (rLvl d)) (h₁ : Measurable (nearCoef 0 b₁)) (h₂ : Measurable (nearCoef 0 b₂))
    (i₁ : IntegrableOn (fun v => ‖b₁ v‖) (Set.Icc 0 (a + T))) (i₂ : IntegrableOn (fun v => ‖b₂ v‖) (Set.Icc 0 (a + T)))
    (u u' : ℝ) (hu : 0 ≤ u) (huu : u ≤ u') (hu' : u' ≤ a + T) :
    winDrift (regime S β₀ hE) m T a ha (fun v => NegSobolev.embed m (b₁ v + b₂ v)) u u' =
      winDrift (regime S β₀ hE) m T a ha (fun v => NegSobolev.embed m (b₁ v)) u u' +
        winDrift (regime S β₀ hE) m T a ha (fun v => NegSobolev.embed m (b₂ v)) u u' := by
  obtain ⟨C, c, hC, hc, Vev, hsp⟩ := u1_vev hE
  set ι := HRS.MD.EQInterp.embedCLM (rLvl_le hE) with hι
  -- the sum
  have h12 : Measurable (nearCoef 0 (fun v => b₁ v + b₂ v)) := by
    have : nearCoef 0 (fun v => b₁ v + b₂ v) = fun v => nearCoef 0 b₁ v + nearCoef 0 b₂ v := by
      funext v; unfold nearCoef; split_ifs <;> simp
    rw [this]; exact h₁.add h₂
  have hsetm : MeasurableSet (Set.Icc (0 : ℝ) (a + T)) := measurableSet_Icc
  have i12 : IntegrableOn (fun v => ‖b₁ v + b₂ v‖) (Set.Icc 0 (a + T)) := by
    have e1 := u1_aesm_of_nearCoef h₁ hsetm (fun v hv => Set.mem_Ici.2 hv.1)
    have e2 := u1_aesm_of_nearCoef h₂ hsetm (fun v hv => Set.mem_Ici.2 hv.1)
    refine (i₁.add i₂).mono' (e1.add e2).norm ?_
    exact Filter.Eventually.of_forall fun v => by
      rw [norm_norm]; exact norm_add_le _ _
  have c1 := winDrift_cont_proof hE T hT a ha b₁ h₁ i₁ u u' hu huu hu'
  have c2 := winDrift_cont_proof hE T hT a ha b₂ h₂ i₂ u u' hu huu hu'
  have c12 := winDrift_cont_proof hE T hT a ha (fun v => b₁ v + b₂ v) h12 i12 u u' hu huu hu'
  have hint : ∀ t : Set.Icc (0 : ℝ) (a + T),
      (∫ v in Set.Ioc u (min u' (t : ℝ)), Vprop (regime S β₀ hE).D (regime S β₀ hE).ρ m (t : ℝ) v
        (NegSobolev.embed m (b₁ v + b₂ v))) =
      (∫ v in Set.Ioc u (min u' (t : ℝ)), Vprop (regime S β₀ hE).D (regime S β₀ hE).ρ m (t : ℝ) v
        (NegSobolev.embed m (b₁ v))) +
      (∫ v in Set.Ioc u (min u' (t : ℝ)), Vprop (regime S β₀ hE).D (regime S β₀ hE).ρ m (t : ℝ) v
        (NegSobolev.embed m (b₂ v))) := by
    intro t
    have hsp' := hsp
    obtain ⟨p12, -⟩ := u1_Fint hE hC hc hsp' T a hT ha (fun v => b₁ v + b₂ v) h12 i12 u u' hu hu' t t.2
    obtain ⟨p1, q1, -⟩ := u1_Fint hE hC hc hsp' T a hT ha b₁ h₁ i₁ u u' hu hu' t t.2
    obtain ⟨p2, q2, -⟩ := u1_Fint hE hC hc hsp' T a hT ha b₂ h₂ i₂ u u' hu hu' t t.2
    rw [p12, p1, p2, ← integral_add q1 q2]
    refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    have := u1_F_add Vev (fun v => ι (b₁ v)) (fun v => ι (b₂ v)) t v
    simp only [map_add] at this ⊢
    exact this
  -- the paths
  unfold winDrift driftInc
  rw [← map_add]
  congr 1
  classical
  refine HRS.MC.E213O.e213o_ext (fun t => ?_)
  rw [HRS.MC.E213O.e213o_pathOf_at' _ c12 t]
  have hadd : ∀ (w₁ w₂ : PathSpace d m (a + T)) (t : Set.Icc (0 : ℝ) (a + T)),
      (w₁ + w₂).at' t = w₁.at' t + w₂.at' t := fun _ _ _ => rfl
  rw [hadd, HRS.MC.E213O.e213o_pathOf_at' _ c1 t, HRS.MC.E213O.e213o_pathOf_at' _ c2 t]
  exact hint t

end Bounds

end HRS.MC.E213U1

end
