import HRS.MC.E213U11b
import HRS.MC.E213U2
import HRS.MC.E213U3G

/-!
# Packet e213u11, file d: deterministic bound for the window covariance tensor `J_a`

For `zr : ℝ → E_r` measurable on `[0,∞)` and bounded on `[0,a+T]`, with `b = max (a-1) 0`:
`𝒥_{a+T}(zr; (0,a+T])` exists (`IsJValue`), and its window push forward satisfies
`‖winJ‖ ≤ K₁ · M_near + K₂ ∫_{(0,a+T]∩(-∞,b)} e^{-c(a-v)}‖zr v‖ dv`, where `M_near` bounds `zr` on `[b,a+T]`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.E213U11

open HRS HRS.Sec7 HRS.Main HRS.Uniform HRS.MC.E213O HRS.MC.E213T HRS.MC.E213Plan

variable {d : ℕ}

/-- Enlarging the integration set of `IsJValue` over a set where the coefficient vanishes a.e. -/
theorem u11_isJValue_enlarge (D : DynData d) (ρ : ℝ → Torus d → ℝ) (m G : ℝ) {z : ℝ → NegSobolev d m}
    {I I' : Set ℝ} (hI' : I' ⊆ I) (hIm : MeasurableSet I) (hI'm : MeasurableSet I')
    (hz : ∀ᵐ u ∂(volume : Measure ℝ), u ∈ I \ I' → 0 ≤ u → z u = 0)
    {J : TensorDual (PathSpace d m G) 2} (h : IsJValue D ρ m G z I' J) : IsJValue D ρ m G z I J := by
  refine ⟨h.1, ?_⟩
  intro ta tb φa φb l₁ l₂ hφa hφb hta htb hl₁ hl₂
  rw [h.2 ta tb φa φb l₁ l₂ hφa hφb hta htb hl₁ hl₂]
  congr 1
  refine (setIntegral_eq_of_subset_of_ae_sdiff_eq_zero (hIm.inter measurableSet_Icc).nullMeasurableSet
    (Set.inter_subset_inter hI' (subset_refl _)) ?_).symm
  filter_upwards [hz] with u hu hmem
  have h1 : u ∈ I \ I' := by
    refine ⟨hmem.1.1, fun h' => hmem.2 ⟨h', hmem.1.2⟩⟩
  rw [hu h1 hmem.1.2.1]
  exact HRS.MC.E213U2.e213u2_eval_zero _

/-- The tensor behind `winJ` only depends on the coefficient on `I ∩ [0,∞)`. -/
theorem u11_jTensor_congr (R : Regime d) (m G : ℝ) {z z' : ℝ → NegSobolev d m} {I : Set ℝ}
    (hIm : MeasurableSet I) (hzz : ∀ u ∈ I, 0 ≤ u → z u = z' u) :
    jTensor R.D R.ρ m G z I = jTensor R.D R.ρ m G z' I := by
  by_cases hex : ∃ J, IsJValue R.D R.ρ m G z I J
  · obtain ⟨J, hJ⟩ := hex
    have hJ' : IsJValue R.D R.ρ m G z' I J := HRS.MC.E213U3.u3_IsJValue_congr R.D R.ρ m G hIm hzz hJ
    rw [HRS.MC.E213U2.e213u2_jTensor_eq R m G z I J hJ, HRS.MC.E213U2.e213u2_jTensor_eq R m G z' I J hJ']
  · have hex' : ¬ ∃ J, IsJValue R.D R.ρ m G z' I J := by
      rintro ⟨J, hJ⟩
      exact hex ⟨J, HRS.MC.E213U3.u3_IsJValue_congr R.D R.ρ m G hIm (fun u hu hu0 => (hzz u hu hu0).symm) hJ⟩
    unfold jTensor
    rw [dif_neg hex, dif_neg hex']


section JBound

variable {S : PreparedData d} {β₀ m : ℝ}

theorem u11_winJ_bound (hE : EdgeworthHyp S β₀ m) (T : ℝ) (hT : 0 < T) :
    ∃ K₁ K₂ c : ℝ, 0 < K₁ ∧ 0 < K₂ ∧ 0 < c ∧ ∀ (a : ℝ) (ha : 0 ≤ a) (zr : ℝ → NegSobolev d (rLvl d)),
      Measurable (nearCoef 0 zr) → ∀ M₀ Mn : ℝ, (∀ v ∈ Set.Icc 0 (a + T), ‖zr v‖ ≤ M₀) →
      (∀ v ∈ Set.Icc (max (a - 1) 0) (a + T), ‖zr v‖ ≤ Mn) →
      (∃ J, IsJValue (regime S β₀ hE).D (regime S β₀ hE).ρ m (a + T) (fun v => NegSobolev.embed m (zr v))
          (Set.Ioc 0 (a + T)) J) ∧
      ‖winJ (regime S β₀ hE) m T a ha (fun v => NegSobolev.embed m (zr v)) (Set.Ioc 0 (a + T))‖ ≤
        K₁ * Mn + K₂ * ∫ v in Set.Ioc 0 (a + T) ∩ Set.Iio (max (a - 1) 0),
          Real.exp (-c * (a - v)) * ‖zr v‖ := by
  classical
  obtain ⟨Cn, hCn0, hnear⟩ := HRS.MC.E213U2.winJ_near_proof hE T hT 1 one_pos
  obtain ⟨Cf, c, hCf, hc, hfar⟩ := HRS.MC.E213U3.winJ_far_proof hE T hT
  have hrm : rLvl d ≤ m := rLvl_le hE
  refine ⟨Cn * (T + 1), Cf, c, by positivity, hCf, hc, fun a ha zr hzm M₀ Mn hM₀ hMn => ?_⟩
  set R := regime S β₀ hE with hR
  set b : ℝ := max (a - 1) 0 with hb
  set H : ℝ := a + T with hH
  have hb0 : 0 ≤ b := le_max_right _ _
  have hba : b ≤ a := max_le (by linarith) ha
  have hab : a - b ≤ 1 := by
    have : a - 1 ≤ b := le_max_left _ _
    linarith
  have hHpos : 0 < H := by rw [hH]; linarith
  have hbH : b ≤ H := by rw [hH]; linarith
  have hM00 : 0 ≤ M₀ := (norm_nonneg _).trans (hM₀ 0 ⟨le_rfl, hHpos.le⟩)
  have hMn0 : 0 ≤ Mn := (norm_nonneg _).trans (hMn b ⟨le_rfl, hbH⟩)
  -- near part
  obtain ⟨⟨J₁, hJ₁⟩, hn⟩ := hnear a ha b hb0 hba hab zr hzm Mn hMn b H hb0 hbH le_rfl
  -- far part
  have hae : AEStronglyMeasurable zr (volume.restrict (Set.Ioc 0 (min b H))) :=
    HRS.MC.E213U1.u1_aesm_of_nearCoef hzm measurableSet_Ioc (fun v hv => Set.mem_Ici.2 hv.1.le)
  have hint : IntegrableOn (fun v => Real.exp (-c * (a - v)) * ‖zr v‖) (Set.Ioc 0 (min b H)) := by
    haveI : IsFiniteMeasure (volume.restrict (Set.Ioc (0 : ℝ) (min b H))) := Real.isFiniteMeasure_restrict_Ioc _ _
    refine Integrable.mono' (g := fun _ => Real.exp (c * T) * M₀) (integrable_const _) ?_ ?_
    · exact ((Real.continuous_exp.comp (continuous_const.mul (continuous_const.sub continuous_id))).aestronglyMeasurable).mul
        hae.norm
    · refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun v hv => ?_)
      have hvH : v ∈ Set.Icc 0 H := ⟨hv.1.le, hv.2.trans (min_le_right _ _)⟩
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (norm_nonneg _))]
      refine mul_le_mul ?_ (hM₀ v hvH) (norm_nonneg _) (Real.exp_pos _).le
      exact Real.exp_le_exp.2 (by nlinarith [hvH.2])
  obtain ⟨⟨J₂, hJ₂⟩, hf⟩ := hfar a ha b hb0 zr hzm hint 0 H le_rfl hHpos.le le_rfl
  -- enlarge the near tensor to `(0,H]`
  have hJ₁' : IsJValue R.D R.ρ m H (nearCoef b (fun v => NegSobolev.embed m (zr v))) (Set.Ioc 0 H) J₁ := by
    refine u11_isJValue_enlarge R.D R.ρ m H (I' := Set.Ioc b H) ?_ measurableSet_Ioc measurableSet_Ioc ?_ hJ₁
    · exact Set.Ioc_subset_Ioc_left hb0
    · have hne : ∀ᵐ u ∂(volume : Measure ℝ), u ≠ b := by
        have := (Set.countable_singleton b).ae_notMem (volume : Measure ℝ)
        filter_upwards [this] with u hu
        simpa using hu
      filter_upwards [hne] with u hu hmem _
      have hle : u ≤ b := by
        by_contra hcon
        exact hmem.2 ⟨not_le.1 hcon, hmem.1.2⟩
      unfold nearCoef
      rw [if_neg (not_le.2 (lt_of_le_of_ne hle hu))]
  -- the splitting of the coefficient
  set z₁ : ℝ → NegSobolev d (rLvl d) := nearCoef b zr with hz₁
  set z₂ : ℝ → NegSobolev d (rLvl d) := farCoef b zr with hz₂
  have hm1 : Measurable (nearCoef 0 z₁) := u11_measurable_nearCoef_near hzm hb0
  have hm2 : Measurable (nearCoef 0 z₂) := u11_measurable_nearCoef_far hzm b
  have hb1 : ∀ v ∈ Set.Icc (0 : ℝ) H, ‖z₁ v‖ ≤ M₀ := fun v hv => by
    rw [hz₁]; unfold nearCoef; split_ifs
    · exact hM₀ v hv
    · rw [norm_zero]; exact hM00
  have hb2 : ∀ v ∈ Set.Icc (0 : ℝ) H, ‖z₂ v‖ ≤ M₀ := fun v hv => by
    rw [hz₂]; unfold farCoef; split_ifs
    · exact hM₀ v hv
    · rw [norm_zero]; exact hM00
  have hzz : (fun v => z₁ v + z₂ v) = zr := nearCoef_add_farCoef b zr
  have hzv : ∀ v, z₁ v + z₂ v = zr v := fun v => congrFun hzz v
  have hJ₁'' : IsJValue R.D R.ρ m H (fun v => NegSobolev.embed m (z₁ v)) (Set.Ioc 0 H) J₁ := by
    rw [hz₁, ← u11_nearCoef_embed hrm]; exact hJ₁'
  have hJ₂'' : IsJValue R.D R.ρ m H (fun v => NegSobolev.embed m (z₂ v)) (Set.Ioc 0 H) J₂ := by
    rw [hz₂, ← u11_farCoef_embed hrm]; exact hJ₂
  have hsum := HRS.MC.E213U2.e213u2_isJValue_add R m hE.m_gt H hHpos z₁ z₂ hm1 hm2 M₀ M₀ hb1 hb2 _
    measurableSet_Ioc (Set.Ioc_subset_Ioc_left le_rfl) J₁ J₂ hJ₁'' hJ₂''
  simp only [hzv] at hsum
  refine ⟨⟨_, hsum⟩, ?_⟩
  -- the norm bound
  have hadd := HRS.MC.E213U2.winJ_add_proof hE T hT a ha z₁ z₂ hm1 hm2 M₀ M₀ hb1 hb2 0 H le_rfl hHpos.le le_rfl
  simp only [hzv] at hadd
  rw [hadd]
  have hw1 : winJ R m T a ha (fun v => NegSobolev.embed m (z₁ v)) (Set.Ioc 0 H) =
      winJ R m T a ha (fun v => NegSobolev.embed m (z₁ v)) (Set.Ioc b H) := by
    unfold winJ
    rw [HRS.MC.E213U2.e213u2_jTensor_eq R m H _ _ J₁ hJ₁'',
      HRS.MC.E213U2.e213u2_jTensor_eq R m H _ _ J₁ (by rw [hz₁, ← u11_nearCoef_embed hrm]; exact hJ₁)]
  rw [hw1]
  have hn' : ‖winJ R m T a ha (fun v => NegSobolev.embed m (z₁ v)) (Set.Ioc b H)‖ ≤ Cn * Mn * (H - b) := by
    rw [hz₁, ← u11_nearCoef_embed hrm]; exact hn
  have hf' : ‖winJ R m T a ha (fun v => NegSobolev.embed m (z₂ v)) (Set.Ioc 0 H)‖ ≤
      Cf * ∫ v in Set.Ioc 0 H ∩ Set.Iio b, Real.exp (-c * (a - v)) * ‖zr v‖ := by
    rw [hz₂, ← u11_farCoef_embed hrm]; exact hf
  refine (norm_add_le (winJ R m T a ha (fun v => NegSobolev.embed m (z₁ v)) (Set.Ioc b H))
    (winJ R m T a ha (fun v => NegSobolev.embed m (z₂ v)) (Set.Ioc 0 H))).trans ?_
  calc _ ≤ Cn * Mn * (H - b) + Cf * ∫ v in Set.Ioc 0 H ∩ Set.Iio b, Real.exp (-c * (a - v)) * ‖zr v‖ :=
        add_le_add hn' hf'
    _ ≤ Cn * (T + 1) * Mn + Cf * ∫ v in Set.Ioc 0 H ∩ Set.Iio b, Real.exp (-c * (a - v)) * ‖zr v‖ := by
        refine add_le_add ?_ le_rfl
        have : H - b ≤ T + 1 := by
          have : a - 1 ≤ b := le_max_left _ _
          rw [hH]; linarith
        nlinarith [mul_nonneg hCn0.le hMn0]

end JBound

end HRS.MC.E213U11

end
