import HRS.MS.Fp81S21GaussG4U823
import HRS.MS.Fp81S21GaussG4U812
import HRS.Main.A34Aux2
import HRS.MS.SharpBiasAux1

/-! Generic Hilbert-space energy convergence for propagated fields. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Filter Topology Set
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.S111K4AT HRS.MS.ProClosureS111

/-- Squared L² energies converge when the squared L² energy of the error
converges to zero. This applies to any linear propagated field once its
pointwise difference and its L² representative have been identified. -/
theorem fp81s21_g4_l2_energy_continuous {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {d : ℕ} (g : α → Euc d) (G : ℕ → α → Euc d)
    (hg : MemLp g 2 μ) (hG : ∀ n, MemLp (G n) 2 μ)
    (herr : Tendsto (fun n => ∫ x, ‖G n x - g x‖ ^ 2 ∂μ) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, ‖G n x‖ ^ 2 ∂μ) atTop
      (𝓝 (∫ x, ‖g x‖ ^ 2 ∂μ)) := by
  have he : Tendsto (fun n => Real.sqrt (∫ x, ‖G n x - g x‖ ^ 2 ∂μ))
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.sqrt_zero] using
      Real.continuous_sqrt.continuousAt.tendsto.comp herr
  have hr : Tendsto (fun n => Real.sqrt (∫ x, ‖G n x‖ ^ 2 ∂μ)) atTop
      (𝓝 (Real.sqrt (∫ x, ‖g x‖ ^ 2 ∂μ))) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    have hs := tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds he
      (fun n => abs_nonneg (Real.sqrt (∫ x, ‖G n x‖ ^ 2 ∂μ) -
        Real.sqrt (∫ x, ‖g x‖ ^ 2 ∂μ)))
      (fun n => HRS.A34.a34_sqrt_tri (hG n) hg)
    simpa only [Real.norm_eq_abs] using hs
  have hp := hr.pow 2
  simpa only [Real.sq_sqrt (integral_nonneg fun x => sq_nonneg ‖G _ x‖),
    Real.sq_sqrt (integral_nonneg fun x => sq_nonneg ‖g x‖)] using hp

/-- The new-interval energy is bounded by the uniform propagator budget. -/
theorem fp81s21_g4_new_stability (p : Parameters) :
    fp81s21_g4Phys p (fun _ R =>
      ∃ B : ℝ, 0 ≤ B ∧ ∀ g : Euc p.d → ℝ,
        IsOscTest (wholeSpaceIndex p.d : ℝ) g →
        ∀ v w : ℝ, 0 ≤ v → v ≤ w →
          fp81s21_g4_New R g v w ≤ B * fp81s21_g4_J p.d g) := by
  obtain ⟨δ0, hδ0, hhalf, hstab⟩ := fp81s21_g4_propagator_stability p
  refine ⟨δ0, hδ0, hhalf, ?_⟩
  intro δ hδ hδle R
  obtain ⟨B, hB, hbudget⟩ := hstab δ hδ hδle R
  refine ⟨B, hB, ?_⟩
  intro g hg v w hv hvw
  obtain ⟨_, hi, hb, _⟩ := hbudget g hg w (hv.trans hvw)
  unfold fp81s21_g4_New
  refine (setIntegral_mono_set hi ?_ ?_).trans hb
  · exact Filter.Eventually.of_forall fun r => integral_nonneg fun x => sq_nonneg _
  · exact Filter.Eventually.of_forall (Icc_subset_Icc_left hv)

/-- The centered initial increment is bounded by the same stability budget. -/
theorem fp81s21_g4_initial_stability (p : Parameters) :
    fp81s21_g4Phys p (fun _ R =>
      ∃ B : ℝ, 0 ≤ B ∧ ∀ g : Euc p.d → ℝ,
        IsOscTest (wholeSpaceIndex p.d : ℝ) g →
        ∀ v w : ℝ, 0 ≤ v → v ≤ w →
          fp81s21_g4_initialValue R g v w ≤ 4 * B * fp81s21_g4_J p.d g) := by
  obtain ⟨δ0, hδ0, hhalf, hstab⟩ := fp81s21_g4_propagator_stability p
  refine ⟨δ0, hδ0, hhalf, ?_⟩
  intro δ hδ hδle R
  obtain ⟨B, hB, hbudget⟩ := hstab δ hδ hδle R
  refine ⟨B, hB, ?_⟩
  intro g hg v w hv hvw
  let μ := HRS.Whole.withDensityReal R.ρβ
  letI : IsProbabilityMeasure μ := HRS.Whole.Q34.isProbabilityMeasure_nu R.thermal.1.1
  let a := r26t3_U R 0 w g
  let b := r26t3_U R 0 v g
  have hw := (hbudget g hg w (hv.trans hvw)).2.2.2 0 ⟨le_rfl, hv.trans hvw⟩
  have hv' := (hbudget g hg v hv).2.2.2 0 ⟨le_rfl, hv⟩
  have ha : MemLp a 2 μ := hw.1
  have hb : MemLp b 2 μ := hv'.1
  have hpa : MemLp (HRS.Whole.projMean μ a) 2 μ := ha.sub (memLp_const _)
  have hpb : MemLp (HRS.Whole.projMean μ b) 2 μ := hb.sub (memLp_const _)
  have heq : HRS.Whole.projMean μ (fun x => a x - b x) =
      fun x => HRS.Whole.projMean μ a x - HRS.Whole.projMean μ b x := by
    funext x
    simp only [HRS.Whole.projMean, HRS.Whole.pair, integral_sub (ha.integrable one_le_two) (hb.integrable one_le_two)]
    ring
  have htri := HRS.Whole.S71.s71_l2Norm_sub_le hpa hpb
  rw [← heq] at htri
  have hJ : 0 ≤ fp81s21_g4_J p.d g := by
    unfold fp81s21_g4_J
    exact sq_nonneg _
  have hC : 0 ≤ B * fp81s21_g4_J p.d g := mul_nonneg hB hJ
  have hra := Real.sqrt_le_sqrt hw.2
  have hrb := Real.sqrt_le_sqrt hv'.2
  have hi : 0 ≤ fp81s21_g4_initialValue R g v w := by
    unfold fp81s21_g4_initialValue
    exact integral_nonneg fun x => sq_nonneg _
  change Real.sqrt (fp81s21_g4_initialValue R g v w) ≤
    Real.sqrt (∫ x, (HRS.Whole.projMean μ a x)^2 ∂μ) +
    Real.sqrt (∫ x, (HRS.Whole.projMean μ b x)^2 ∂μ) at htri
  have hs := Real.sq_sqrt hi
  have hc := Real.sq_sqrt hC
  have hsi := Real.sqrt_nonneg (fp81s21_g4_initialValue R g v w)
  have hsc := Real.sqrt_nonneg (B * fp81s21_g4_J p.d g)
  have hia : Real.sqrt (fp81s21_g4_initialValue R g v w) ≤
      2 * Real.sqrt (B * fp81s21_g4_J p.d g) := by linarith
  nlinarith

/-- The old-interval energy is bounded by two propagator budgets on the
same time-space measure. -/
theorem fp81s21_g4_old_stability (p : Parameters) :
    fp81s21_g4Phys p (fun _ R =>
      ∃ B : ℝ, 0 ≤ B ∧ ∀ g : Euc p.d → ℝ,
        IsOscTest (wholeSpaceIndex p.d : ℝ) g →
        ∀ v w : ℝ, 0 ≤ v → v ≤ w →
          fp81s21_g4_Old R g v w ≤ 4 * B * fp81s21_g4_J p.d g) := by
  obtain ⟨δ0, hδ0, hhalf, hstab⟩ := fp81s21_g4_propagator_stability p
  refine ⟨δ0, hδ0, hhalf, ?_⟩
  intro δ hδ hδle R
  obtain ⟨B, hB, hbudget⟩ := hstab δ hδ hδle R
  refine ⟨B, hB, ?_⟩
  intro g hg v w hv hvw
  let μ := HRS.Whole.withDensityReal R.ρβ
  letI : IsProbabilityMeasure μ := HRS.Whole.Q34.isProbabilityMeasure_nu R.thermal.1.1
  let ν := (volume.restrict (Icc (0 : ℝ) v)).prod μ
  let a : ℝ × Euc p.d → Euc p.d := fun z => gradient (r26t3_U R z.1 w g) z.2
  let b : ℝ × Euc p.d → Euc p.d := fun z => gradient (r26t3_U R z.1 v g) z.2
  obtain ⟨haw, hai, hab, _⟩ := hbudget g hg w (hv.trans hvw)
  obtain ⟨hbm, _, hbb, _⟩ := hbudget g hg v hv
  have hν : ν ≤ (volume.restrict (Icc (0 : ℝ) w)).prod μ :=
    Measure.prod_mono (Measure.restrict_mono (Icc_subset_Icc_right hvw) le_rfl) le_rfl
  have ha : MemLp a 2 ν := haw.mono_measure hν
  have hb : MemLp b 2 ν := hbm
  have haI : Integrable (fun z => ‖a z‖^2) ν :=
    (memLp_two_iff_integrable_sq_norm ha.aestronglyMeasurable).1 ha
  have hbI : Integrable (fun z => ‖b z‖^2) ν :=
    (memLp_two_iff_integrable_sq_norm hb.aestronglyMeasurable).1 hb
  have hd : MemLp (a - b) 2 ν := ha.sub hb
  have hdI : Integrable (fun z => ‖(a-b) z‖^2) ν :=
    (memLp_two_iff_integrable_sq_norm hd.aestronglyMeasurable).1 hd
  have hA : ‖ha.toLp a‖^2 ≤ B * fp81s21_g4_J p.d g := by
    rw [HRS.A34.a34_norm_toLp_sq ha, integral_prod _ haI]
    exact (setIntegral_mono_set hai
      (Filter.Eventually.of_forall fun r => integral_nonneg fun x => sq_nonneg _)
      (Filter.Eventually.of_forall (Icc_subset_Icc_right hvw))).trans hab
  have hB' : ‖hb.toLp b‖^2 ≤ B * fp81s21_g4_J p.d g := by
    rw [HRS.A34.a34_norm_toLp_sq hb, integral_prod _ hbI]
    exact hbb
  have hOld : fp81s21_g4_Old R g v w = ‖ha.toLp a - hb.toLp b‖^2 := by
    rw [← MemLp.toLp_sub ha hb, HRS.A34.a34_norm_toLp_sq hd,
      integral_prod _ hdI]
    rfl
  rw [hOld]
  have htri := norm_sub_le (ha.toLp a) (hb.toLp b)
  have hn : 0 ≤ ‖ha.toLp a - hb.toLp b‖ := norm_nonneg _
  have hna : 0 ≤ ‖ha.toLp a‖ := norm_nonneg _
  have hnb : 0 ≤ ‖hb.toLp b‖ := norm_nonneg _
  nlinarith [sq_nonneg (‖ha.toLp a‖ - ‖hb.toLp b‖)]

/-- All three propagated error energies vanish under G4-cost convergence. -/
theorem fp81s21_g4_piece_errors_tendsto (p : Parameters) :
    fp81s21_g4Phys p (fun _ R =>
      ∀ f : Euc p.d → ℝ, IsOscTest (wholeSpaceIndex p.d : ℝ) f →
      ∀ F : ℕ → Euc p.d → ℝ,
        (∀ n, IsOscTest (wholeSpaceIndex p.d : ℝ) (F n)) →
        Tendsto (fun n => fp81s21_g4_J p.d (F n - f)) atTop (𝓝 0) →
      ∀ v w : ℝ, 0 ≤ v → v ≤ w →
        Tendsto (fun n => fp81s21_g4_initialValue R (F n - f) v w) atTop (𝓝 0) ∧
        Tendsto (fun n => fp81s21_g4_Old R (F n - f) v w) atTop (𝓝 0) ∧
        Tendsto (fun n => fp81s21_g4_New R (F n - f) v w) atTop (𝓝 0)) := by
  obtain ⟨δi, hi, hihalf, hinit⟩ := fp81s21_g4_initial_stability p
  obtain ⟨δo, ho, _, hold⟩ := fp81s21_g4_old_stability p
  obtain ⟨δn, hn, _, hnew⟩ := fp81s21_g4_new_stability p
  refine ⟨min δi (min δo δn), lt_min hi (lt_min ho hn),
    (min_le_left _ _).trans hihalf, ?_⟩
  intro δ hδ hδle R
  obtain ⟨Bi, _, hBi⟩ := hinit δ hδ (hδle.trans (min_le_left _ _)) R
  obtain ⟨Bo, _, hBo⟩ := hold δ hδ
    (hδle.trans ((min_le_right _ _).trans (min_le_left _ _))) R
  obtain ⟨Bn, _, hBn⟩ := hnew δ hδ
    (hδle.trans ((min_le_right _ _).trans (min_le_right _ _))) R
  intro f hf F hF hconv v w hv hvw
  have herr (n : ℕ) : IsOscTest (wholeSpaceIndex p.d : ℝ) (F n - f) :=
    ⟨(hF n).1.sub hf.1, HRS.MS.MovLin.mov2d_memOsc_sub (hF n).2 hf.2⟩
  have hci : Tendsto (fun n => (4 * Bi) * fp81s21_g4_J p.d (F n - f))
      atTop (𝓝 0) := by simpa using hconv.const_mul (4 * Bi)
  have hco : Tendsto (fun n => (4 * Bo) * fp81s21_g4_J p.d (F n - f))
      atTop (𝓝 0) := by simpa using hconv.const_mul (4 * Bo)
  have hcn : Tendsto (fun n => Bn * fp81s21_g4_J p.d (F n - f))
      atTop (𝓝 0) := by simpa using hconv.const_mul Bn
  refine ⟨?_, ?_, ?_⟩
  · refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hci ?_ ?_
    · intro n
      unfold fp81s21_g4_initialValue
      exact integral_nonneg fun x => sq_nonneg _
    · exact fun n => hBi (F n - f) (herr n) v w hv hvw
  · refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hco ?_ ?_
    · intro n
      unfold fp81s21_g4_Old
      exact integral_nonneg fun r => integral_nonneg fun x => sq_nonneg _
    · exact fun n => hBo (F n - f) (herr n) v w hv hvw
  · refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hcn ?_ ?_
    · intro n
      unfold fp81s21_g4_New
      exact integral_nonneg fun r => integral_nonneg fun x => sq_nonneg _
    · exact fun n => hBn (F n - f) (herr n) v w hv hvw

/-- The chosen adjoint propagator preserves subtraction of oscillator tests. -/
theorem fp81s21_g4_U_sub (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    {f g : Euc p.d → ℝ}
    (hf : IsOscTest (wholeSpaceIndex p.d : ℝ) f)
    (hg : IsOscTest (wholeSpaceIndex p.d : ℝ) g)
    {r t : ℝ} (ht : 0 ≤ t) (hr : r ∈ Icc (0 : ℝ) t) :
    r26t3_U R r t (f - g) = r26t3_U R r t f - r26t3_U R r t g := by
  have h := fp81s21_U_linear_of_osc_test p R hf hg (-1) ht hr
  have hi : (fun x => f x + (-1 : ℝ) * g x) = f - g := by
    funext x
    simp [sub_eq_add_neg]
  have ho : (fun x => r26t3_U R r t f x + (-1 : ℝ) * r26t3_U R r t g x) =
      r26t3_U R r t f - r26t3_U R r t g := by
    funext x
    simp [sub_eq_add_neg]
  rw [hi, ho] at h
  exact h

/-- The gradients of propagated oscillator tests also preserve subtraction. -/
theorem fp81s21_g4_gradient_U_sub (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    {f g : Euc p.d → ℝ}
    (hf : IsOscTest (wholeSpaceIndex p.d : ℝ) f)
    (hg : IsOscTest (wholeSpaceIndex p.d : ℝ) g)
    {r t : ℝ} (ht : 0 ≤ t) (hr : r ∈ Icc (0 : ℝ) t) (x : Euc p.d) :
    gradient (r26t3_U R r t (f - g)) x =
      gradient (r26t3_U R r t f) x - gradient (r26t3_U R r t g) x := by
  rw [fp81s21_g4_U_sub p R hf hg ht hr]
  exact HRS.MS.R2WinOrbNL.s104g_gradient_sub
    ((fp81s21_U_osc_test_classical p R hf ht).c2 r hr |>.differentiable (by norm_num) x)
    ((fp81s21_U_osc_test_classical p R hg ht).c2 r hr |>.differentiable (by norm_num) x)

/-- New-interval energy is continuous under convergence in G4 cost. -/
theorem fp81s21_g4_new_continuous (p : Parameters) :
    fp81s21_g4Phys p (fun _ R =>
      ∀ f : Euc p.d → ℝ, IsOscTest (wholeSpaceIndex p.d : ℝ) f →
      ∀ F : ℕ → Euc p.d → ℝ,
        (∀ n, IsOscTest (wholeSpaceIndex p.d : ℝ) (F n)) →
        Tendsto (fun n => fp81s21_g4_J p.d (F n - f)) atTop (𝓝 0) →
      ∀ v w : ℝ, 0 ≤ v → v ≤ w →
        Tendsto (fun n => fp81s21_g4_New R (F n) v w) atTop
          (𝓝 (fp81s21_g4_New R f v w))) := by
  obtain ⟨δs, hs, hhalf, hstab⟩ := fp81s21_g4_propagator_stability p
  obtain ⟨δe, he, _, herr⟩ := fp81s21_g4_piece_errors_tendsto p
  refine ⟨min δs δe, lt_min hs he, (min_le_left _ _).trans hhalf, ?_⟩
  intro δ hδ hδle R
  obtain ⟨B, hB, hbudget⟩ := hstab δ hδ (hδle.trans (min_le_left _ _)) R
  have herrR := herr δ hδ (hδle.trans (min_le_right _ _)) R
  intro f hf F hF hconv v w hv hvw
  let μ := HRS.Whole.withDensityReal R.ρβ
  letI : IsProbabilityMeasure μ := HRS.Whole.Q34.isProbabilityMeasure_nu R.thermal.1.1
  let ν := (volume.restrict (Icc v w)).prod μ
  let A : ℕ → ℝ × Euc p.d → Euc p.d := fun n z =>
    gradient (r26t3_U R z.1 w (F n)) z.2
  let a : ℝ × Euc p.d → Euc p.d := fun z => gradient (r26t3_U R z.1 w f) z.2
  have hν : ν ≤ (volume.restrict (Icc (0 : ℝ) w)).prod μ :=
    Measure.prod_mono (Measure.restrict_mono (Icc_subset_Icc_left hv) le_rfl) le_rfl
  have ha : MemLp a 2 ν := ((hbudget f hf w (hv.trans hvw)).1).mono_measure hν
  have hA (n : ℕ) : MemLp (A n) 2 ν :=
    ((hbudget (F n) (hF n) w (hv.trans hvw)).1).mono_measure hν
  have hval (g : Euc p.d → ℝ)
      (hg : MemLp (fun z : ℝ × Euc p.d => gradient (r26t3_U R z.1 w g) z.2) 2 ν) :
      (∫ z, ‖gradient (r26t3_U R z.1 w g) z.2‖^2 ∂ν) =
        fp81s21_g4_New R g v w := by
    have hgi := (memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable).1 hg
    rw [integral_prod _ hgi]
    rfl
  have hdiff (n : ℕ) :
      (∫ z, ‖A n z - a z‖^2 ∂ν) = fp81s21_g4_New R (F n - f) v w := by
    have hdi := (memLp_two_iff_integrable_sq_norm ((hA n).sub ha).aestronglyMeasurable).1
      ((hA n).sub ha)
    change (∫ z, ‖((A n) - a) z‖^2 ∂ν) = _
    rw [integral_prod _ hdi]
    unfold fp81s21_g4_New
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
    apply integral_congr_ae
    filter_upwards with x
    change ‖gradient (r26t3_U R r w (F n)) x - gradient (r26t3_U R r w f) x‖^2 = _
    rw [fp81s21_g4_gradient_U_sub p R (hF n) hf (hv.trans hvw)
      ⟨hv.trans hr.1, hr.2⟩ x]
  have herror : Tendsto (fun n => ∫ z, ‖A n z - a z‖^2 ∂ν) atTop (𝓝 0) := by
    simpa only [hdiff] using (herrR f hf F hF hconv v w hv hvw).2.2
  have hlim := fp81s21_g4_l2_energy_continuous a A ha hA herror
  have hvals : (fun n => ∫ z, ‖A n z‖^2 ∂ν) =
      (fun n => fp81s21_g4_New R (F n) v w) := by
    funext n
    exact hval (F n) (hA n)
  have hvalf : (∫ z, ‖a z‖^2 ∂ν) = fp81s21_g4_New R f v w := hval f ha
  rw [hvals, hvalf] at hlim
  exact hlim

/-- Old-interval energy is continuous under convergence in G4 cost. -/
theorem fp81s21_g4_old_continuous (p : Parameters) :
    fp81s21_g4Phys p (fun _ R =>
      ∀ f : Euc p.d → ℝ, IsOscTest (wholeSpaceIndex p.d : ℝ) f →
      ∀ F : ℕ → Euc p.d → ℝ,
        (∀ n, IsOscTest (wholeSpaceIndex p.d : ℝ) (F n)) →
        Tendsto (fun n => fp81s21_g4_J p.d (F n - f)) atTop (𝓝 0) →
      ∀ v w : ℝ, 0 ≤ v → v ≤ w →
        Tendsto (fun n => fp81s21_g4_Old R (F n) v w) atTop
          (𝓝 (fp81s21_g4_Old R f v w))) := by
  obtain ⟨δs, hs, hhalf, hstab⟩ := fp81s21_g4_propagator_stability p
  obtain ⟨δe, he, _, herr⟩ := fp81s21_g4_piece_errors_tendsto p
  refine ⟨min δs δe, lt_min hs he, (min_le_left _ _).trans hhalf, ?_⟩
  intro δ hδ hδle R
  obtain ⟨B, hB, hbudget⟩ := hstab δ hδ (hδle.trans (min_le_left _ _)) R
  have herrR := herr δ hδ (hδle.trans (min_le_right _ _)) R
  intro f hf F hF hconv v w hv hvw
  let μ := HRS.Whole.withDensityReal R.ρβ
  letI : IsProbabilityMeasure μ := HRS.Whole.Q34.isProbabilityMeasure_nu R.thermal.1.1
  let ν := (volume.restrict (Icc (0 : ℝ) v)).prod μ
  let field : (Euc p.d → ℝ) → ℝ × Euc p.d → Euc p.d := fun g z =>
    gradient (r26t3_U R z.1 w g) z.2 - gradient (r26t3_U R z.1 v g) z.2
  have hν : ν ≤ (volume.restrict (Icc (0 : ℝ) w)).prod μ :=
    Measure.prod_mono (Measure.restrict_mono (Icc_subset_Icc_right hvw) le_rfl) le_rfl
  have hfield (g : Euc p.d → ℝ) (hg : IsOscTest (wholeSpaceIndex p.d : ℝ) g) :
      MemLp (field g) 2 ν :=
    (((hbudget g hg w (hv.trans hvw)).1).mono_measure hν).sub ((hbudget g hg v hv).1)
  let A : ℕ → ℝ × Euc p.d → Euc p.d := fun n => field (F n)
  let a : ℝ × Euc p.d → Euc p.d := field f
  have ha : MemLp a 2 ν := hfield f hf
  have hA (n : ℕ) : MemLp (A n) 2 ν := hfield (F n) (hF n)
  have hval (g : Euc p.d → ℝ) (hg : IsOscTest (wholeSpaceIndex p.d : ℝ) g) :
      (∫ z, ‖field g z‖^2 ∂ν) = fp81s21_g4_Old R g v w := by
    have hm := hfield g hg
    have hi := (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).1 hm
    rw [integral_prod _ hi]
    rfl
  have hdiff (n : ℕ) :
      (∫ z, ‖A n z - a z‖^2 ∂ν) = fp81s21_g4_Old R (F n - f) v w := by
    have hm := (hA n).sub ha
    have hi := (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).1 hm
    change (∫ z, ‖((A n) - a) z‖^2 ∂ν) = _
    rw [integral_prod _ hi]
    unfold fp81s21_g4_Old
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
    apply integral_congr_ae
    filter_upwards with x
    change ‖(gradient (r26t3_U R r w (F n)) x - gradient (r26t3_U R r v (F n)) x) -
      (gradient (r26t3_U R r w f) x - gradient (r26t3_U R r v f) x)‖^2 = _
    rw [fp81s21_g4_gradient_U_sub p R (hF n) hf (hv.trans hvw)
      ⟨hr.1, hr.2.trans hvw⟩ x,
      fp81s21_g4_gradient_U_sub p R (hF n) hf hv hr x]
    congr 1
    congr 1
    abel
  have herror : Tendsto (fun n => ∫ z, ‖A n z - a z‖^2 ∂ν) atTop (𝓝 0) := by
    simpa only [hdiff] using (herrR f hf F hF hconv v w hv hvw).2.1
  have hlim := fp81s21_g4_l2_energy_continuous a A ha hA herror
  have hvals : (fun n => ∫ z, ‖A n z‖^2 ∂ν) =
      (fun n => fp81s21_g4_Old R (F n) v w) := by
    funext n
    exact hval (F n) (hF n)
  have hvalf : (∫ z, ‖a z‖^2 ∂ν) = fp81s21_g4_Old R f v w := hval f hf
  rw [hvals, hvalf] at hlim
  exact hlim

/-- Scalar L² energies converge when the squared L² error vanishes. -/
theorem fp81s21_g4_real_l2_energy_continuous {d : ℕ}
    {μ : Measure (Euc d)} (g : Euc d → ℝ) (G : ℕ → Euc d → ℝ)
    (hg : MemLp g 2 μ) (hG : ∀ n, MemLp (G n) 2 μ)
    (herr : Tendsto (fun n => ∫ x, (G n x - g x)^2 ∂μ) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, (G n x)^2 ∂μ) atTop (𝓝 (∫ x, (g x)^2 ∂μ)) := by
  have he : Tendsto (fun n => HRS.Whole.l2Norm μ (G n - g)) atTop (𝓝 0) := by
    have h := Real.continuous_sqrt.continuousAt.tendsto.comp herr
    simpa only [Function.comp_def, Real.sqrt_zero, HRS.Whole.l2Norm, Pi.sub_apply] using h
  have htri (n : ℕ) :
      |HRS.Whole.l2Norm μ (G n) - HRS.Whole.l2Norm μ g| ≤
        HRS.Whole.l2Norm μ (G n - g) := by
    have e1 := HRS.Whole.Q34.l2Norm_eq (hG n).coeFn_toLp.symm
    have e2 := HRS.Whole.Q34.l2Norm_eq hg.coeFn_toLp.symm
    have e3 := HRS.Whole.Q34.l2Norm_eq ((hG n).sub hg).coeFn_toLp.symm
    rw [e1, e2, e3, MemLp.toLp_sub]
    exact abs_norm_sub_norm_le _ _
  have hr : Tendsto (fun n => HRS.Whole.l2Norm μ (G n)) atTop
      (𝓝 (HRS.Whole.l2Norm μ g)) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    have hs := tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds he
      (fun n => abs_nonneg (HRS.Whole.l2Norm μ (G n) - HRS.Whole.l2Norm μ g)) htri
    simpa only [Real.norm_eq_abs] using hs
  have hp := hr.pow 2
  simpa only [HRS.Whole.l2Norm, Real.sq_sqrt (integral_nonneg fun x => sq_nonneg (G _ x)),
    Real.sq_sqrt (integral_nonneg fun x => sq_nonneg (g x))] using hp

/-- The centered initial-value energy is continuous under G4-cost convergence. -/
theorem fp81s21_g4_initial_continuous (p : Parameters) :
    fp81s21_g4Phys p (fun _ R =>
      ∀ f : Euc p.d → ℝ, IsOscTest (wholeSpaceIndex p.d : ℝ) f →
      ∀ F : ℕ → Euc p.d → ℝ,
        (∀ n, IsOscTest (wholeSpaceIndex p.d : ℝ) (F n)) →
        Tendsto (fun n => fp81s21_g4_J p.d (F n - f)) atTop (𝓝 0) →
      ∀ v w : ℝ, 0 ≤ v → v ≤ w →
        Tendsto (fun n => fp81s21_g4_initialValue R (F n) v w) atTop
          (𝓝 (fp81s21_g4_initialValue R f v w))) := by
  obtain ⟨δs, hs, hhalf, hstab⟩ := fp81s21_g4_propagator_stability p
  obtain ⟨δe, he, _, herr⟩ := fp81s21_g4_piece_errors_tendsto p
  refine ⟨min δs δe, lt_min hs he, (min_le_left _ _).trans hhalf, ?_⟩
  intro δ hδ hδle R
  obtain ⟨B, hB, hbudget⟩ := hstab δ hδ (hδle.trans (min_le_left _ _)) R
  have herrR := herr δ hδ (hδle.trans (min_le_right _ _)) R
  intro f hf F hF hconv v w hv hvw
  let μ := HRS.Whole.withDensityReal R.ρβ
  letI : IsProbabilityMeasure μ := HRS.Whole.Q34.isProbabilityMeasure_nu R.thermal.1.1
  let raw : (Euc p.d → ℝ) → Euc p.d → ℝ := fun g x =>
    r26t3_U R 0 w g x - r26t3_U R 0 v g x
  let field : (Euc p.d → ℝ) → Euc p.d → ℝ := fun g => HRS.Whole.projMean μ (raw g)
  have hraw (g : Euc p.d → ℝ) (hg : IsOscTest (wholeSpaceIndex p.d : ℝ) g) :
      MemLp (raw g) 2 μ := by
    exact ((hbudget g hg w (hv.trans hvw)).2.2.2 0 ⟨le_rfl, hv.trans hvw⟩).1.sub
      (((hbudget g hg v hv).2.2.2 0 ⟨le_rfl, hv⟩).1)
  have hfield (g : Euc p.d → ℝ) (hg : IsOscTest (wholeSpaceIndex p.d : ℝ) g) :
      MemLp (field g) 2 μ := (hraw g hg).sub (memLp_const _)
  have hproj (a b : Euc p.d → ℝ) (ha : MemLp a 2 μ) (hb : MemLp b 2 μ) :
      HRS.Whole.projMean μ (a - b) = HRS.Whole.projMean μ a - HRS.Whole.projMean μ b := by
    funext x
    simp only [HRS.Whole.projMean, HRS.Whole.pair, Pi.sub_apply,
      integral_sub (ha.integrable one_le_two) (hb.integrable one_le_two)]
    ring
  have hsub (n : ℕ) : field (F n - f) = field (F n) - field f := by
    have hw := fp81s21_g4_U_sub p R (hF n) hf (hv.trans hvw) ⟨le_rfl, hv.trans hvw⟩
    have hv' := fp81s21_g4_U_sub p R (hF n) hf hv ⟨le_rfl, hv⟩
    have heq : raw (F n - f) = raw (F n) - raw f := by
      dsimp [raw]
      rw [hw, hv']
      funext x
      simp only [Pi.sub_apply]
      ring
    dsimp [field]
    rw [heq]
    exact hproj (raw (F n)) (raw f) (hraw (F n) (hF n)) (hraw f hf)
  let A : ℕ → Euc p.d → ℝ := fun n => field (F n)
  let a : Euc p.d → ℝ := field f
  have ha : MemLp a 2 μ := hfield f hf
  have hA (n : ℕ) : MemLp (A n) 2 μ := hfield (F n) (hF n)
  have hdiff (n : ℕ) : (∫ x, (A n x - a x)^2 ∂μ) =
      fp81s21_g4_initialValue R (F n - f) v w := by
    change (∫ x, ((A n - a) x)^2 ∂μ) = _
    rw [← hsub n]
    rfl
  have herror : Tendsto (fun n => ∫ x, (A n x - a x)^2 ∂μ) atTop (𝓝 0) := by
    simpa only [hdiff] using (herrR f hf F hF hconv v w hv hvw).1
  have hlim := fp81s21_g4_real_l2_energy_continuous a A ha hA herror
  exact hlim

/-- The G4 cost and all three propagated pieces are continuous under
convergence of the oscillator-test difference in G4 cost. -/
theorem fp81s21_g4_pieces_continuous (p : Parameters) :
    fp81s21_g4Phys p (fun _ R =>
      ∀ f : Euc p.d → ℝ,
        IsOscTest (wholeSpaceIndex p.d : ℝ) f →
      ∀ F : ℕ → Euc p.d → ℝ,
        (∀ n, IsOscTest (wholeSpaceIndex p.d : ℝ) (F n)) →
        Tendsto (fun n => fp81s21_g4_J p.d (F n - f)) atTop (𝓝 0) →
      ∀ v w : ℝ, 0 ≤ v → v ≤ w →
        Tendsto (fun n => fp81s21_g4_J p.d (F n))
          atTop (𝓝 (fp81s21_g4_J p.d f)) ∧
        Tendsto (fun n => fp81s21_g4_initialValue R (F n - f) v w) atTop (𝓝 0) ∧
        Tendsto (fun n => fp81s21_g4_Old R (F n - f) v w) atTop (𝓝 0) ∧
        Tendsto (fun n => fp81s21_g4_New R (F n - f) v w) atTop (𝓝 0) ∧
        Tendsto (fun n => fp81s21_g4_initialValue R (F n) v w)
          atTop (𝓝 (fp81s21_g4_initialValue R f v w)) ∧
        Tendsto (fun n => fp81s21_g4_Old R (F n) v w)
          atTop (𝓝 (fp81s21_g4_Old R f v w)) ∧
        Tendsto (fun n => fp81s21_g4_New R (F n) v w)
          atTop (𝓝 (fp81s21_g4_New R f v w))) := by
  obtain ⟨δi, hi, hihalf, hini⟩ := fp81s21_g4_initial_continuous p
  obtain ⟨δo, ho, _, hold⟩ := fp81s21_g4_old_continuous p
  obtain ⟨δn, hn, _, hnew⟩ := fp81s21_g4_new_continuous p
  obtain ⟨δe, he, _, herr⟩ := fp81s21_g4_piece_errors_tendsto p
  refine ⟨min δi (min δo (min δn δe)), lt_min hi (lt_min ho (lt_min hn he)),
    (min_le_left _ _).trans hihalf, ?_⟩
  intro δ hδ hδle R
  have hδi : δ ≤ δi := hδle.trans (min_le_left _ _)
  have hδo : δ ≤ δo := hδle.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδn : δ ≤ δn := hδle.trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hδe : δ ≤ δe := hδle.trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  intro f hf F hF hconv v w hv hvw
  have herrors := herr δ hδ hδe R f hf F hF hconv v w hv hvw
  exact ⟨fp81s21_g4_osc_cost_continuous f F hf hF hconv,
    herrors.1, herrors.2.1, herrors.2.2,
    hini δ hδ hδi R f hf F hF hconv v w hv hvw,
    hold δ hδ hδo R f hf F hF hconv v w hv hvw,
    hnew δ hδ hδn R f hf F hF hconv v w hv hvw⟩

/-- The finite-combination G4 reference bounds extend to compact tests. -/
theorem fp81s21_g4_compact_reference_pieces (p : Parameters) :
    fp81s21_g4Phys p (fun _ R =>
      ∃ A : ℝ, 0 ≤ A ∧
        ∀ f, IsR2Test f →
          ∀ v w : ℝ, 0 ≤ v → v ≤ w →
            fp81s21_g4_initialValue R f v w ≤
              A * (w-v)^2 * fp81s21_g4_J p.d f ∧
            fp81s21_g4_Old R f v w ≤
              A * (w-v)^2 * fp81s21_g4_J p.d f ∧
            fp81s21_g4_New R f v w ≤
              A * ((w-v)+(w-v)^2) * fp81s21_g4_J p.d f) := by
  apply fp81s21_g4_compact_reference_pieces_of_continuity p
  obtain ⟨δ0, hδ0, hhalf, hcont⟩ := fp81s21_g4_pieces_continuous p
  refine ⟨δ0, hδ0, hhalf, ?_⟩
  intro δ hδ hδle R f hf v w hv hvw
  have h := hcont δ hδ hδle R f
    (r2Test_isOscTest (wholeSpaceIndex p.d : ℝ) hf)
    (fun n => k4hs (wholeSpaceIndex p.d : ℝ) n f)
    (fun n => k4hs_osc (wholeSpaceIndex p.d : ℝ) n f)
    (fp81s21_g4_cost_approx p hf) v w hv hvw
  exact ⟨h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩

#print axioms fp81s21_g4_pieces_continuous
#print axioms fp81s21_g4_compact_reference_pieces
#print axioms fp81s21_g4_real_l2_energy_continuous
#print axioms fp81s21_g4_initial_continuous
#print axioms fp81s21_g4_old_continuous
#print axioms fp81s21_g4_new_continuous
#print axioms fp81s21_g4_U_sub
#print axioms fp81s21_g4_gradient_U_sub
#print axioms fp81s21_g4_l2_energy_continuous
#print axioms fp81s21_g4_new_stability
#print axioms fp81s21_g4_initial_stability
#print axioms fp81s21_g4_old_stability
#print axioms fp81s21_g4_piece_errors_tendsto
end HRS.Fp81.S21
end
