import HRS.MS.Fp81S21GaussG4U85

/-! Pointwise normalization on the old and new noise-time regions. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3

/-- On the old time region the kernel difference is the weighted gradient
    difference; on the new region only the later kernel remains. -/
theorem fp81s21_g4_noise_kernel_regions
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    {f : Euc p.d → ℝ} {v w : ℝ} (hv : 0 ≤ v) (hvw : v ≤ w) :
    (∀ r ∈ Icc (0 : ℝ) v, ∀ x,
      ‖movingNoiseKernel R 0 w f (r,x) - movingNoiseKernel R 0 v f (r,x)‖^2 =
        2 * p.β⁻¹ * (‖gradient (r26t3_U R r w f) x -
          gradient (r26t3_U R r v f) x‖^2 * R.ρ r x)) ∧
    (∀ r ∈ Ioc v w, ∀ x,
      ‖movingNoiseKernel R 0 w f (r,x) - movingNoiseKernel R 0 v f (r,x)‖^2 =
        2 * p.β⁻¹ * (‖gradient (r26t3_U R r w f) x‖^2 * R.ρ r x)) ∧
    (∀ r ∉ Icc (0 : ℝ) w, ∀ x,
      movingNoiseKernel R 0 w f (r,x) - movingNoiseKernel R 0 v f (r,x) = 0) := by
  have hρ : ∀ r ∈ Icc (0 : ℝ) w, ∀ x, 0 ≤ R.ρ r x := by
    intro r hr x
    have hT : 0 < w + 1 := by linarith
    exact ((R.resulting.global (w + 1)).density r
      ⟨hr.1, by linarith [hr.2]⟩).nonneg x
  have hsq : ∀ r ∈ Icc (0 : ℝ) w, ∀ x (a : Euc p.d),
      ‖(Real.sqrt (2 * p.β⁻¹) * Real.sqrt (R.ρ r x)) • a‖^2 =
        2 * p.β⁻¹ * (‖a‖^2 * R.ρ r x) := by
    intro r hr x a
    rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, mul_pow,
      Real.sq_sqrt (mul_nonneg (by norm_num) (inv_nonneg.mpr p.hβ.le)),
      Real.sq_sqrt (hρ r hr x)]
    ring
  refine ⟨?_, ?_, ?_⟩
  · intro r hr x
    have hrw : r ∈ Icc (0 : ℝ) w := ⟨hr.1, hr.2.trans hvw⟩
    simp only [movingNoiseKernel, if_pos hrw, if_pos hr]
    rw [← smul_sub]
    exact hsq r hrw x _
  · intro r hr x
    have hrw : r ∈ Icc (0 : ℝ) w := ⟨hv.trans hr.1.le, hr.2⟩
    have hrv : r ∉ Icc (0 : ℝ) v := fun h => (not_lt_of_ge h.2) hr.1
    simp only [movingNoiseKernel, if_pos hrw, if_neg hrv, sub_zero]
    exact hsq r hrw x _
  · intro r hr x
    have hrv : r ∉ Icc (0 : ℝ) v := fun h => hr ⟨h.1, h.2.trans hvw⟩
    simp [movingNoiseKernel, hr, hrv]

/-- The raw squared kernel difference is integrable on time-space. -/
theorem fp81s21_g4_noise_kernel_difference_integrable
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2)
    {f : Euc p.d → ℝ} (hf : IsOscTest (wholeSpaceIndex p.d : ℝ) f)
    {v w : ℝ} (hv : 0 ≤ v) (hvw : v ≤ w) :
    Integrable (fun q =>
      ‖movingNoiseKernel R 0 w f q - movingNoiseKernel R 0 v f q‖^2)
      ((volume : Measure ℝ).prod (volume : Measure (Euc p.d))) := by
  have hT : 0 < w + 1 := by linarith
  have hvT : v ∈ Icc (0 : ℝ) (w + 1) := ⟨hv, by linarith⟩
  have hwT : w ∈ Icc (0 : ℝ) (w + 1) := ⟨hv.trans hvw, by linarith⟩
  have hmemW := (movingNoiseFeature_spec p R hδ hδhalf hT).1 0
    ⟨le_rfl, hT.le⟩ w hwT f hf
  have hmemV := (movingNoiseFeature_spec p R hδ hδhalf hT).1 0
    ⟨le_rfl, hT.le⟩ v hvT f hf
  exact (hmemW.sub hmemV).integrable_norm_pow (by norm_num)

/-- Integrating the density comparison over a nonnegative time interval. -/
theorem fp81s21_g4_density_time_integral_le
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2) {a b : ℝ} (ha : 0 ≤ a)
    {g : ℝ → Euc p.d → ℝ} (hg0 : ∀ r x, 0 ≤ g r x)
    (hgref : ∀ᵐ r ∂(volume.restrict (Icc a b)), Integrable (g r) (fp81s21_g4_mu R))
    (hmove : IntegrableOn (fun r => ∫ x, g r x ∂r26t3_mu R r) (Icc a b))
    (hfixed : IntegrableOn (fun r => ∫ x, g r x ∂fp81s21_g4_mu R) (Icc a b)) :
    (∫ r in Icc a b, ∫ x, g r x ∂r26t3_mu R r) ≤
      p.C₁ * ∫ r in Icc a b, ∫ x, g r x ∂fp81s21_g4_mu R := by
  rw [← integral_const_mul]
  apply integral_mono_ae hmove (hfixed.const_mul p.C₁)
  filter_upwards [ae_restrict_mem measurableSet_Icc, hgref] with r hr hgr
  exact fp81s21_g4_density_integral_le p R hδ hδhalf (ha.trans hr.1) hgr (hg0 r)

/-- Each propagated gradient is square-integrable under the reference measure. -/
theorem fp81s21_g4_gradient_reference_memLp
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    {f : Euc p.d → ℝ} (hf : IsOscTest (wholeSpaceIndex p.d : ℝ) f)
    {r T : ℝ} (hr : 0 ≤ r) (hrT : r ≤ T) :
    MemLp (gradient (r26t3_U R r T f)) 2 (fp81s21_g4_mu R) := by
  have hT : 0 ≤ T := hr.trans hrT
  have hu := fp81s21_U_osc_test_classical p R hf hT
  obtain ⟨B, hB, hb⟩ := HRS.MS.S111X1.x1_fderiv_bdd hu
  letI : IsProbabilityMeasure (fp81s21_g4_mu R) :=
    HRS.Whole.Q34.isProbabilityMeasure_nu R.thermal.1.1
  have hc := HRS.MS.S111X2.s111x2_gradient_continuous
    ((hu.c2 r ⟨hr, hrT⟩).of_le (by norm_num))
  exact (MemLp.of_bound hc.aestronglyMeasurable B
    (Eventually.of_forall (hb r ⟨hr, hrT⟩))).mono_exponent le_top

/-- Exact old/new decomposition under the moving density. -/
theorem fp81s21_g4_noise_increment_moving
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2)
    {f : Euc p.d → ℝ} (hf : IsOscTest (wholeSpaceIndex p.d : ℝ) f)
    {v w : ℝ} (hv : 0 ≤ v) (hvw : v ≤ w) :
    ‖movingNoiseFeature R 0 w f - movingNoiseFeature R 0 v f‖^2 =
      2 * p.β⁻¹ *
        ((∫ r in Icc (0 : ℝ) v, ∫ x,
          ‖gradient (r26t3_U R r w f) x - gradient (r26t3_U R r v f) x‖^2
            ∂r26t3_mu R r) +
         (∫ r in Icc v w, ∫ x,
          ‖gradient (r26t3_U R r w f) x‖^2 ∂r26t3_mu R r)) := by
  let F : ℝ × Euc p.d → ℝ := fun q =>
    ‖movingNoiseKernel R 0 w f q - movingNoiseKernel R 0 v f q‖^2
  let G : ℝ → ℝ := fun r => ∫ x, F (r, x)
  let A : ℝ → ℝ := fun r => ∫ x,
    ‖gradient (r26t3_U R r w f) x - gradient (r26t3_U R r v f) x‖^2
      ∂r26t3_mu R r
  let B : ℝ → ℝ := fun r => ∫ x,
    ‖gradient (r26t3_U R r w f) x‖^2 ∂r26t3_mu R r
  let c : ℝ := 2 * p.β⁻¹
  have hF : Integrable F ((volume : Measure ℝ).prod (volume : Measure (Euc p.d))) :=
    fp81s21_g4_noise_kernel_difference_integrable p R hδ hδhalf hf hv hvw
  have hG : Integrable G := hF.integral_prod_left
  have hreg := fp81s21_g4_noise_kernel_regions p R hv hvw (f := f)
  have hrow (r : ℝ) (hr : 0 ≤ r) (g : Euc p.d → ℝ) :
      (∫ x, g x * R.ρ r x) = ∫ x, g x ∂r26t3_mu R r := by
    have hρm : Measurable (R.ρ r) := (R.resulting.regular r hr).measurable
    have hρ0 : ∀ x, 0 ≤ R.ρ r x := by
      intro x
      have hT : 0 < r + 1 := by linarith
      exact ((R.resulting.global (r + 1)).density r ⟨hr, by linarith⟩).nonneg x
    have hh := HRS.MP.RdRem.mrr_integral_withDensityReal (R.ρ r) hρm hρ0 g
    change (∫ x, g x * R.ρ r x) = ∫ x, g x ∂HRS.Whole.withDensityReal (R.ρ r)
    rw [hh]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => mul_comm _ _
  have hA : ∀ r ∈ Icc (0 : ℝ) v, G r = c * A r := by
    intro r hr
    dsimp [G, F, c, A]
    calc
      _ = ∫ x, (2 * p.β⁻¹) *
          (‖gradient (r26t3_U R r w f) x - gradient (r26t3_U R r v f) x‖^2 * R.ρ r x) := by
            apply integral_congr_ae
            exact Eventually.of_forall (hreg.1 r hr)
      _ = _ := by rw [integral_const_mul, hrow r hr.1]
  have hB : ∀ r ∈ Ioc v w, G r = c * B r := by
    intro r hr
    dsimp [G, F, c, B]
    calc
      _ = ∫ x, (2 * p.β⁻¹) *
          (‖gradient (r26t3_U R r w f) x‖^2 * R.ρ r x) := by
            apply integral_congr_ae
            exact Eventually.of_forall (hreg.2.1 r hr)
      _ = _ := by rw [integral_const_mul, hrow r (hv.trans hr.1.le)]
  have hsupport : (∫ r, G r) = ∫ r in Icc (0 : ℝ) w, G r := by
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro r hr
    dsimp [G, F]
    simp [hreg.2.2 r hr]
  have hdisj : Disjoint (Icc (0 : ℝ) v) (Ioc v w) := by
    rw [Set.disjoint_left]
    intro r h1 h2
    exact (not_lt_of_ge h1.2) h2.1
  have hsplit : (∫ r in Icc (0 : ℝ) w, G r) =
      (∫ r in Icc (0 : ℝ) v, G r) + ∫ r in Ioc v w, G r := by
    rw [← Set.Icc_union_Ioc_eq_Icc hv hvw]
    exact setIntegral_union hdisj measurableSet_Ioc hG.integrableOn hG.integrableOn
  calc
    _ = ∫ q, F q := fp81s21_g4_noise_increment_kernel p R hδ hδhalf hf hv hvw
    _ = ∫ r, G r := integral_prod _ hF
    _ = _ := by
      rw [hsupport, hsplit]
      have ha : (∫ r in Icc (0 : ℝ) v, G r) = ∫ r in Icc (0 : ℝ) v, c * A r :=
        setIntegral_congr_fun measurableSet_Icc hA
      have hb : (∫ r in Ioc v w, G r) = ∫ r in Ioc v w, c * B r :=
        setIntegral_congr_fun measurableSet_Ioc hB
      rw [ha, hb, integral_const_mul, integral_const_mul,
        ← integral_Icc_eq_integral_Ioc]
      dsimp [c, A, B]
      ring

#print axioms fp81s21_g4_noise_increment_moving
#print axioms fp81s21_g4_gradient_reference_memLp
#print axioms fp81s21_g4_noise_kernel_regions
#print axioms fp81s21_g4_noise_kernel_difference_integrable
#print axioms fp81s21_g4_density_time_integral_le
end HRS.Fp81.S21
end
