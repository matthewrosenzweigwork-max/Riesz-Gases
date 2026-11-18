import HRS.PDE.MovSpec1

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS

variable {d N : ℕ}

theorem movc_riesz_lower {s : ℝ} (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ z : Torus d, -B ≤ periodicRiesz d s z := by
  have : ∃ B : ℝ, ∀ z : Torus d, -B ≤ periodicRiesz d s z := by
    rcases hd.eq_or_lt with h | h
    · subst h
      exact b15_periodicRiesz_ge_d1 hs0 (by simpa using hsd)
    · exact periodicRiesz_ge (by omega) hs0 hsd
  obtain ⟨B, hB⟩ := this
  exact ⟨max B 0, le_max_right _ _, fun z => (neg_le_neg (le_max_left _ _)).trans (hB z)⟩

theorem movc_gReg_measurable {s : ℝ} (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (M : ℝ) :
    Continuous (b15c_gReg d s M) :=
  b15c_isSmooth_continuous (b15c_gReg_isSmooth hd hs0 hsd M)

theorem movc_gReg_L1_tendsto (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {M : ℕ → ℝ}
    (hM : Tendsto M atTop atTop) (hM0 : ∀ n, 0 ≤ M n) :
    Tendsto (fun n => ∫ z : Torus d, |periodicRiesz d s z - b15c_gReg d s (M n) z|) atTop (𝓝 0) := by
  obtain ⟨B, hB0, hB⟩ := movc_riesz_lower hd hs0 hsd
  have hgi : Integrable (periodicRiesz d s) := CoercAux.integrable_periodicRiesz_one hd hs0 hsd
  have hmeas : ∀ n, AEStronglyMeasurable
      (fun z : Torus d => |periodicRiesz d s z - b15c_gReg d s (M n) z|) volume := fun n =>
    ((hgi.aestronglyMeasurable).sub
      (movc_gReg_measurable hd hs0 hsd (M n)).aestronglyMeasurable).norm
  have hbound : Integrable (fun z : Torus d => |periodicRiesz d s z| + B) volume :=
    hgi.abs.add (integrable_const B)
  have := tendsto_integral_of_dominated_convergence (μ := (volume : Measure (Torus d)))
    (F := fun n z => |periodicRiesz d s z - b15c_gReg d s (M n) z|) (f := fun _ => (0 : ℝ))
    (fun z => |periodicRiesz d s z| + B) hmeas hbound ?_ ?_
  · simpa using this
  · intro n
    have h0 : (volume : Measure (Torus d)) {0} = 0 := volume_singleton_torus hd 0
    have : ∀ᵐ z : Torus d ∂volume, z ≠ 0 := by
      rw [ae_iff]; simpa using h0
    filter_upwards [this] with z hz
    have h1 := b15c_gReg_le s (M n) hz
    have h2 := b15c_gReg_ge s hB0 (hM0 n) hB z
    rw [Real.norm_eq_abs, abs_abs, abs_le]
    constructor
    · linarith [abs_nonneg (periodicRiesz d s z)]
    · have := le_abs_self (periodicRiesz d s z); linarith
  · have h0 : (volume : Measure (Torus d)) {0} = 0 := volume_singleton_torus hd 0
    have : ∀ᵐ z : Torus d ∂volume, z ≠ 0 := by
      rw [ae_iff]; simpa using h0
    filter_upwards [this] with z hz
    have hev := (hM.eventually (b15c_gReg_eventuallyEq (d := d) s hz))
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hev] with n hn
    simp [hn]


theorem movc_convFun_diff_le (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (M : ℝ)
    {f : Torus d → ℝ} (hf : Continuous f) {C : ℝ} (hC : ∀ x, |f x| ≤ C) (x : Torus d) :
    |convFun (periodicRiesz d s) f x - convFun (b15c_gReg d s M) f x| ≤
      C * ∫ z : Torus d, |periodicRiesz d s z - b15c_gReg d s M z| := by
  have hgi : Integrable (periodicRiesz d s) := CoercAux.integrable_periodicRiesz_one hd hs0 hsd
  have hgc := movc_gReg_measurable hd hs0 hsd M
  have hfb : ∀ y, |f y| ≤ C := hC
  have hgM : Integrable (b15c_gReg d s M) := hgc.integrable_of_hasCompactSupport (by
    exact HasCompactSupport.of_compactSpace _)
  have hi1 : Integrable (fun y => periodicRiesz d s (x - y) * f y) := by
    refine Integrable.mul_bdd (c := C) ?_ hf.aestronglyMeasurable ?_
    · exact (hgi.comp_sub_left x)
    · exact Filter.Eventually.of_forall (fun y => by simpa using hC y)
  have hi2 : Integrable (fun y => b15c_gReg d s M (x - y) * f y) := by
    refine Integrable.mul_bdd (c := C) ?_ hf.aestronglyMeasurable ?_
    · exact (hgM.comp_sub_left x)
    · exact Filter.Eventually.of_forall (fun y => by simpa using hC y)
  have hdiff : Integrable (fun z : Torus d => |periodicRiesz d s z - b15c_gReg d s M z|) :=
    (hgi.sub hgM).abs
  unfold convFun
  rw [← integral_sub hi1 hi2]
  have hshift : ∫ y : Torus d, |periodicRiesz d s (x - y) - b15c_gReg d s M (x - y)| =
      ∫ z : Torus d, |periodicRiesz d s z - b15c_gReg d s M z| :=
    integral_sub_left_eq_self (fun z : Torus d => |periodicRiesz d s z - b15c_gReg d s M z|)
      volume x
  rw [← hshift, ← integral_const_mul]
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0)
  have h1 : |∫ y : Torus d, (periodicRiesz d s (x - y) * f y - b15c_gReg d s M (x - y) * f y)| ≤
      ∫ y : Torus d, |periodicRiesz d s (x - y) * f y - b15c_gReg d s M (x - y) * f y| := by
    have := norm_integral_le_integral_norm (μ := (volume : Measure (Torus d)))
      (fun y : Torus d => periodicRiesz d s (x - y) * f y - b15c_gReg d s M (x - y) * f y)
    simpa [Real.norm_eq_abs] using this
  refine h1.trans ?_
  refine integral_mono_of_nonneg (Eventually.of_forall fun y => abs_nonneg _) ?_
    (Eventually.of_forall fun y => ?_)
  · exact (hdiff.comp_sub_left x).const_mul C
  · beta_reduce
    rw [← sub_mul, abs_mul]
    calc _ ≤ |periodicRiesz d s (x - y) - b15c_gReg d s M (x - y)| * C :=
          mul_le_mul_of_nonneg_left (hC y) (abs_nonneg _)
      _ = _ := mul_comm _ _

theorem movc_convFun_tendstoUniformly (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d)
    {M : ℕ → ℝ} (hM : Tendsto M atTop atTop) (hM0 : ∀ n, 0 ≤ M n) {f : Torus d → ℝ}
    (hf : Continuous f) :
    TendstoUniformly (fun n x => convFun (b15c_gReg d s (M n)) f x) (convFun (periodicRiesz d s) f)
      atTop := by
  obtain ⟨C, hC0, hC⟩ := exists_abs_bound hf
  have hT := movc_gReg_L1_tendsto hd hs0 hsd hM hM0
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  have hT' := (hT.const_mul (C + 1))
  rw [mul_zero] at hT'
  filter_upwards [hT'.eventually (gt_mem_nhds hε)] with n hn x
  rw [Real.dist_eq]
  refine lt_of_le_of_lt ?_ hn
  have := movc_convFun_diff_le hd hs0 hsd (M n) hf hC x
  refine this.trans ?_
  have hI : 0 ≤ ∫ z : Torus d, |periodicRiesz d s z - b15c_gReg d s (M n) z| :=
    integral_nonneg (fun z => abs_nonneg _)
  exact mul_le_mul_of_nonneg_right (by linarith) hI

end HRS
