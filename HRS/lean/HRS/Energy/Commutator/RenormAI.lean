import HRS.Energy.Commutator.RoughMain
import HRS.Energy.Commutator.RenormSlice

/-!
# Route S, packet S4: `L¹` approximate identity for the heat kernel `hk_ε` on `T^d`
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators
open HRS HRS.KernelAux HRS.Commutator.FourierAux HRS.Commutator.RoughAux HRS.Commutator.RoughHeat

namespace HRS.Commutator.Renorm

variable {d : ℕ}

/-- Heat mollification `hk_ε ⋆ f`. -/
def cv (ε : ℝ) (f : Torus d → ℝ) (x : Torus d) : ℝ := ∫ y, hk ε (x - y) * f y

theorem integral_hk_sub (ε : ℝ) (hε : 0 < ε) (x : Torus d) : ∫ y, hk ε (x - y) = 1 := by
  rw [integral_sub_left_eq_self (fun z => hk ε z) volume x]
  exact integral_hk hε

theorem integrable_hk_sub (ε : ℝ) (hε : 0 < ε) (x : Torus d) : Integrable (fun y => hk ε (x - y)) volume :=
  (integrable_hk hε).comp_sub_left x

/-- uniform convergence of the mollification for continuous functions -/
theorem cv_tendsto_cont {g : Torus d → ℝ} (hg : Continuous g) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ x, |cv ε g x - g x| ≤ η := by
  obtain ⟨B, hB⟩ : ∃ B : ℝ, ∀ x, |g x| ≤ B := by
    obtain ⟨B, hB⟩ := isCompact_univ.exists_bound_of_continuousOn hg.continuousOn
    exact ⟨B, fun x => by simpa using hB x (mem_univ x)⟩
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  have hucont : UniformContinuous g := CompactSpace.uniformContinuous_of_continuous hg
  obtain ⟨r, hr, hrg⟩ := Metric.uniformContinuous_iff.mp hucont (η / 2) (by positivity)
  obtain ⟨C, hC0, hC⟩ := hk_tail d (d + 1) hr
  -- smallness of the tail
  have hsmall : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 2 * B * (C * ε ^ ((((d + 1 : ℕ) : ℝ) - d) / 2)) ≤ η / 2 := by
    have h := tendsto_rpow_nhdsGT_zero (p := (((d + 1 : ℕ) : ℝ) - d) / 2) (by push_cast; linarith)
    have h2 : Tendsto (fun ε : ℝ => 2 * B * (C * ε ^ ((((d + 1 : ℕ) : ℝ) - d) / 2))) (𝓝[>] (0 : ℝ)) (𝓝 (2 * B * (C * 0))) :=
      (h.const_mul C).const_mul (2 * B)
    rw [mul_zero, mul_zero] at h2
    exact h2.eventually (ge_mem_nhds (by positivity))
  have hε1 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 2 ^ (d + 1) * (4 * Real.pi ^ 2 * ε) ≤ 1 := by
    have : Tendsto (fun ε : ℝ => 2 ^ (d + 1) * (4 * Real.pi ^ 2 * ε)) (𝓝[>] (0 : ℝ)) (𝓝 (2 ^ (d + 1) * (4 * Real.pi ^ 2 * 0))) :=
      (((continuous_id.const_mul _).const_mul _).tendsto 0).mono_left nhdsWithin_le_nhds
    rw [mul_zero, mul_zero] at this
    exact this.eventually (ge_mem_nhds one_pos)
  filter_upwards [hsmall, hε1, self_mem_nhdsWithin] with ε hs h1 hεpos
  have hεpos' : 0 < ε := hεpos
  intro x
  have hkint := integrable_hk_sub ε hεpos' x
  have hgint : Integrable g (volume : Measure (Torus d)) := hg.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hcv : cv ε g x - g x = ∫ y, hk ε (x - y) * (g y - g x) := by
    unfold cv
    have : ∀ y, hk ε (x - y) * (g y - g x) = hk ε (x - y) * g y - hk ε (x - y) * g x := fun y => by ring
    simp_rw [this]
    rw [integral_sub, integral_mul_const, integral_hk_sub ε hεpos' x, one_mul]
    · -- integrability of the first term
      exact (hkint.mul_bdd (c := B) hg.aestronglyMeasurable (Filter.Eventually.of_forall fun y => by simpa using hB y)).congr
        (Filter.Eventually.of_forall fun y => by simp [mul_comm])
    · exact hkint.mul_const _
  rw [hcv]
  have hpt : ∀ y, |hk ε (x - y) * (g y - g x)| ≤ (η / 2) * hk ε (x - y) + 2 * B * (C * ε ^ ((((d + 1 : ℕ) : ℝ) - d) / 2)) := by
    intro y
    have hk0 := hk_nonneg hεpos' (x - y)
    rw [abs_mul, abs_of_nonneg hk0]
    by_cases hy : r ≤ KernelGrad.tdist (x - y) 0
    · have h1' := hC ε hεpos' h1 (x - y) hy
      have h2 : |g y - g x| ≤ 2 * B := by
        have := abs_sub (g y) (g x)
        linarith [hB y, hB x]
      calc hk ε (x - y) * |g y - g x| ≤ (C * ε ^ ((((d + 1 : ℕ) : ℝ) - d) / 2)) * (2 * B) :=
            mul_le_mul h1' h2 (abs_nonneg _) (by positivity)
        _ = 2 * B * (C * ε ^ ((((d + 1 : ℕ) : ℝ) - d) / 2)) := by ring
        _ ≤ _ := by linarith [mul_nonneg (by positivity : (0:ℝ) ≤ η / 2) hk0]
    · push Not at hy
      have hd' : dist y x < r := by
        have := RoughMain.dist_le_tdist y x
        have e : KernelGrad.tdist y x = KernelGrad.tdist (x - y) 0 := by
          rw [tdist_symm' y x, EnergyAux.tdist_def]
        linarith
      have := hrg hd'
      rw [Real.dist_eq] at this
      calc hk ε (x - y) * |g y - g x| ≤ hk ε (x - y) * (η / 2) := mul_le_mul_of_nonneg_left this.le hk0
        _ = (η / 2) * hk ε (x - y) := by ring
        _ ≤ _ := by linarith [mul_nonneg (by linarith : (0:ℝ) ≤ 2 * B) (mul_nonneg hC0 (Real.rpow_nonneg hεpos'.le (((((d + 1 : ℕ) : ℝ) - d) / 2))))]
  have hint1 : Integrable (fun y => hk ε (x - y) * (g y - g x)) volume := by
    refine (hkint.mul_bdd (c := 2 * B) (hg.sub continuous_const).aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => ?_))
    rw [Real.norm_eq_abs]
    have := abs_sub (g y) (g x)
    linarith [hB y, hB x]
  calc |∫ y, hk ε (x - y) * (g y - g x)| ≤ ∫ y, |hk ε (x - y) * (g y - g x)| := by
        simpa using norm_integral_le_integral_norm (fun y => hk ε (x - y) * (g y - g x))
    _ ≤ ∫ y, ((η / 2) * hk ε (x - y) + 2 * B * (C * ε ^ ((((d + 1 : ℕ) : ℝ) - d) / 2))) :=
        integral_mono hint1.abs ((hkint.const_mul _).add (integrable_const _)) hpt
    _ = η / 2 + 2 * B * (C * ε ^ ((((d + 1 : ℕ) : ℝ) - d) / 2)) := by
        rw [integral_add (hkint.const_mul _) (integrable_const _), integral_const_mul,
          integral_hk_sub ε hεpos' x]
        simp
    _ ≤ η := by linarith


theorem integrable_cv_prod {h : Torus d → ℝ} (hhm : Measurable h) (hh : Integrable h volume) {ε : ℝ} (hε : 0 < ε) :
    Integrable (fun p : Torus d × Torus d => hk ε (p.1 - p.2) * h p.2)
      ((volume : Measure (Torus d)).prod volume) := by
  obtain ⟨M, hM⟩ := hk_bdd hε
  have hm : Measurable fun p : Torus d × Torus d => hk ε (p.1 - p.2) * h p.2 :=
    ((continuous_hk hε).measurable.comp (measurable_fst.sub measurable_snd)).mul (hhm.comp measurable_snd)
  refine Integrable.mono' ((hh.norm.comp_snd (μ := (volume : Measure (Torus d)))).const_mul M)
    hm.aestronglyMeasurable (Filter.Eventually.of_forall fun p => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hk_nonneg hε _)]
  exact mul_le_mul_of_nonneg_right (hM _) (abs_nonneg _)

theorem integral_abs_cv_le {h : Torus d → ℝ} (hhm : Measurable h) (hh : Integrable h volume) {ε : ℝ} (hε : 0 < ε) :
    ∫ x, |cv ε h x| ≤ ∫ y, |h y| := by
  have hint := integrable_cv_prod hhm hh hε
  have hint' : Integrable (fun p : Torus d × Torus d => hk ε (p.1 - p.2) * |h p.2|)
      ((volume : Measure (Torus d)).prod volume) := by
    refine hint.abs.congr (Filter.Eventually.of_forall fun p => ?_)
    simp only [abs_mul, abs_of_nonneg (hk_nonneg hε _)]
  calc ∫ x, |cv ε h x| ≤ ∫ x, ∫ y, hk ε (x - y) * |h y| := by
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => abs_nonneg _)
          hint'.integral_prod_left (Filter.Eventually.of_forall fun x => ?_)
        unfold cv
        calc |∫ y, hk ε (x - y) * h y| ≤ ∫ y, |hk ε (x - y) * h y| := by
              simpa using norm_integral_le_integral_norm (fun y => hk ε (x - y) * h y)
          _ = ∫ y, hk ε (x - y) * |h y| := by
              refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
              simp only [abs_mul, abs_of_nonneg (hk_nonneg hε _)]
    _ = ∫ y, ∫ x, hk ε (x - y) * |h y| := integral_integral_swap hint'
    _ = ∫ y, |h y| := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
        simp only []
        rw [integral_mul_const, integral_sub_right_eq_self (fun z => hk ε z) y, integral_hk hε, one_mul]

theorem integrable_hk_mul {u : Torus d → ℝ} (hu : Integrable u volume) {ε : ℝ} (hε : 0 < ε) (x : Torus d) :
    Integrable (fun y => hk ε (x - y) * u y) volume := by
  obtain ⟨M, hM⟩ := hk_bdd (d := d) hε
  refine (hu.mul_bdd (c := M) ((continuous_hk hε).comp (continuous_const.sub continuous_id)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => ?_)).congr (Filter.Eventually.of_forall fun y => mul_comm _ _)
  rw [Real.norm_eq_abs]
  show |hk ε (x - y)| ≤ M
  rw [abs_of_nonneg (hk_nonneg hε _)]
  exact hM _

theorem cv_add {u w : Torus d → ℝ} (hu : Integrable u volume) (hw : Integrable w volume) {ε : ℝ} (hε : 0 < ε)
    (x : Torus d) : cv ε (fun y => u y + w y) x = cv ε u x + cv ε w x := by
  unfold cv
  simp_rw [mul_add]
  exact integral_add (integrable_hk_mul hu hε x) (integrable_hk_mul hw hε x)

theorem cv_L1 {f : Torus d → ℝ} (hfm : Measurable f) (hf : Integrable f volume) :
    Tendsto (fun ε : ℝ => ∫ x, |cv ε f x - f x|) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro η hη
  obtain ⟨g, hg1, hgint⟩ := hf.exists_boundedContinuous_integral_sub_le (show 0 < η / 4 by positivity)
  have hgc : Continuous g := g.continuous
  have hgm : Measurable (g : Torus d → ℝ) := hgc.measurable
  filter_upwards [cv_tendsto_cont hgc (show 0 < η / 4 by positivity), self_mem_nhdsWithin] with ε hε hεpos
  have hεpos' : 0 < ε := hεpos
  have hh : Integrable (fun y => f y - g y) volume := hf.sub hgint
  have hhm : Measurable (fun y => f y - g y) := hfm.sub hgm
  have e : ∀ x, cv ε f x - f x = cv ε (fun y => f y - g y) x + (cv ε g x - g x) - (f x - g x) := by
    intro x
    have := cv_add hh hgint hεpos' x
    simp only [sub_add_cancel] at this
    rw [this]; ring
  have hcvh : Integrable (cv ε (fun y => f y - g y)) volume :=
    (integrable_cv_prod hhm hh hεpos').integral_prod_left
  have hcvg : Integrable (cv ε g) volume :=
    (integrable_cv_prod hgm hgint hεpos').integral_prod_left
  have hdiff : Integrable (fun x => cv ε f x - f x) volume := by
    have : (fun x => cv ε f x - f x) = fun x => cv ε (fun y => f y - g y) x + (cv ε g x - g x) - (f x - g x) :=
      funext e
    rw [this]
    exact (hcvh.add (hcvg.sub hgint)).sub hh
  have hle : ∫ x, |cv ε f x - f x| ≤ ∫ x, (|cv ε (fun y => f y - g y) x| + |cv ε g x - g x| + |f x - g x|) := by
    refine integral_mono hdiff.abs ((hcvh.abs.add (hcvg.sub hgint).abs).add hh.abs) fun x => ?_
    rw [e x]
    refine (abs_sub _ _).trans ?_
    have := abs_add_le (cv ε (fun y => f y - g y) x) (cv ε g x - g x)
    linarith
  have hsum : ∫ x, (|cv ε (fun y => f y - g y) x| + |cv ε g x - g x| + |f x - g x|) =
      (∫ x, |cv ε (fun y => f y - g y) x|) + (∫ x, |cv ε g x - g x|) + (∫ x, |f x - g x|) := by
    have i1 : Integrable (fun x => |cv ε (fun y => f y - g y) x|) volume := hcvh.abs
    have i2 : Integrable (fun x => |cv ε g x - g x|) volume := (hcvg.sub hgint).abs
    have i3 : Integrable (fun x => |f x - g x|) volume := hh.abs
    have h12 : Integrable (fun x => |cv ε (fun y => f y - g y) x| + |cv ε g x - g x|) volume := i1.add i2
    rw [integral_add h12 i3, integral_add i1 i2]
  have b1 : ∫ x, |cv ε (fun y => f y - g y) x| ≤ η / 4 := by
    refine (integral_abs_cv_le hhm hh hεpos').trans ?_
    simpa [Real.norm_eq_abs] using hg1
  have b2 : ∫ x, |cv ε g x - g x| ≤ η / 4 := by
    calc ∫ x, |cv ε g x - g x| ≤ ∫ x : Torus d, η / 4 :=
          integral_mono (hcvg.sub hgint).abs (integrable_const _) hε
      _ = η / 4 := by simp
  have b3 : ∫ x, |f x - g x| ≤ η / 4 := by simpa [Real.norm_eq_abs] using hg1
  have hnn : 0 ≤ ∫ x, |cv ε f x - f x| := integral_nonneg fun x => abs_nonneg _
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hnn]
  linarith

end HRS.Commutator.Renorm
