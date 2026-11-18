import HRS.MD.EQLZCap3

/-!
# EQ-LZ packet CAP, helper 4: the cut-off stage (ii)-(iii) and the abstract core theorem

`CutFam Bd χ`: a family of smooth cut-offs, vanishing near the (closed) bad set `Bd`, eventually `1` near every
point off `Bd`, with energies `∫ capG (χ m) → 0`.  `stageC`: for `Ψ` bounded, `C¹` off `Bd` with integrable
energy, `χ m * Ψ` is globally `C¹`, converges to `Ψ` in `L²(ν)` and in energy.  `cap_core`: the abstract
approximation theorem (truncation, cut-off, mollification), conclusion in the form of `eqlz_cap` on the torus.
-/

noncomputable section

set_option linter.unusedSectionVars false

open MeasureTheory Filter Topology
open scoped Classical

namespace HRS.MD.EQLZ.Cap

variable {n : ℕ}

structure CutFam (Bd : Set (Torus n)) (χ : ℕ → Torus n → ℝ) : Prop where
  smooth : ∀ m, Torus.IsSmooth (χ m)
  nonneg : ∀ m x, 0 ≤ χ m x
  le_one : ∀ m x, χ m x ≤ 1
  zero_near : ∀ m y, Torus.mk y ∈ Bd → ∀ᶠ z in 𝓝 y, Torus.lift (χ m) z = 0
  one_near : ∀ y, Torus.mk y ∉ Bd → ∃ m₀, ∀ m ≥ m₀, ∀ᶠ z in 𝓝 y, Torus.lift (χ m) z = 1
  energy : Tendsto (fun m => ∫ x, capG (χ m) x) atTop (𝓝 0)

theorem contDiff_cut {Bd : Set (Torus n)} (hBd : IsClosed Bd) {c h : Euc n → ℝ} (hc : ContDiff ℝ 1 c)
    (hh : ContDiffOn ℝ 1 h {y | Torus.mk y ∉ Bd})
    (h0 : ∀ y, Torus.mk y ∈ Bd → ∀ᶠ z in 𝓝 y, c z = 0) : ContDiff ℝ 1 (fun y => c y * h y) := by
  rw [contDiff_iff_contDiffAt]
  intro y
  by_cases hy : Torus.mk y ∈ Bd
  · have : (fun y => c y * h y) =ᶠ[𝓝 y] fun _ => (0 : ℝ) := by
      filter_upwards [h0 y hy] with z hz
      simp [hz]
    exact contDiffAt_const.congr_of_eventuallyEq this
  · exact hc.contDiffAt.mul (hh.contDiffAt ((isOpen_notBd Bd hBd).mem_nhds hy))

theorem energy_pt {c h : Euc n → ℝ} {y : Euc n} (hc : DifferentiableAt ℝ c y)
    (hh : DifferentiableAt ℝ h y) (hc0 : 0 ≤ c y) (hc1 : c y ≤ 1) :
    |‖fderiv ℝ (fun z => c z * h z) y‖ ^ 2 - ‖fderiv ℝ h y‖ ^ 2| ≤
      2 * (h y) ^ 2 * ‖fderiv ℝ c y‖ ^ 2 +
        ‖fderiv ℝ h y‖ ^ 2 * ((if ‖fderiv ℝ c y‖ = 0 then 0 else 1) + (1 - c y ^ 2)) := by
  have e : fderiv ℝ (fun z => c z * h z) y = c y • fderiv ℝ h y + h y • fderiv ℝ c y :=
    fderiv_mul hc hh
  rw [e]
  set D := fderiv ℝ h y with hD
  set Dc := fderiv ℝ c y with hDc
  set a := h y • Dc with ha
  set b := c y • D with hb
  have hβ : ‖b‖ = c y * ‖D‖ := by rw [hb, norm_smul, Real.norm_eq_abs, abs_of_nonneg hc0]
  have hα : ‖a‖ ^ 2 = (h y) ^ 2 * ‖Dc‖ ^ 2 := by
    rw [ha, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  have hβD : ‖b‖ ≤ ‖D‖ := by
    rw [hβ]; exact mul_le_of_le_one_left (norm_nonneg _) hc1
  have hβ2 : ‖b‖ ^ 2 = c y ^ 2 * ‖D‖ ^ 2 := by rw [hβ, mul_pow]
  have hγ1 : ‖b + a‖ ≤ ‖b‖ + ‖a‖ := norm_add_le _ _
  have hγ2 : |‖b + a‖ - ‖b‖| ≤ ‖a‖ := by
    have := abs_norm_sub_norm_le (b + a) b
    simpa using this
  have h1 : |‖b + a‖ ^ 2 - ‖b‖ ^ 2| ≤ 2 * ‖a‖ ^ 2 + ‖b‖ ^ 2 * (if ‖Dc‖ = 0 then 0 else 1) := by
    have hfac : ‖b + a‖ ^ 2 - ‖b‖ ^ 2 = (‖b + a‖ - ‖b‖) * (‖b + a‖ + ‖b‖) := by ring
    rw [hfac, abs_mul, abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
    by_cases hz : ‖Dc‖ = 0
    · have hz' : Dc = 0 := norm_eq_zero.1 hz
      have : a = 0 := by rw [ha, hz']; simp
      have h0 : ‖a‖ = 0 := by rw [this]; simp
      simp only [hz, if_true]
      have := hγ2
      rw [h0] at this
      have : |‖b + a‖ - ‖b‖| = 0 := le_antisymm this (abs_nonneg _)
      rw [this]; simp
    · simp only [hz, if_false]
      calc |‖b + a‖ - ‖b‖| * (‖b + a‖ + ‖b‖) ≤ ‖a‖ * (2 * ‖b‖ + ‖a‖) := by
            apply mul_le_mul hγ2 (by linarith) (add_nonneg (norm_nonneg _) (norm_nonneg _)) (norm_nonneg _)
        _ ≤ 2 * ‖a‖ ^ 2 + ‖b‖ ^ 2 * 1 := by nlinarith [sq_nonneg (‖a‖ - ‖b‖), norm_nonneg a, norm_nonneg b]
  have h2 : |‖b‖ ^ 2 - ‖D‖ ^ 2| = ‖D‖ ^ 2 * (1 - c y ^ 2) := by
    rw [hβ2]
    have : c y ^ 2 * ‖D‖ ^ 2 - ‖D‖ ^ 2 = -(‖D‖ ^ 2 * (1 - c y ^ 2)) := by ring
    rw [this, abs_neg, abs_of_nonneg]
    exact mul_nonneg (sq_nonneg _) (by nlinarith)
  have h3 : |‖b + a‖ ^ 2 - ‖D‖ ^ 2| ≤ |‖b + a‖ ^ 2 - ‖b‖ ^ 2| + |‖b‖ ^ 2 - ‖D‖ ^ 2| := by
    have := abs_add_le (‖b + a‖ ^ 2 - ‖b‖ ^ 2) (‖b‖ ^ 2 - ‖D‖ ^ 2)
    simpa using this
  have h4 : ‖b‖ ^ 2 * (if ‖Dc‖ = 0 then 0 else 1) ≤ ‖D‖ ^ 2 * (if ‖Dc‖ = 0 then 0 else 1) := by
    apply mul_le_mul_of_nonneg_right _ (by split_ifs <;> norm_num)
    exact pow_le_pow_left₀ (norm_nonneg _) hβD 2
  calc _ ≤ _ := h3
    _ ≤ (2 * ‖a‖ ^ 2 + ‖b‖ ^ 2 * (if ‖Dc‖ = 0 then 0 else 1)) + ‖D‖ ^ 2 * (1 - c y ^ 2) := by
        rw [h2]; exact add_le_add h1 le_rfl
    _ ≤ _ := by rw [hα]; nlinarith [h4]

/-! ### The cut-off stage -/

section StageC

variable (ν : Measure (Torus n)) [IsFiniteMeasure ν]

theorem integrable_capG_of_cdiff (μ : Measure (Torus n)) [IsFiniteMeasure μ] {φ : Torus n → ℝ}
    (h : ContDiff ℝ 1 (Torus.lift φ)) : Integrable (capG φ) μ := by
  obtain ⟨L, hL0, hL⟩ := bdd_fderiv_of_cdiff h
  refine Integrable.of_bound (measurable_capG φ).aestronglyMeasurable (L ^ 2) (ae_of_all _ fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact pow_le_pow_left₀ (norm_nonneg _) (hL _) 2

theorem integral_le_vol {c : ℝ} (hc : 0 ≤ c) (hνc : ν ≤ ENNReal.ofReal c • (volume : Measure (Torus n)))
    {f : Torus n → ℝ} (hf0 : ∀ x, 0 ≤ f x) (hf : Integrable f (volume : Measure (Torus n))) :
    ∫ x, f x ∂ν ≤ c * ∫ x, f x := by
  have := integral_mono_measure hνc (ae_of_all _ hf0) (hf.smul_measure ENNReal.ofReal_ne_top)
  rwa [integral_smul_measure, ENNReal.toReal_ofReal hc, smul_eq_mul] at this

theorem stageC {Bd : Set (Torus n)} (hBd : IsClosed Bd) (hBd0 : ν Bd = 0) {c : ℝ} (hc : 0 ≤ c)
    (hνc : ν ≤ ENNReal.ofReal c • (volume : Measure (Torus n))) {χ : ℕ → Torus n → ℝ}
    (hχ : CutFam Bd χ) {Ψ : Torus n → ℝ} {B : ℝ} (hΨm : Measurable Ψ) (hΨb : ∀ x, |Ψ x| ≤ B)
    (hΨc : ContDiffOn ℝ 1 (Torus.lift Ψ) {y | Torus.mk y ∉ Bd}) (hΨE : Integrable (capG Ψ) ν) :
    (∀ m, ContDiff ℝ 1 (Torus.lift (fun x => χ m x * Ψ x))) ∧
    Tendsto (fun m => ∫ x, (χ m x * Ψ x - Ψ x) ^ 2 ∂ν) atTop (𝓝 0) ∧
    Tendsto (fun m => ∫ x, capG (fun x => χ m x * Ψ x) x ∂ν) atTop (𝓝 (∫ x, capG Ψ x ∂ν)) := by
  have hae : ∀ᵐ x ∂ν, x ∉ Bd := measure_eq_zero_iff_ae_notMem.1 hBd0
  have hcm : ∀ m, ContDiff ℝ 1 (Torus.lift (χ m)) := fun m => isSmooth_cdiff (hχ.smooth m)
  have hχm : ∀ m, Measurable (χ m) := fun m => (continuous_of_cdiff (hcm m)).measurable
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hΨb 0)
  -- (1) global C¹
  have hglob : ∀ m, ContDiff ℝ 1 (Torus.lift (fun x => χ m x * Ψ x)) := fun m =>
    contDiff_cut hBd (hcm m) hΨc (hχ.zero_near m)
  -- eventually `χ m x = 1` and `∇ lift χ m = 0` at the representative
  have hev : ∀ x, x ∉ Bd → ∀ᶠ m in atTop, χ m x = 1 ∧ ‖fderiv ℝ (Torus.lift (χ m)) (Torus.rep x)‖ = 0 := by
    intro x hx
    have hy : Torus.mk (Torus.rep x) ∉ Bd := by simpa [Torus.mk_rep] using hx
    obtain ⟨m₀, hm₀⟩ := hχ.one_near _ hy
    filter_upwards [eventually_ge_atTop m₀] with m hm
    have h1 := hm₀ m hm
    refine ⟨?_, ?_⟩
    · have := Filter.Eventually.self_of_nhds h1
      rwa [lift_rep] at this
    · have h1' : Torus.lift (χ m) =ᶠ[𝓝 (Torus.rep x)] fun _ => (1 : ℝ) := h1
      rw [h1'.fderiv_eq]; simp
  refine ⟨hglob, ?_, ?_⟩
  · -- values
    have := tendsto_integral_of_dominated_convergence (μ := ν)
      (F := fun (m : ℕ) x => (χ m x * Ψ x - Ψ x) ^ 2) (f := fun _ => (0 : ℝ)) (fun _ => B ^ 2)
      (fun m => (((hχm m).mul hΨm).sub hΨm).pow_const 2 |>.aestronglyMeasurable)
      (integrable_const _)
      (fun m => ae_of_all _ fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        have h1 : |χ m x * Ψ x - Ψ x| ≤ B := by
          have : χ m x * Ψ x - Ψ x = -((1 - χ m x) * Ψ x) := by ring
          rw [this, abs_neg, abs_mul, abs_of_nonneg (by linarith [hχ.le_one m x])]
          calc (1 - χ m x) * |Ψ x| ≤ 1 * |Ψ x| := by
                apply mul_le_mul_of_nonneg_right _ (abs_nonneg _); linarith [hχ.nonneg m x]
            _ ≤ B := by rw [one_mul]; exact hΨb x
        calc (χ m x * Ψ x - Ψ x) ^ 2 = |χ m x * Ψ x - Ψ x| ^ 2 := (sq_abs _).symm
          _ ≤ B ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2)
      (by
        filter_upwards [hae] with x hx
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [hev x hx] with m hm
        rw [hm.1]; simp)
    simpa using this
  · -- energies
    set r : ℕ → Torus n → ℝ := fun m x => 2 * B ^ 2 * capG (χ m) x +
      capG Ψ x * ((if ‖fderiv ℝ (Torus.lift (χ m)) (Torus.rep x)‖ = 0 then 0 else 1) + (1 - χ m x ^ 2))
      with hr
    have hS : ∀ m, MeasurableSet {x : Torus n | ‖fderiv ℝ (Torus.lift (χ m)) (Torus.rep x)‖ = 0} :=
      fun m => (measurableSet_singleton (0 : ℝ)).preimage
        ((measurable_fderiv ℝ (Torus.lift (χ m))).comp measurable_rep').norm
    have hsecm : ∀ m, Measurable (fun x => capG Ψ x * ((if ‖fderiv ℝ (Torus.lift (χ m)) (Torus.rep x)‖ = 0
        then 0 else 1) + (1 - χ m x ^ 2))) := fun m =>
      (measurable_capG Ψ).mul ((Measurable.ite (hS m) measurable_const measurable_const).add
        (measurable_const.sub ((hχm m).pow_const 2)))
    have hsecb : ∀ m x, |capG Ψ x * ((if ‖fderiv ℝ (Torus.lift (χ m)) (Torus.rep x)‖ = 0 then 0 else 1) +
        (1 - χ m x ^ 2))| ≤ 2 * capG Ψ x := by
      intro m x
      have h1 : (if ‖fderiv ℝ (Torus.lift (χ m)) (Torus.rep x)‖ = 0 then (0 : ℝ) else 1) ≤ 1 := by
        split_ifs <;> norm_num
      have h2 : 0 ≤ (if ‖fderiv ℝ (Torus.lift (χ m)) (Torus.rep x)‖ = 0 then (0 : ℝ) else 1) := by
        split_ifs <;> norm_num
      have h3 : 0 ≤ 1 - χ m x ^ 2 := by nlinarith [hχ.nonneg m x, hχ.le_one m x]
      have h4 : 1 - χ m x ^ 2 ≤ 1 := by nlinarith [hχ.nonneg m x]
      rw [abs_mul, abs_of_nonneg (capG_nonneg _ _), abs_of_nonneg (by linarith)]
      nlinarith [capG_nonneg Ψ x]
    have hsecI : ∀ m, Integrable (fun x => capG Ψ x * ((if ‖fderiv ℝ (Torus.lift (χ m)) (Torus.rep x)‖ = 0
        then 0 else 1) + (1 - χ m x ^ 2))) ν := fun m =>
      Integrable.mono' (hΨE.const_mul 2) (hsecm m).aestronglyMeasurable
        (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hsecb m x)
    have hfirstI : ∀ m, Integrable (fun x => 2 * B ^ 2 * capG (χ m) x) ν := fun m =>
      (integrable_capG_of_cdiff ν (hcm m)).const_mul _
    have hrI : ∀ m, Integrable (r m) ν := fun m => (hfirstI m).add (hsecI m)
    -- ∫ r → 0
    have tfirst : Tendsto (fun m => ∫ x, 2 * B ^ 2 * capG (χ m) x ∂ν) atTop (𝓝 0) := by
      refine squeeze_zero (fun m => integral_nonneg fun x => mul_nonneg (by positivity) (capG_nonneg _ _))
        (fun m => ?_) (by simpa using (hχ.energy.const_mul (2 * B ^ 2 * c)))
      rw [integral_const_mul]
      have := integral_le_vol ν hc hνc (f := capG (χ m)) (fun x => capG_nonneg _ _)
        (integrable_capG_of_cdiff _ (hcm m))
      calc 2 * B ^ 2 * ∫ x, capG (χ m) x ∂ν ≤ 2 * B ^ 2 * (c * ∫ x, capG (χ m) x) := by
            apply mul_le_mul_of_nonneg_left this (by positivity)
        _ = 2 * B ^ 2 * c * ∫ x, capG (χ m) x := by ring
    have tsecond : Tendsto (fun m => ∫ x, capG Ψ x * ((if ‖fderiv ℝ (Torus.lift (χ m)) (Torus.rep x)‖ = 0
        then 0 else 1) + (1 - χ m x ^ 2)) ∂ν) atTop (𝓝 0) := by
      have := tendsto_integral_of_dominated_convergence (μ := ν)
        (F := fun (m : ℕ) x => capG Ψ x * ((if ‖fderiv ℝ (Torus.lift (χ m)) (Torus.rep x)‖ = 0
          then 0 else 1) + (1 - χ m x ^ 2))) (f := fun _ => (0 : ℝ)) (fun x => 2 * capG Ψ x)
        (fun m => (hsecm m).aestronglyMeasurable) (hΨE.const_mul 2)
        (fun m => ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hsecb m x)
        (by
          filter_upwards [hae] with x hx
          refine tendsto_const_nhds.congr' ?_
          filter_upwards [hev x hx] with m hm
          rw [hm.2, hm.1]; simp)
      simpa using this
    have tr : Tendsto (fun m => ∫ x, r m x ∂ν) atTop (𝓝 0) := by
      have := tfirst.add tsecond
      simp only [add_zero] at this
      refine this.congr fun m => ?_
      rw [hr]
      exact (integral_add (hfirstI m) (hsecI m)).symm
    -- the pointwise bound
    have hpt : ∀ m, ∀ᵐ x ∂ν, |capG (fun x => χ m x * Ψ x) x - capG Ψ x| ≤ r m x := by
      intro m
      filter_upwards [hae] with x hx
      have hy : Torus.rep x ∈ {y : Euc n | Torus.mk y ∉ Bd} := by simpa [Torus.mk_rep] using hx
      have hh : DifferentiableAt ℝ (Torus.lift Ψ) (Torus.rep x) :=
        (hΨc.contDiffAt ((isOpen_notBd Bd hBd).mem_nhds hy)).differentiableAt one_ne_zero
      have hcd : DifferentiableAt ℝ (Torus.lift (χ m)) (Torus.rep x) :=
        ((hcm m).differentiable one_ne_zero) _
      have := energy_pt (c := Torus.lift (χ m)) (h := Torus.lift Ψ) hcd hh
        (by rw [lift_rep]; exact hχ.nonneg m x) (by rw [lift_rep]; exact hχ.le_one m x)
      rw [lift_rep, lift_rep] at this
      have hhy : (Ψ x) ^ 2 ≤ B ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hΨb x) 2
      refine this.trans ?_
      simp only [hr]
      unfold capG
      have hnn := sq_nonneg ‖fderiv ℝ (Torus.lift (χ m)) (Torus.rep x)‖
      nlinarith [mul_le_mul_of_nonneg_right hhy hnn]
    have hlow : ∀ m, |∫ x, capG (fun x => χ m x * Ψ x) x ∂ν - ∫ x, capG Ψ x ∂ν| ≤ ∫ x, r m x ∂ν := by
      intro m
      rw [← integral_sub (integrable_capG_of_cdiff ν (hglob m)) hΨE, ← Real.norm_eq_abs]
      refine (norm_integral_le_integral_norm _).trans ?_
      refine integral_mono_of_nonneg (ae_of_all _ fun x => norm_nonneg _) (hrI m) ?_
      filter_upwards [hpt m] with x hx
      rwa [Real.norm_eq_abs]
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero (fun m => norm_nonneg _) (fun m => by rw [Real.norm_eq_abs]; exact hlow m) tr

end StageC

/-! ### The abstract core theorem -/

section Core

variable (ν : Measure (Torus n)) [IsFiniteMeasure ν]

theorem capGood_core {Bd : Set (Torus n)} (hBd : IsClosed Bd) (hBd0 : ν Bd = 0) {c : ℝ} (hc : 0 ≤ c)
    (hνc : ν ≤ ENNReal.ofReal c • (volume : Measure (Torus n))) {χ : ℕ → Torus n → ℝ}
    (hχ : CutFam Bd χ) {Φ : Torus n → ℝ} (hm : Measurable Φ) (h2 : MemLp Φ 2 ν)
    (hcd : ContDiffOn ℝ 1 (Torus.lift Φ) {y | Torus.mk y ∉ Bd}) (hE : Integrable (capG Φ) ν) :
    CapGood ν Φ := by
  refine capGood_of_approx ν h2 (fun ε hε => ?_)
  obtain ⟨K, hK, hv, he⟩ := trunc_approx Bd ν hBd hBd0 hm h2 hcd hE ε hε
  obtain ⟨hm', hb', hc', hE'⟩ := trunc_props Bd ν hBd hBd0 hm hcd hE hK
  have hmem : MemLp (fun x => capTr K (Φ x)) 2 ν :=
    MemLp.of_bound hm'.aestronglyMeasurable (2 * K) (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs]; exact hb' x)
  refine ⟨fun x => capTr K (Φ x), hmem, hv, he, ?_⟩
  refine capGood_of_approx ν hmem (fun ε' hε' => ?_)
  obtain ⟨hglob, hv2, he2⟩ := stageC ν hBd hBd0 hc hνc hχ hm' hb' hc' hE'
  obtain ⟨m, hm1, hm2⟩ := ((hv2.eventually (gt_mem_nhds hε')).and
    ((tendsto_iff_norm_sub_tendsto_zero.1 he2).eventually (gt_mem_nhds hε'))).exists
  exact ⟨fun x => χ m x * capTr K (Φ x), memLp_of_cdiff ν (hglob m), hm1,
    by simpa [Real.norm_eq_abs] using hm2, capGood_of_C1 ν (hglob m)⟩

/-- **Core approximation theorem** on the torus `𝕋^n`. -/
theorem cap_core {Bd : Set (Torus n)} (hBd : IsClosed Bd) (hBd0 : ν Bd = 0) {c : ℝ} (hc : 0 ≤ c)
    (hνc : ν ≤ ENNReal.ofReal c • (volume : Measure (Torus n))) {χ : ℕ → Torus n → ℝ}
    (hχ : CutFam Bd χ) {Φ : Torus n → ℝ} (hm : Measurable Φ) (h2 : MemLp Φ 2 ν)
    (hcd : ContDiffOn ℝ 1 (Torus.lift Φ) {y | Torus.mk y ∉ Bd}) (hE : Integrable (capG Φ) ν) :
    ∃ G : ℕ → Torus n → ℝ, (∀ k, Torus.IsSmooth (G k)) ∧
      Tendsto (fun k => ∫ x, (G k x - Φ x) ^ 2 ∂ν) atTop (𝓝 0) ∧
      Tendsto (fun k => ∫ x, capG (G k) x ∂ν) atTop (𝓝 (∫ x, capG Φ x ∂ν)) :=
  exists_seq_of_capGood ν (capGood_core ν hBd hBd0 hc hνc hχ hm h2 hcd hE)

end Core

end HRS.MD.EQLZ.Cap
