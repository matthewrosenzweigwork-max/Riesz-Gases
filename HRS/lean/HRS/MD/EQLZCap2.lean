import HRS.MD.EQLZCap1

/-!
# EQ-LZ packet CAP, helper 2: the approximation predicate `CapGood`

`CapGood ν Ψ`: `Ψ` is approximated by smooth functions in `L²(ν)` with convergence of the energies `∫ capG`.
It holds for `C¹` functions (mollification, `capGood_of_C1`), and it is transitive through approximants
(`capGood_of_approx`).  Everything on the torus `𝕋^n` with a finite measure `ν`.
-/

noncomputable section

open MeasureTheory Filter Topology

namespace HRS.MD.EQLZ.Cap

variable {n : ℕ}

theorem measurable_rep' : Measurable (Torus.rep : Torus n → Euc n) := by
  have h : Measurable (fun (x : Torus n) (i : Fin n) =>
      ((AddCircle.equivIco (1 : ℝ) 0 (x i) : Set.Ico (0 : ℝ) (0 + 1)) : ℝ)) :=
    measurable_pi_iff.2 fun i => measurable_subtype_coe.comp
      ((AddCircle.measurableEquivIco (1 : ℝ) 0).measurable.comp (measurable_pi_apply i))
  exact (WithLp.measurable_toLp 2 _).comp h

theorem measurable_capG (φ : Torus n → ℝ) : Measurable (capG φ) :=
  ((measurable_fderiv ℝ (Torus.lift φ)).comp measurable_rep').norm.pow_const 2

theorem continuous_of_cdiff {φ : Torus n → ℝ} (h : ContDiff ℝ 1 (Torus.lift φ)) : Continuous φ :=
  KernelGrad.continuous_of_lift h.continuous

theorem bdd_of_cdiff {φ : Torus n → ℝ} (h : ContDiff ℝ 1 (Torus.lift φ)) : ∃ B, ∀ x, |φ x| ≤ B := by
  obtain ⟨B, hB⟩ := (isCompact_univ (X := Torus n)).exists_bound_of_continuousOn
    (continuous_of_cdiff h).continuousOn
  exact ⟨B, fun x => by simpa using hB x (Set.mem_univ x)⟩

theorem bdd_fderiv_of_cdiff {φ : Torus n → ℝ} (h : ContDiff ℝ 1 (Torus.lift φ)) :
    ∃ L, 0 ≤ L ∧ ∀ y, ‖fderiv ℝ (Torus.lift φ) y‖ ≤ L := by
  have p0 : ∀ (y : Euc n) (k : Lattice n), Torus.lift φ (y + Lattice.toEuc k) = Torus.lift φ y :=
    fun y k => Torus.lift_periodic φ y k
  obtain ⟨L, hL⟩ := d1_periodic_bounded (h.continuous_fderiv one_ne_zero) (d1_fderiv_periodic p0)
  exact ⟨max L 0, le_max_right _ _, fun y => (hL y).trans (le_max_left _ _)⟩

theorem memLp_of_cdiff (ν : Measure (Torus n)) [IsFiniteMeasure ν] {φ : Torus n → ℝ}
    (h : ContDiff ℝ 1 (Torus.lift φ)) : MemLp φ 2 ν := by
  obtain ⟨B, hB⟩ := bdd_of_cdiff h
  exact MemLp.of_bound (continuous_of_cdiff h).aestronglyMeasurable B
    (ae_of_all _ fun x => by simpa using hB x)

theorem isSmooth_cdiff {φ : Torus n → ℝ} (h : Torus.IsSmooth φ) : ContDiff ℝ 1 (Torus.lift φ) := by
  have h' : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift φ) := h
  exact h'.of_le (by exact_mod_cast le_top)

/-- Approximation of `Ψ` by smooth functions with convergence of values (`L²(ν)`) and of energies. -/
def CapGood (ν : Measure (Torus n)) (Ψ : Torus n → ℝ) : Prop :=
  ∀ ε > 0, ∃ G : Torus n → ℝ, Torus.IsSmooth G ∧ ∫ x, (G x - Ψ x) ^ 2 ∂ν < ε ∧
    |∫ x, capG G x ∂ν - ∫ x, capG Ψ x ∂ν| < ε

theorem integrable_sq_diff_of_bdd (ν : Measure (Torus n)) [IsFiniteMeasure ν] {f g : Torus n → ℝ}
    (hf : Measurable f) (hg : Measurable g) {B : ℝ} (hB : ∀ x, |f x - g x| ≤ B) :
    Integrable (fun x => (f x - g x) ^ 2) ν := by
  refine Integrable.of_bound ((hf.sub hg).pow_const 2).aestronglyMeasurable (B ^ 2)
    (ae_of_all _ fun x => ?_)
  rw [Real.norm_eq_abs, abs_pow]
  exact pow_le_pow_left₀ (abs_nonneg _) (hB x) 2

/-- `C¹` functions on the torus are `CapGood` (mollification). -/
theorem capGood_of_C1 (ν : Measure (Torus n)) [IsFiniteMeasure ν] {Ψ : Torus n → ℝ}
    (hΨ : ContDiff ℝ 1 (Torus.lift Ψ)) : CapGood ν Ψ := by
  intro ε hε
  obtain ⟨L, hL0, hL⟩ := bdd_fderiv_of_cdiff hΨ
  set M : ℝ := ν.real Set.univ + 1 with hM
  have hνM : ν.real Set.univ ≤ M := by rw [hM]; linarith
  have hν0 : 0 ≤ ν.real Set.univ := ENNReal.toReal_nonneg
  have hMpos : 0 < M := by rw [hM]; linarith
  set η : ℝ := min 1 (ε / (M * (2 * L + 3))) with hη
  have hηpos : 0 < η := lt_min one_pos (by positivity)
  have hη1 : η ≤ 1 := min_le_left _ _
  have hη2 : η ≤ ε / (M * (2 * L + 3)) := min_le_right _ _
  have hη3 : η * (M * (2 * L + 3)) ≤ ε := (le_div_iff₀ (by positivity)).1 hη2
  obtain ⟨ψ, hψ, hψb⟩ := exists_C1_approx hΨ hηpos
  have hψc : ContDiff ℝ 1 (Torus.lift ψ) := isSmooth_cdiff hψ
  obtain ⟨L', hL'0, hL'⟩ := bdd_fderiv_of_cdiff hψc
  have hm1 : Measurable ψ := (continuous_of_cdiff hψc).measurable
  have hm2 : Measurable Ψ := (continuous_of_cdiff hΨ).measurable
  refine ⟨ψ, hψ, ?_, ?_⟩
  · -- values
    have h1 : ∫ x, (ψ x - Ψ x) ^ 2 ∂ν ≤ ∫ _x, η ^ 2 ∂ν := by
      refine integral_mono_of_nonneg (ae_of_all _ fun x => sq_nonneg _) (integrable_const _)
        (ae_of_all _ fun x => ?_)
      have := (hψb x).1
      rw [abs_sub_comm] at this
      have h2 := (sq_le_sq₀ (abs_nonneg _) hηpos.le).2 this
      rwa [sq_abs] at h2
    rw [integral_const, smul_eq_mul] at h1
    refine lt_of_le_of_lt h1 ?_
    have hk : M * η * 3 ≤ ε := by nlinarith [mul_pos hMpos hηpos]
    calc ν.real Set.univ * η ^ 2 ≤ M * η := by
          have : η ^ 2 ≤ η := by nlinarith
          calc ν.real Set.univ * η ^ 2 ≤ M * η ^ 2 := by gcongr
            _ ≤ M * η := by gcongr
      _ < ε := by nlinarith [mul_pos hMpos hηpos]
  · -- energies
    have hpt : ∀ x, |capG ψ x - capG Ψ x| ≤ η * (2 * L + 1) := by
      intro x
      have ha := hL (Torus.rep x)
      have hb := (hψb x).2
      set a := fderiv ℝ (Torus.lift Ψ) (Torus.rep x)
      set b := fderiv ℝ (Torus.lift ψ) (Torus.rep x)
      have hba : ‖b‖ ≤ L + η := by
        calc ‖b‖ = ‖a - (a - b)‖ := by congr 1; abel
          _ ≤ ‖a‖ + ‖a - b‖ := norm_sub_le _ _
          _ ≤ L + η := add_le_add ha hb
      have hab : |‖b‖ - ‖a‖| ≤ η := (abs_norm_sub_norm_le b a).trans (by rwa [norm_sub_rev])
      unfold capG
      change |‖b‖ ^ 2 - ‖a‖ ^ 2| ≤ _
      have : ‖b‖ ^ 2 - ‖a‖ ^ 2 = (‖b‖ - ‖a‖) * (‖b‖ + ‖a‖) := by ring
      rw [this, abs_mul, abs_of_nonneg (add_nonneg (norm_nonneg b) (norm_nonneg a))]
      exact mul_le_mul hab (by linarith) (add_nonneg (norm_nonneg _) (norm_nonneg _)) hηpos.le
    have hi1 : Integrable (capG ψ) ν := Integrable.of_bound (measurable_capG ψ).aestronglyMeasurable
      ((L' ) ^ 2) (ae_of_all _ fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact pow_le_pow_left₀ (norm_nonneg _) (hL' _) 2)
    have hi2 : Integrable (capG Ψ) ν := Integrable.of_bound (measurable_capG Ψ).aestronglyMeasurable
      (L ^ 2) (ae_of_all _ fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact pow_le_pow_left₀ (norm_nonneg _) (hL _) 2)
    rw [← integral_sub hi1 hi2, ← Real.norm_eq_abs]
    have hb : ‖∫ x, (capG ψ x - capG Ψ x) ∂ν‖ ≤ η * (2 * L + 1) * ν.real Set.univ :=
      norm_integral_le_of_norm_le_const (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hpt x)
    refine lt_of_le_of_lt hb ?_
    calc η * (2 * L + 1) * ν.real Set.univ ≤ η * (2 * L + 1) * M := by gcongr
      _ < ε := by nlinarith [mul_pos hMpos hηpos]

/-- Triangle inequality in `L²`, squared form. -/
theorem l2_trans (ν : Measure (Torus n)) {u v w : Torus n → ℝ} (hu : MemLp u 2 ν) (hv : MemLp v 2 ν)
    (hw : MemLp w 2 ν) :
    ∫ x, (u x - w x) ^ 2 ∂ν ≤ 2 * ∫ x, (u x - v x) ^ 2 ∂ν + 2 * ∫ x, (v x - w x) ^ 2 ∂ν := by
  have h1 : Integrable (fun x => (u x - v x) ^ 2) ν := (hu.sub hv).integrable_sq
  have h2 : Integrable (fun x => (v x - w x) ^ 2) ν := (hv.sub hw).integrable_sq
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add (h1.const_mul 2) (h2.const_mul 2)]
  refine integral_mono_of_nonneg (ae_of_all _ fun x => sq_nonneg _) ((h1.const_mul 2).add (h2.const_mul 2))
    (ae_of_all _ fun x => ?_)
  nlinarith [sq_nonneg (u x - v x + (v x - w x)), sq_nonneg (u x - v x - (v x - w x))]

/-- `CapGood` passes through approximants. -/
theorem capGood_of_approx (ν : Measure (Torus n)) [IsFiniteMeasure ν] {Ψ : Torus n → ℝ}
    (hΨ : MemLp Ψ 2 ν)
    (h : ∀ ε > 0, ∃ Ψ' : Torus n → ℝ, MemLp Ψ' 2 ν ∧ ∫ x, (Ψ' x - Ψ x) ^ 2 ∂ν < ε ∧
      |∫ x, capG Ψ' x ∂ν - ∫ x, capG Ψ x ∂ν| < ε ∧ CapGood ν Ψ') : CapGood ν Ψ := by
  intro ε hε
  obtain ⟨Ψ', hΨ'2, hv, he, hg⟩ := h (ε / 5) (by positivity)
  obtain ⟨G, hG, hGv, hGe⟩ := hg (ε / 5) (by positivity)
  refine ⟨G, hG, ?_, ?_⟩
  · have hG2 : MemLp G 2 ν := memLp_of_cdiff ν (isSmooth_cdiff hG)
    have := l2_trans ν hG2 hΨ'2 hΨ
    linarith
  · calc |∫ x, capG G x ∂ν - ∫ x, capG Ψ x ∂ν|
        = |(∫ x, capG G x ∂ν - ∫ x, capG Ψ' x ∂ν) + (∫ x, capG Ψ' x ∂ν - ∫ x, capG Ψ x ∂ν)| := by
          congr 1; ring
      _ ≤ |∫ x, capG G x ∂ν - ∫ x, capG Ψ' x ∂ν| + |∫ x, capG Ψ' x ∂ν - ∫ x, capG Ψ x ∂ν| :=
          abs_add_le _ _
      _ < ε := by linarith

/-- A `CapGood` function is the limit of a sequence of smooth functions. -/
theorem exists_seq_of_capGood (ν : Measure (Torus n)) {Ψ : Torus n → ℝ} (h : CapGood ν Ψ) :
    ∃ G : ℕ → Torus n → ℝ, (∀ k, Torus.IsSmooth (G k)) ∧
      Tendsto (fun k => ∫ x, (G k x - Ψ x) ^ 2 ∂ν) atTop (𝓝 0) ∧
      Tendsto (fun k => ∫ x, capG (G k) x ∂ν) atTop (𝓝 (∫ x, capG Ψ x ∂ν)) := by
  have hk : ∀ k : ℕ, ∃ G : Torus n → ℝ, Torus.IsSmooth G ∧ ∫ x, (G x - Ψ x) ^ 2 ∂ν < 1 / ((k : ℝ) + 1) ∧
      |∫ x, capG G x ∂ν - ∫ x, capG Ψ x ∂ν| < 1 / ((k : ℝ) + 1) := fun k => h _ (by positivity)
  choose G hG hv he using hk
  refine ⟨G, hG, ?_, ?_⟩
  · refine squeeze_zero (fun k => integral_nonneg fun x => sq_nonneg _) (fun k => (hv k).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  · rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun k => norm_nonneg _) (fun k => ?_) tendsto_one_div_add_atTop_nhds_zero_nat
    rw [Real.norm_eq_abs]
    exact (he k).le

end HRS.MD.EQLZ.Cap
