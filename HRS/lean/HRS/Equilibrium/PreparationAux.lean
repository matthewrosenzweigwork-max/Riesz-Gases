import HRS.Equilibrium.PoleCavity

/-! Auxiliary results for `HRS.Equilibrium.Preparation` (package EQ-PREP). -/

open MeasureTheory Filter Topology ProbabilityTheory Metric Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.PreparationAux

variable {d : ℕ}

/-- The energy `W = N F_N(·, μ)`. -/
def Wen (g : Torus d → ℝ) (N : ℕ) (μ : Measure (Torus d)) (X : Config d N) : ℝ :=
  (N : ℝ) * modulatedEnergyKernel g X μ

theorem measurable_energy {g : Torus d → ℝ} (hg : Measurable g) (μ : Measure (Torus d))
    [SFinite μ] {N : ℕ} : Measurable (fun X : Config d N => modulatedEnergyKernel g X μ) := by
  unfold modulatedEnergyKernel modulatedEnergy
  have h1 : Measurable (fun X : Config d N => ∑ i, ∑ j ∈ Finset.univ.erase i, g (X i - X j)) :=
    Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ =>
      hg.comp ((measurable_pi_apply i).sub (measurable_pi_apply j))
  have h2 : Measurable (fun X : Config d N => ∑ i, ∫ y, g (X i - y) ∂μ) :=
    Finset.measurable_sum _ fun i _ =>
      (PoleCavityAux.measurable_convMeasure hg μ).comp (measurable_pi_apply i)
  exact ((h1.const_mul _).sub (h2.const_mul _)).add_const _

theorem measurable_Wen {g : Torus d → ℝ} (hg : Measurable g) (μ : Measure (Torus d))
    [SFinite μ] {N : ℕ} : Measurable (Wen g N μ) :=
  (measurable_energy hg μ).const_mul _

section Energy

variable {g : Torus d → ℝ} {μ : Measure (Torus d)} [IsProbabilityMeasure μ] {N : ℕ}

theorem integrable_energy_terms (hI : Integrable (fun p : Torus d × Torus d => g (p.1 - p.2)) (μ.prod μ)) :
    Integrable (fun X : Config d N => modulatedEnergyKernel g X μ) (Measure.pi fun _ : Fin N => μ) := by
  have hpair : ∀ i j : Fin N, i ≠ j →
      Integrable (fun X : Config d N => g (X i - X j)) (Measure.pi fun _ : Fin N => μ) :=
    fun i j hij => integrable_pair_comp μ hij (H := fun p => g (p.1 - p.2)) hI
  have hconv_int : Integrable (fun x => ∫ y, g (x - y) ∂μ) μ := hI.integral_prod_left
  have h1 : ∀ i : Fin N, Integrable (fun X : Config d N => ∫ y, g (X i - y) ∂μ)
      (Measure.pi fun _ : Fin N => μ) := fun i =>
    integrable_comp_eval (μ := fun _ : Fin N => μ) (i := i) hconv_int
  have hT1 : Integrable (fun X : Config d N => ∑ i, ∑ j ∈ Finset.univ.erase i, g (X i - X j))
      (Measure.pi fun _ : Fin N => μ) :=
    integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j hj =>
      hpair i j (Finset.ne_of_mem_erase hj).symm
  have hT2 : Integrable (fun X : Config d N => ∑ i, ∫ y, g (X i - y) ∂μ)
      (Measure.pi fun _ : Fin N => μ) := integrable_finsetSum _ fun i _ => h1 i
  unfold modulatedEnergyKernel modulatedEnergy
  exact ((hT1.const_mul _).sub (hT2.const_mul _)).add (integrable_const _)

theorem integral_energy_iid (hN : 1 ≤ N)
    (hI : Integrable (fun p : Torus d × Torus d => g (p.1 - p.2)) (μ.prod μ)) :
    ∫ X, modulatedEnergyKernel g X μ ∂(Measure.pi fun _ : Fin N => μ) =
      -(1 / (2 * N)) * ∫ p : Torus d × Torus d, g (p.1 - p.2) ∂(μ.prod μ) := by
  set G := ∫ p : Torus d × Torus d, g (p.1 - p.2) ∂(μ.prod μ) with hG
  have hN' : (N : ℝ) ≠ 0 := by positivity
  have hpair : ∀ i j : Fin N, i ≠ j →
      Integrable (fun X : Config d N => g (X i - X j)) (Measure.pi fun _ : Fin N => μ) :=
    fun i j hij => integrable_pair_comp μ hij (H := fun p => g (p.1 - p.2)) hI
  have hpair' : ∀ i j : Fin N, i ≠ j →
      ∫ X : Config d N, g (X i - X j) ∂(Measure.pi fun _ : Fin N => μ) = G :=
    fun i j hij => integral_pair_comp μ hij (H := fun p => g (p.1 - p.2)) hI
  have hconv_int : Integrable (fun x => ∫ y, g (x - y) ∂μ) μ := hI.integral_prod_left
  have hconv_mean : ∫ x, ∫ y, g (x - y) ∂μ ∂μ = G := by
    rw [hG, integral_prod _ hI]
  have h1 : ∀ i : Fin N, Integrable (fun X : Config d N => ∫ y, g (X i - y) ∂μ)
      (Measure.pi fun _ : Fin N => μ) := fun i =>
    integrable_comp_eval (μ := fun _ : Fin N => μ) (i := i) hconv_int
  have h1' : ∀ i : Fin N, ∫ X : Config d N, ∫ y, g (X i - y) ∂μ ∂(Measure.pi fun _ : Fin N => μ) = G :=
    fun i => by
      have := integral_comp_eval (μ := fun _ : Fin N => μ) (i := i) hconv_int.aestronglyMeasurable
      exact this.trans hconv_mean
  have hT1 : Integrable (fun X : Config d N => ∑ i, ∑ j ∈ Finset.univ.erase i, g (X i - X j))
      (Measure.pi fun _ : Fin N => μ) :=
    integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j hj =>
      hpair i j (Finset.ne_of_mem_erase hj).symm
  have hT2 : Integrable (fun X : Config d N => ∑ i, ∫ y, g (X i - y) ∂μ)
      (Measure.pi fun _ : Fin N => μ) := integrable_finsetSum _ fun i _ => h1 i
  have E1 : ∫ X : Config d N, ∑ i, ∑ j ∈ Finset.univ.erase i, g (X i - X j)
      ∂(Measure.pi fun _ : Fin N => μ) = (N : ℝ) * ((N : ℝ) - 1) * G := by
    rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j hj =>
      hpair i j (Finset.ne_of_mem_erase hj).symm]
    have : ∀ i : Fin N, ∫ X : Config d N, ∑ j ∈ Finset.univ.erase i, g (X i - X j)
        ∂(Measure.pi fun _ : Fin N => μ) = ((N : ℝ) - 1) * G := by
      intro i
      rw [integral_finsetSum _ fun j hj => hpair i j (Finset.ne_of_mem_erase hj).symm]
      rw [Finset.sum_congr rfl fun j hj => hpair' i j (Finset.ne_of_mem_erase hj).symm]
      rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ i)]
      simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [Nat.cast_sub hN]; simp
    simp_rw [this]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  have E2 : ∫ X : Config d N, ∑ i, ∫ y, g (X i - y) ∂μ ∂(Measure.pi fun _ : Fin N => μ) = N * G := by
    rw [integral_finsetSum _ fun i _ => h1 i]
    simp_rw [h1']
    simp
  unfold modulatedEnergyKernel modulatedEnergy
  rw [integral_add, integral_sub, integral_const_mul, integral_const_mul, E1, E2, integral_const]
  · have hμ : (Measure.pi fun _ : Fin N => μ).real Set.univ = 1 := by simp [Measure.real]
    rw [hμ, one_smul]
    have : ∫ x, ∫ y, (fun x y => g (x - y)) x y ∂μ ∂μ = G := hconv_mean
    rw [this]
    field_simp
    ring
  all_goals first
    | exact (hT1.const_mul _)
    | exact (hT2.const_mul _)
    | exact ((hT1.const_mul _).sub (hT2.const_mul _))
    | exact integrable_const _

theorem integrable_Wen (hI : Integrable (fun p : Torus d × Torus d => g (p.1 - p.2)) (μ.prod μ)) :
    Integrable (Wen g N μ) (Measure.pi fun _ : Fin N => μ) :=
  (integrable_energy_terms hI).const_mul _

theorem integral_Wen (hN : 1 ≤ N)
    (hI : Integrable (fun p : Torus d × Torus d => g (p.1 - p.2)) (μ.prod μ)) :
    ∫ X, Wen g N μ X ∂(Measure.pi fun _ : Fin N => μ) =
      -(1 / 2) * ∫ p : Torus d × Torus d, g (p.1 - p.2) ∂(μ.prod μ) := by
  unfold Wen
  rw [integral_const_mul, integral_energy_iid hN hI]
  have : (N : ℝ) ≠ 0 := by positivity
  field_simp



end Energy

section Abstract

variable {α : Type*} [MeasurableSpace α] {ν : Measure α} [IsProbabilityMeasure ν] {W : α → ℝ}

/-- the partition function -/
def Zf (ν : Measure α) (W : α → ℝ) (c : ℝ) : ℝ := ∫ x, Real.exp (-c * W x) ∂ν

theorem integrable_exp_of_succ (hW : Measurable W) {c : ℝ} (hc : 0 ≤ c)
    (h : Integrable (fun x => Real.exp (-(c + 1) * W x)) ν) :
    Integrable (fun x => Real.exp (-c * W x)) ν := by
  refine Integrable.mono' ((integrable_const (1:ℝ)).add h) ?_ (Filter.Eventually.of_forall fun x => ?_)
  · exact (Real.measurable_exp.comp (measurable_const.mul hW)).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    by_cases hx : 0 ≤ W x
    · have : Real.exp (-c * W x) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
      have := (Real.exp_pos (-(c + 1) * W x)).le
      simp only [Pi.add_apply]; linarith
    · push Not at hx
      have h1 : Real.exp (-c * W x) ≤ Real.exp (-(c + 1) * W x) :=
        Real.exp_le_exp.2 (by nlinarith)
      simp only [Pi.add_apply]; linarith

theorem integrable_W_exp (hW : Measurable W) (hWi : Integrable W ν) {c : ℝ} (hc : 0 ≤ c)
    (h : Integrable (fun x => Real.exp (-(c + 1) * W x)) ν) :
    Integrable (fun x => W x * Real.exp (-c * W x)) ν := by
  refine Integrable.mono' (hWi.norm.add h) ?_ (Filter.Eventually.of_forall fun x => ?_)
  · exact (hW.mul (Real.measurable_exp.comp (measurable_const.mul hW))).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    simp only [Pi.add_apply, Real.norm_eq_abs]
    by_cases hx : 0 ≤ W x
    · have : Real.exp (-c * W x) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
      have h0 := abs_nonneg (W x)
      have := (Real.exp_pos (-(c + 1) * W x)).le
      nlinarith
    · push Not at hx
      have e1 : |W x| ≤ Real.exp (|W x|) := by linarith [Real.add_one_le_exp (|W x|)]
      have e2 : |W x| * Real.exp (-c * W x) ≤ Real.exp (-(c + 1) * W x) := by
        calc |W x| * Real.exp (-c * W x) ≤ Real.exp (|W x|) * Real.exp (-c * W x) :=
              mul_le_mul_of_nonneg_right e1 (Real.exp_pos _).le
          _ = Real.exp (-(c + 1) * W x) := by
              rw [← Real.exp_add, abs_of_neg hx]; congr 1; ring
      have := abs_nonneg (W x)
      linarith

/-- tilted Jensen: `Z(c) ≤ exp(t m) Z(c+t)` with `m = E_c[W]`. -/
theorem tilt_jensen (hW : Measurable W) {c t : ℝ}
    (h0 : Integrable (fun x => Real.exp (-c * W x)) ν)
    (h1 : Integrable (fun x => W x * Real.exp (-c * W x)) ν)
    (h2 : Integrable (fun x => Real.exp (-(c + t) * W x)) ν) :
    Zf ν W c ≤ Real.exp (t * ((∫ x, W x * Real.exp (-c * W x) ∂ν) / Zf ν W c)) * Zf ν W (c + t) := by
  have hZ : 0 < Zf ν W c := integral_exp_pos (f := fun x => -c * W x) h0
  set m := (∫ x, W x * Real.exp (-c * W x) ∂ν) / Zf ν W c with hm
  have hmZ : m * Zf ν W c = ∫ x, W x * Real.exp (-c * W x) ∂ν := by
    rw [hm, div_mul_cancel₀ _ hZ.ne']
  have hpt : ∀ x, Real.exp (-c * W x) * (1 + t * (m - W x)) ≤
      Real.exp (t * m) * Real.exp (-(c + t) * W x) := by
    intro x
    have : Real.exp (t * m) * Real.exp (-(c + t) * W x) =
        Real.exp (-c * W x) * Real.exp (t * (m - W x)) := by
      rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
    rw [this]
    exact mul_le_mul_of_nonneg_left (by linarith [Real.add_one_le_exp (t * (m - W x))])
      (Real.exp_pos _).le
  have hint_l : Integrable (fun x => Real.exp (-c * W x) * (1 + t * (m - W x))) ν := by
    have : (fun x => Real.exp (-c * W x) * (1 + t * (m - W x))) =
        fun x => (1 + t * m) * Real.exp (-c * W x) - t * (W x * Real.exp (-c * W x)) := by
      funext x; ring
    rw [this]
    exact (h0.const_mul _).sub (h1.const_mul _)
  have := integral_mono hint_l (h2.const_mul (Real.exp (t * m))) hpt
  have e1 : ∫ x, Real.exp (-c * W x) * (1 + t * (m - W x)) ∂ν = Zf ν W c := by
    have : (fun x => Real.exp (-c * W x) * (1 + t * (m - W x))) =
        fun x => (1 + t * m) * Real.exp (-c * W x) - t * (W x * Real.exp (-c * W x)) := by
      funext x; ring
    rw [this, integral_sub (h0.const_mul _) (h1.const_mul _), integral_const_mul, integral_const_mul,
      ← hmZ]
    unfold Zf; ring
  rw [e1, integral_const_mul] at this
  exact this

end Abstract




section Gibbs

/-- Same as `HRS.modNormalizerE` (defined in `Preparation.lean`; the two are definitionally equal). -/
def KE {d : ℕ} (g : Torus d → ℝ) (N : ℕ) (γ : ℝ) (μ : Measure (Torus d)) : ℝ≥0∞ :=
  ∫⁻ X : Config d N, ENNReal.ofReal (Real.exp (-γ * N * modulatedEnergyKernel g X μ))
    ∂(Measure.pi fun _ => μ)

variable {d : ℕ} {g : Torus d → ℝ} {μ : Measure (Torus d)} [IsProbabilityMeasure μ] {N : ℕ}

theorem neg_mul_Wen (c : ℝ) (X : Config d N) :
    -c * (N : ℝ) * modulatedEnergyKernel g X μ = -c * Wen g N μ X := by
  unfold Wen; ring

theorem KE_eq (c : ℝ) :
    KE g N c μ =
      ∫⁻ X, ENNReal.ofReal (Real.exp (-c * Wen g N μ X)) ∂(Measure.pi fun _ : Fin N => μ) := by
  unfold KE
  simp_rw [neg_mul_Wen]

theorem gibbsNormalizer_eq (c : ℝ) :
    gibbsNormalizer g N c μ = Zf (Measure.pi fun _ : Fin N => μ) (Wen g N μ) c := by
  unfold gibbsNormalizer Zf
  simp_rw [neg_mul_Wen]

theorem toReal_KE (hg : Measurable g) (c : ℝ) :
    (KE g N c μ).toReal = Zf (Measure.pi fun _ : Fin N => μ) (Wen g N μ) c := by
  rw [KE_eq, Zf]
  exact (integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun x => (Real.exp_pos _).le)
    (Real.measurable_exp.comp (measurable_const.mul (measurable_Wen hg μ))).aestronglyMeasurable).symm

theorem integrable_exp_of_ne_top (hg : Measurable g) {c : ℝ} (h : KE g N c μ ≠ ∞) :
    Integrable (fun X : Config d N => Real.exp (-c * Wen g N μ X)) (Measure.pi fun _ : Fin N => μ) := by
  rw [KE_eq] at h
  have := integrable_toReal_of_lintegral_ne_top
    (μ := Measure.pi fun _ : Fin N => μ)
    (f := fun X : Config d N => ENNReal.ofReal (Real.exp (-c * Wen g N μ X)))
    (ENNReal.measurable_ofReal.comp
      (Real.measurable_exp.comp (measurable_const.mul (measurable_Wen hg μ)))).aemeasurable h
  simpa [ENNReal.toReal_ofReal (Real.exp_pos _).le] using this

theorem modulatedGibbs_eq (c : ℝ) :
    modulatedGibbs g N c μ =
      (ENNReal.ofReal (Zf (Measure.pi fun _ : Fin N => μ) (Wen g N μ) c))⁻¹ •
        (Measure.pi fun _ : Fin N => μ).withDensity
          fun X => ENNReal.ofReal (Real.exp (-c * Wen g N μ X)) := by
  unfold modulatedGibbs
  rw [gibbsNormalizer_eq]
  simp_rw [neg_mul_Wen]

theorem integral_modulatedGibbs (c : ℝ) (hg : Measurable g) (f : Config d N → ℝ) :
    ∫ X, f X ∂(modulatedGibbs g N c μ) =
      (Zf (Measure.pi fun _ : Fin N => μ) (Wen g N μ) c)⁻¹ *
        ∫ X, Real.exp (-c * Wen g N μ X) * f X ∂(Measure.pi fun _ : Fin N => μ) := by
  have hZ0 : 0 ≤ Zf (Measure.pi fun _ : Fin N => μ) (Wen g N μ) c :=
    integral_nonneg fun x => (Real.exp_pos _).le
  have hm : Measurable (fun X : Config d N => ENNReal.ofReal (Real.exp (-c * Wen g N μ X))) :=
    ENNReal.measurable_ofReal.comp
      (Real.measurable_exp.comp (measurable_const.mul (measurable_Wen hg μ)))
  rw [modulatedGibbs_eq, integral_smul_measure,
    integral_withDensity_eq_integral_toReal_smul hm
      (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
  rw [ENNReal.toReal_inv, ENNReal.toReal_ofReal hZ0, smul_eq_mul]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun X => ?_)
  simp [ENNReal.toReal_ofReal (Real.exp_pos _).le]

/-- Integrability of `W` under `Q_c`, from integrability of `W e^{-cW}`. -/
theorem integrable_Wen_Q (hg : Measurable g) {c : ℝ} (hZ : 0 < Zf (Measure.pi fun _ : Fin N => μ) (Wen g N μ) c)
    (h : Integrable (fun X => Wen g N μ X * Real.exp (-c * Wen g N μ X)) (Measure.pi fun _ : Fin N => μ)) :
    Integrable (Wen g N μ) (modulatedGibbs g N c μ) := by
  have hm : Measurable (fun X : Config d N => ENNReal.ofReal (Real.exp (-c * Wen g N μ X))) :=
    ENNReal.measurable_ofReal.comp
      (Real.measurable_exp.comp (measurable_const.mul (measurable_Wen hg μ)))
  rw [modulatedGibbs_eq]
  refine Integrable.smul_measure ?_ ?_
  · rw [integrable_withDensity_iff_integrable_smul' hm
      (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
    refine h.congr (Filter.Eventually.of_forall fun X => ?_)
    simp [ENNReal.toReal_ofReal (Real.exp_pos _).le, mul_comm]
  · exact ENNReal.inv_ne_top.2 (ENNReal.ofReal_pos.2 hZ).ne'

theorem isProb_modulatedGibbs (hg : Measurable g) {c : ℝ} (hK : KE g N c μ ≠ ∞) :
    IsProbabilityMeasure (modulatedGibbs g N c μ) := by
  have hint := integrable_exp_of_ne_top hg hK
  have hZ : 0 < Zf (Measure.pi fun _ : Fin N => μ) (Wen g N μ) c :=
    integral_exp_pos (f := fun X => -c * Wen g N μ X) hint
  refine modulatedGibbs_isProbabilityMeasure g c μ ?_ ?_
  · rw [gibbsNormalizer_eq]; exact hZ
  · simp only [neg_mul_Wen]; exact hint

theorem Zf_pos (hg : Measurable g) {c : ℝ} (hK : KE g N c μ ≠ ∞) :
    0 < Zf (Measure.pi fun _ : Fin N => μ) (Wen g N μ) c :=
  integral_exp_pos (f := fun X => -c * Wen g N μ X) (integrable_exp_of_ne_top hg hK)

theorem KE_ne_top_of_succ (hg : Measurable g) {c : ℝ} (hc : 0 ≤ c) (h : KE g N (c + 1) μ ≠ ∞) :
    KE g N c μ ≠ ∞ := by
  have hi := integrable_exp_of_succ (measurable_Wen hg μ) hc (integrable_exp_of_ne_top hg h)
  rw [KE_eq]
  exact hi.lintegral_lt_top.ne

theorem relEntropy_eq_aux (hg : Measurable g)
    (hI : Integrable (fun p : Torus d × Torus d => g (p.1 - p.2)) (μ.prod μ))
    (β β₀ : ℝ) (hβ₀ : 0 ≤ β₀) (hfin : KE g N β μ ≠ ∞) (hfin₀ : KE g N (β₀ + 1) μ ≠ ∞) :
    Integrable (Wen g N μ) (modulatedGibbs g N β₀ μ) ∧
      relEntropy (modulatedGibbs g N β₀ μ) (modulatedGibbs g N β μ) =
        ENNReal.ofReal ((β - β₀) * ∫ X, Wen g N μ X ∂(modulatedGibbs g N β₀ μ) +
          Real.log (KE g N β μ).toReal - Real.log (KE g N β₀ μ).toReal) := by
  set ν : Measure (Config d N) := Measure.pi fun _ : Fin N => μ with hν
  set W := Wen g N μ with hWdef
  have hW : Measurable W := measurable_Wen hg μ
  have hK0 : KE g N β₀ μ ≠ ∞ := KE_ne_top_of_succ hg hβ₀ hfin₀
  have hZβ := Zf_pos hg hfin
  have hZ0 := Zf_pos hg hK0
  have := isProb_modulatedGibbs hg hfin
  have := isProb_modulatedGibbs hg hK0
  have hWi : Integrable W ν := integrable_Wen hI
  have hexp1 : Integrable (fun X => Real.exp (-(β₀ + 1) * W X)) ν := integrable_exp_of_ne_top hg hfin₀
  have hWe : Integrable (fun X => W X * Real.exp (-β₀ * W X)) ν :=
    integrable_W_exp hW hWi hβ₀ hexp1
  have hQint : Integrable W (modulatedGibbs g N β₀ μ) := integrable_Wen_Q hg hZ0 hWe
  refine ⟨hQint, ?_⟩
  -- density
  set φ' : Config d N → ℝ≥0∞ := fun X =>
    ENNReal.ofReal (Zf ν W β / Zf ν W β₀) * ENNReal.ofReal (Real.exp ((β - β₀) * W X)) with hφ'
  have hφ'm : Measurable φ' :=
    measurable_const.mul (ENNReal.measurable_ofReal.comp
      (Real.measurable_exp.comp (measurable_const.mul hW)))
  have hmβ : Measurable (fun X : Config d N => ENNReal.ofReal (Real.exp (-β * W X))) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (measurable_const.mul hW))
  have hQ0eq : modulatedGibbs g N β₀ μ = (modulatedGibbs g N β μ).withDensity φ' := by
    rw [modulatedGibbs_eq, modulatedGibbs_eq, withDensity_smul_measure,
      ← withDensity_mul _ hmβ hφ'm]
    have hpt : (fun X => ENNReal.ofReal (Real.exp (-β * W X))) * φ' =
        ENNReal.ofReal (Zf ν W β / Zf ν W β₀) •
          fun X => ENNReal.ofReal (Real.exp (-β₀ * W X)) := by
      funext X
      simp only [Pi.mul_apply, Pi.smul_apply, hφ', smul_eq_mul]
      rw [mul_left_comm, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
      congr 3; ring
    rw [hpt, withDensity_smul' _ _ ENNReal.ofReal_ne_top, smul_smul]
    congr 1
    rw [ENNReal.ofReal_div_of_pos hZ0, div_eq_mul_inv, ← mul_assoc,
      ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.2 hZβ).ne' ENNReal.ofReal_ne_top, one_mul]
  have hac : modulatedGibbs g N β₀ μ ≪ modulatedGibbs g N β μ := by
    rw [hQ0eq]; exact withDensity_absolutelyContinuous _ _
  have hrn : (modulatedGibbs g N β₀ μ).rnDeriv (modulatedGibbs g N β μ) =ᵐ[modulatedGibbs g N β μ] φ' := by
    conv_lhs => rw [hQ0eq]
    exact Measure.rnDeriv_withDensity _ hφ'm
  have hllr : MeasureTheory.llr (modulatedGibbs g N β₀ μ) (modulatedGibbs g N β μ) =ᵐ[modulatedGibbs g N β₀ μ]
      fun X => Real.log (Zf ν W β / Zf ν W β₀) + (β - β₀) * W X := by
    filter_upwards [hac.ae_le hrn] with X hX
    unfold MeasureTheory.llr
    rw [hX, hφ']
    simp only
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (div_pos hZβ hZ0).le,
      ENNReal.toReal_ofReal (Real.exp_pos _).le, Real.log_mul (div_pos hZβ hZ0).ne' (Real.exp_pos _).ne',
      Real.log_exp]
  have hint : Integrable (MeasureTheory.llr (modulatedGibbs g N β₀ μ) (modulatedGibbs g N β μ))
      (modulatedGibbs g N β₀ μ) := by
    refine Integrable.congr ?_ hllr.symm
    exact (integrable_const _).add (hQint.const_mul _)
  unfold relEntropy
  rw [InformationTheory.klDiv_of_ac_of_integrable hac hint, integral_congr_ae hllr,
    integral_add (integrable_const _) (hQint.const_mul _), integral_const_mul, integral_const]
  simp only [Measure.real, measure_univ, ENNReal.toReal_one, smul_eq_mul, one_mul]
  congr 1
  rw [Real.log_div hZβ.ne' hZ0.ne', toReal_KE hg, toReal_KE hg]
  ring

end Gibbs




section Entropy

variable {d : ℕ} {g : Torus d → ℝ} {μ : Measure (Torus d)} [IsProbabilityMeasure μ] {N : ℕ}

/-- `E_{Q_c}[W] = (∫ W e^{-cW}) / Z(c)`. -/
theorem integral_Wen_Q (hg : Measurable g) (c : ℝ) :
    ∫ X, Wen g N μ X ∂(modulatedGibbs g N c μ) =
      (∫ X, Wen g N μ X * Real.exp (-c * Wen g N μ X) ∂(Measure.pi fun _ : Fin N => μ)) /
        Zf (Measure.pi fun _ : Fin N => μ) (Wen g N μ) c := by
  rw [integral_modulatedGibbs c hg, div_eq_inv_mul]
  congr 1
  exact integral_congr_ae (Filter.Eventually.of_forall fun X => mul_comm _ _)

theorem Zf_zero {α : Type*} [MeasurableSpace α] (ν : Measure α) [IsProbabilityMeasure ν] (W : α → ℝ) :
    Zf ν W 0 = 1 := by simp [Zf]

theorem log_Zf_ge (hg : Measurable g)
    (hI : Integrable (fun p : Torus d × Torus d => g (p.1 - p.2)) (μ.prod μ)) (hN : 1 ≤ N)
    {c : ℝ} (hK : KE g N c μ ≠ ∞) :
    c * ((∫ p : Torus d × Torus d, g (p.1 - p.2) ∂(μ.prod μ)) / 2) ≤
      Real.log (Zf (Measure.pi fun _ : Fin N => μ) (Wen g N μ) c) := by
  set ν : Measure (Config d N) := Measure.pi fun _ : Fin N => μ
  have hW := measurable_Wen (N := N) hg μ
  have h := tilt_jensen (ν := ν) (W := Wen g N μ) hW (c := 0) (t := c)
    (by simpa using integrable_const (1 : ℝ)) (by simpa using integrable_Wen hI)
    (by simpa using integrable_exp_of_ne_top hg hK)
  rw [Zf_zero] at h
  have hm : (∫ x, Wen g N μ x * Real.exp (-0 * Wen g N μ x) ∂ν) / 1 =
      -(1 / 2) * ∫ p : Torus d × Torus d, g (p.1 - p.2) ∂(μ.prod μ) := by
    simp only [neg_zero, zero_mul, Real.exp_zero, mul_one, div_one]
    exact integral_Wen hN hI
  rw [hm, zero_add] at h
  have hZpos := Zf_pos hg hK
  have h2 := Real.log_le_log one_pos h
  rw [Real.log_mul (Real.exp_pos _).ne' hZpos.ne', Real.log_exp] at h2
  simp only [Real.log_one] at h2
  linarith

theorem entropy_bound_aux (hg : Measurable g)
    (hI : Integrable (fun p : Torus d × Torus d => g (p.1 - p.2)) (μ.prod μ)) (hN : 1 ≤ N)
    (B Cp L : ℝ) (hB : 0 ≤ B) (hL : 1 ≤ L)
    (hpress : ∀ γ ∈ Set.Icc (0 : ℝ) (B + 1), KE g N γ μ ≤ ENNReal.ofReal (Real.exp (Cp * L)))
    (β : ℝ) (hβ : β ∈ Set.Icc (0 : ℝ) B) (β₀ : ℝ) (hβ₀ : β₀ ∈ Set.Icc (0 : ℝ) B) :
    relEntropy (modulatedGibbs g N β₀ μ) (modulatedGibbs g N β μ) ≤
      ENNReal.ofReal ((B * (|∫ p : Torus d × Torus d, g (p.1 - p.2) ∂(μ.prod μ)| / 2 +
          B * (|∫ p : Torus d × Torus d, g (p.1 - p.2) ∂(μ.prod μ)| / 2) + |Cp|) + |Cp| +
          B * (|∫ p : Torus d × Torus d, g (p.1 - p.2) ∂(μ.prod μ)| / 2)) * L) := by
  set ν : Measure (Config d N) := Measure.pi fun _ : Fin N => μ with hν
  set G := ∫ p : Torus d × Torus d, g (p.1 - p.2) ∂(μ.prod μ) with hG
  set A := |G| with hA
  have hW := measurable_Wen (N := N) hg μ
  have hA0 : 0 ≤ A := abs_nonneg _
  obtain ⟨hβ1, hβ2⟩ := hβ
  obtain ⟨hβ₀1, hβ₀2⟩ := hβ₀
  have hfin : ∀ γ ∈ Set.Icc (0 : ℝ) (B + 1), KE g N γ μ ≠ ∞ := fun γ hγ =>
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hpress γ hγ)
  have hlogle : ∀ γ ∈ Set.Icc (0 : ℝ) (B + 1),
      Real.log (Zf ν (Wen g N μ) γ) ≤ Cp * L := by
    intro γ hγ
    have hZ := Zf_pos hg (hfin γ hγ)
    have h1 : Zf ν (Wen g N μ) γ ≤ Real.exp (Cp * L) := by
      rw [← toReal_KE hg]
      calc (KE g N γ μ).toReal ≤ (ENNReal.ofReal (Real.exp (Cp * L))).toReal :=
            ENNReal.toReal_mono ENNReal.ofReal_ne_top (hpress γ hγ)
        _ = _ := ENNReal.toReal_ofReal (Real.exp_pos _).le
    calc Real.log (Zf ν (Wen g N μ) γ) ≤ Real.log (Real.exp (Cp * L)) := Real.log_le_log hZ h1
      _ = Cp * L := Real.log_exp _
  have hβmem : β ∈ Set.Icc (0 : ℝ) (B + 1) := ⟨hβ1, by linarith⟩
  have hβ₀mem : β₀ ∈ Set.Icc (0 : ℝ) (B + 1) := ⟨hβ₀1, by linarith⟩
  have hβ₀1mem : β₀ + 1 ∈ Set.Icc (0 : ℝ) (B + 1) := ⟨by linarith, by linarith⟩
  have hid := (relEntropy_eq_aux (N := N) hg hI β β₀ hβ₀1 (hfin β hβmem) (hfin _ hβ₀1mem)).2
  rw [hid, toReal_KE hg, toReal_KE hg]
  refine ENNReal.ofReal_le_ofReal ?_
  set m := ∫ X, Wen g N μ X ∂(modulatedGibbs g N β₀ μ) with hm
  have hZ0 := Zf_pos hg (hfin β₀ hβ₀mem)
  have hZ1 := Zf_pos hg (hfin _ hβ₀1mem)
  have hKm : KE g N β₀ μ ≠ ∞ := hfin β₀ hβ₀mem
  have hex0 : Integrable (fun X => Real.exp (-β₀ * Wen g N μ X)) ν := integrable_exp_of_ne_top hg hKm
  have hex1 : Integrable (fun X => Real.exp (-(β₀ + 1) * Wen g N μ X)) ν :=
    integrable_exp_of_ne_top hg (hfin _ hβ₀1mem)
  have hWi : Integrable (Wen g N μ) ν := integrable_Wen hI
  have hWe : Integrable (fun X => Wen g N μ X * Real.exp (-β₀ * Wen g N μ X)) ν :=
    integrable_W_exp hW hWi hβ₀1 hex1
  have hmdef : m = (∫ X, Wen g N μ X * Real.exp (-β₀ * Wen g N μ X) ∂ν) / Zf ν (Wen g N μ) β₀ :=
    integral_Wen_Q hg β₀
  -- lower bound of f(β₀)
  have hf0 := log_Zf_ge hg hI hN hKm
  rw [← hG] at hf0
  have hf0' : -(B * (A / 2)) ≤ Real.log (Zf ν (Wen g N μ) β₀) := by
    have : -(β₀ * (A / 2)) ≤ β₀ * (G / 2) := by
      have := neg_abs_le G
      nlinarith
    nlinarith
  -- lower bound of m
  have hmlow : -(B * (A / 2)) - Cp * L ≤ m := by
    have h := tilt_jensen (ν := ν) (W := Wen g N μ) hW (c := β₀) (t := 1) hex0 hWe
      (by simpa using hex1)
    rw [← hmdef] at h
    have h2 := Real.log_le_log hZ0 h
    rw [Real.log_mul (Real.exp_pos _).ne' (Zf_pos hg (hfin _ hβ₀1mem)).ne', Real.log_exp] at h2
    have h3 := hlogle _ hβ₀1mem
    simp only [one_mul] at h2
    linarith
  -- upper bound of m
  have hmup : m ≤ A / 2 := by
    rcases hβ₀1.eq_or_lt with h0 | hpos
    · subst h0
      rw [hmdef, Zf_zero]
      simp only [neg_zero, zero_mul, Real.exp_zero, mul_one, div_one]
      rw [integral_Wen hN hI]
      have := neg_abs_le G
      have := le_abs_self G
      linarith
    · have h := tilt_jensen (ν := ν) (W := Wen g N μ) hW (c := β₀) (t := -β₀) hex0 hWe
        (by simpa using (integrable_const (1 : ℝ)))
      rw [← hmdef] at h
      simp only [add_neg_cancel, Zf_zero, mul_one] at h
      have h2 := Real.log_le_log hZ0 h
      rw [Real.log_exp] at h2
      have h3 := log_Zf_ge hg hI hN hKm
      rw [← hG] at h3
      have : β₀ * m ≤ β₀ * (-(G / 2)) := by nlinarith
      have h4 : m ≤ -(G / 2) := le_of_mul_le_mul_left this hpos
      have := neg_abs_le G
      have := le_abs_self G
      linarith
  have hfβ := hlogle β hβmem
  have hf1 := hlogle _ hβ₀1mem
  have habs : |m| ≤ A / 2 + B * (A / 2) + |Cp| * L := by
    rw [abs_le]
    constructor
    · have : Cp * L ≤ |Cp| * L := mul_le_mul_of_nonneg_right (le_abs_self Cp) (by linarith)
      nlinarith
    · have : 0 ≤ B * (A / 2) := by positivity
      have : 0 ≤ |Cp| * L := by positivity
      linarith
  have hdiff : |β - β₀| ≤ B := by
    rw [abs_le]; constructor <;> linarith
  have hprod : (β - β₀) * m ≤ B * (A / 2 + B * (A / 2) + |Cp| * L) := by
    calc (β - β₀) * m ≤ |(β - β₀) * m| := le_abs_self _
      _ = |β - β₀| * |m| := abs_mul _ _
      _ ≤ B * (A / 2 + B * (A / 2) + |Cp| * L) :=
          mul_le_mul hdiff habs (abs_nonneg _) hB
  have hCpL : Cp * L ≤ |Cp| * L := mul_le_mul_of_nonneg_right (le_abs_self Cp) (by linarith)
  have hAB : 0 ≤ B * (A / 2) := by positivity
  have hCp0 : 0 ≤ |Cp| := abs_nonneg Cp
  have hB1 : 0 ≤ B * (A / 2 + B * (A / 2) + |Cp|) := by positivity
  -- final arithmetic
  have key : (β - β₀) * m + Real.log (Zf ν (Wen g N μ) β) - Real.log (Zf ν (Wen g N μ) β₀) ≤
      B * (A / 2 + B * (A / 2) + |Cp| * L) + |Cp| * L + B * (A / 2) := by
    linarith
  refine key.trans ?_
  have e1 : B * (A / 2 + B * (A / 2) + |Cp| * L) =
      B * (A / 2 + B * (A / 2)) + B * |Cp| * L := by ring
  have h5 : B * (A / 2 + B * (A / 2)) ≤ B * (A / 2 + B * (A / 2)) * L := by
    have : 0 ≤ B * (A / 2 + B * (A / 2)) := by positivity
    nlinarith
  have h6 : B * (A / 2) ≤ B * (A / 2) * L := by nlinarith
  nlinarith

end Entropy


theorem one_le_N_deltaN {s : ℝ} (hs0 : 0 ≤ s) (N : ℕ) (hN : 1 ≤ N) :
    1 ≤ (N : ℝ) * deltaN d s N := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  unfold deltaN
  split_ifs with h1 h2
  · rw [mul_inv_cancel₀ hNpos.ne']
  · rw [← mul_assoc, mul_inv_cancel₀ hNpos.ne', one_mul, Real.log_mul (Real.exp_pos _).ne' hNpos.ne',
      Real.log_exp]
    have := Real.log_nonneg hN1
    linarith
  · have hspos : 0 < s := by
      push Not at h1
      have : (0 : ℝ) ≤ (d : ℝ) / 2 := by positivity
      rcases lt_or_eq_of_le h1 with h | h
      · linarith
      · exact absurd h.symm h2
    have hs2 : (d : ℝ) / 2 < s := by
      push Not at h1
      exact lt_of_le_of_ne h1 (Ne.symm h2)
    have hds : (d : ℝ) / s ≤ 2 := by
      rw [div_le_iff₀ hspos]; linarith
    calc (1 : ℝ) ≤ (N : ℝ) ^ (2 - (d : ℝ) / s) := Real.one_le_rpow hN1 (by linarith)
      _ = (N : ℝ) * (N : ℝ) ^ (1 - (d : ℝ) / s) := by
          rw [show (2 - (d : ℝ) / s) = 1 + (1 - (d : ℝ) / s) by ring,
            Real.rpow_add hNpos, Real.rpow_one]



section Diverge

variable {d : ℕ}

theorem not_integrableOn_exp_rpow (hd : 1 ≤ d) {s : ℝ} (hs : 0 < s) (κ R ε : ℝ) (hκ : 0 < κ) (hε : 0 < ε) :
    ¬ IntegrableOn (fun w : Euc d => Real.exp (κ * (‖w‖ ^ (-s) - R))) (ball 0 ε) := by
  intro h
  have : Nontrivial (Euc d) := Module.nontrivial_of_finrank_pos (R := ℝ) (by simp; omega)
  have h1 := (integrableOn_fun_norm_addHaar (volume : Measure (Euc d))
    (f := fun t : ℝ => Real.exp (κ * (t ^ (-s) - R))) (r := ε)).1 h
  have hfin : Module.finrank ℝ (Euc d) = d := by simp
  rw [hfin] at h1
  -- choose m with s * m ≥ d
  obtain ⟨m, hm⟩ := exists_nat_ge ((d : ℝ) / s)
  have hsm : (d : ℝ) ≤ s * m := by
    rw [div_le_iff₀ hs] at hm; linarith
  -- lower bound
  set e : ℝ := (d : ℝ) - 1 - s * m with he
  have he1 : e ≤ -1 := by
    simp only [he]
    have : (1 : ℝ) ≤ 1 := le_refl _
    linarith
  have hbound : IntegrableOn (fun y : ℝ => y ^ e) (Ioo 0 ε) := by
    have hc : 0 < κ ^ m / (m.factorial : ℝ) * Real.exp (-(κ * R)) := by positivity
    have h2 : IntegrableOn (fun y : ℝ => (κ ^ m / (m.factorial : ℝ) * Real.exp (-(κ * R))) * y ^ e)
        (Ioo 0 ε) := by
      refine Integrable.mono' h1 ?_ ?_
      · exact ((measurable_const.mul (measurable_id.pow_const e))).aestronglyMeasurable
      · refine (ae_restrict_iff' measurableSet_Ioo).2 (Filter.Eventually.of_forall fun y hy => ?_)
        have hy0 : 0 < y := hy.1
        simp only [smul_eq_mul, Real.norm_eq_abs]
        rw [abs_of_nonneg (by positivity)]
        have hu : 0 ≤ κ * y ^ (-s) := by positivity
        have h3 := Real.pow_div_factorial_le_exp (κ * y ^ (-s)) hu m
        have h4 : (κ * y ^ (-s)) ^ m = κ ^ m * y ^ (-s * m) := by
          rw [mul_pow, ← Real.rpow_natCast (y ^ (-s)) m, ← Real.rpow_mul hy0.le]
        have h5 : y ^ (d - 1) * y ^ (-s * m) = y ^ e := by
          rw [← Real.rpow_natCast, ← Real.rpow_add hy0]
          congr 1
          simp only [he]
          have : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by
            rw [Nat.cast_sub hd]; simp
          rw [this]; ring
        have h6 : Real.exp (κ * (y ^ (-s) - R)) =
            Real.exp (κ * y ^ (-s)) * Real.exp (-(κ * R)) := by
          rw [← Real.exp_add]; congr 1; ring
        rw [h6]
        have h7 : (κ ^ m / (m.factorial : ℝ) * Real.exp (-(κ * R))) * y ^ e =
            y ^ (d - 1) * ((κ * y ^ (-s)) ^ m / (m.factorial : ℝ) * Real.exp (-(κ * R))) := by
          rw [h4, ← h5]; ring
        rw [h7]
        have h8 : 0 ≤ y ^ (d - 1) := by positivity
        calc y ^ (d - 1) * ((κ * y ^ (-s)) ^ m / (m.factorial : ℝ) * Real.exp (-(κ * R)))
            ≤ y ^ (d - 1) * (Real.exp (κ * y ^ (-s)) * Real.exp (-(κ * R))) := by
              gcongr
          _ = _ := by ring
    have := h2.const_mul (κ ^ m / (m.factorial : ℝ) * Real.exp (-(κ * R)))⁻¹
    refine IntegrableOn.congr_fun this (fun y _ => ?_) measurableSet_Ioo
    rw [← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul]
  have := (intervalIntegral.integrableOn_Ioo_rpow_iff hε).1 hbound
  linarith

theorem lintegral_ball_exp_rpow_eq_top (hd : 1 ≤ d) {s : ℝ} (hs : 0 < s) (κ R ε : ℝ) (hκ : 0 < κ)
    (hε : 0 < ε) :
    ∫⁻ w in ball (0 : Euc d) ε, ENNReal.ofReal (Real.exp (κ * (‖w‖ ^ (-s) - R))) = ⊤ := by
  by_contra hne
  have hm : Measurable (fun w : Euc d => Real.exp (κ * (‖w‖ ^ (-s) - R))) :=
    Real.measurable_exp.comp (measurable_const.mul ((measurable_norm.pow_const _).sub_const _))
  have := integrable_toReal_of_lintegral_ne_top (μ := (volume : Measure (Euc d)).restrict (ball 0 ε))
    (f := fun w : Euc d => ENNReal.ofReal (Real.exp (κ * (‖w‖ ^ (-s) - R))))
    (ENNReal.measurable_ofReal.comp hm).aemeasurable hne
  refine not_integrableOn_exp_rpow hd hs κ R ε hκ hε ?_
  have h2 : Integrable (fun w : Euc d => Real.exp (κ * (‖w‖ ^ (-s) - R)))
      ((volume : Measure (Euc d)).restrict (ball 0 ε)) := by
    simpa [ENNReal.toReal_ofReal (Real.exp_pos _).le] using this
  exact h2

/-- Transfer of a lower bound from a small Euclidean ball to the torus. -/
theorem lintegral_ball_le_torus (hd : 1 ≤ d) {ε : ℝ} (hε : ε ≤ 1 / 2) (f : Torus d → ℝ≥0∞)
    (Fw : Euc d → ℝ≥0∞)
    (hfF : ∀ w : Euc d, ‖w‖ < ε → w ≠ 0 → Fw w ≤ f (Torus.mk w)) :
    ∫⁻ w in ball (0 : Euc d) ε, Fw w ≤ ∫⁻ z : Torus d, f z := by
  have : Nontrivial (Euc d) := Module.nontrivial_of_finrank_pos (R := ℝ) (by simp; omega)
  rw [KernelAux.lintegral_torus_box f]
  have hmp := PiLp.volume_preserving_ofLp (Fin d)
  have hemb : MeasurableEmbedding (@WithLp.ofLp 2 (Fin d → ℝ)) :=
    (MeasurableEquiv.toLp 2 (Fin d → ℝ)).symm.measurableEmbedding
  have h1 := hmp.setLIntegral_comp_preimage_emb hemb (fun y => f (KernelAux.boxPt y)) (KernelAux.Box d)
  have hsub : ball (0 : Euc d) ε ⊆ (@WithLp.ofLp 2 (Fin d → ℝ)) ⁻¹' (KernelAux.Box d) := by
    intro w hw
    have hw' : ‖w‖ < ε := by simpa using hw
    intro i
    have : |w i| ≤ ‖w‖ := by
      have := PiLp.norm_apply_le w i
      simpa using this
    have h2 := abs_lt.1 (lt_of_le_of_lt this (hw'.trans_le hε))
    simp only [mem_Ioc]
    constructor <;> linarith [h2.1, h2.2]
  calc ∫⁻ w in ball (0 : Euc d) ε, Fw w
      ≤ ∫⁻ w in ball (0 : Euc d) ε, f (KernelAux.boxPt (@WithLp.ofLp 2 (Fin d → ℝ) w)) := by
        refine lintegral_mono_ae ?_
        have hne : ∀ᵐ w ∂(volume : Measure (Euc d)), w ≠ 0 := by
          rw [ae_iff]; simp
        filter_upwards [ae_restrict_mem measurableSet_ball, ae_restrict_of_ae hne] with w hw hw0
        exact hfF w (by simpa using hw) hw0
    _ ≤ ∫⁻ w in (@WithLp.ofLp 2 (Fin d → ℝ)) ⁻¹' (KernelAux.Box d),
          f (KernelAux.boxPt (@WithLp.ofLp 2 (Fin d → ℝ) w)) := lintegral_mono_set hsub
    _ = _ := h1

end Diverge



section Geometry

variable {d : ℕ}

theorem norm_coe_circle_le (t : ℝ) : ‖(t : UnitAddCircle)‖ ≤ |t| := by
  rw [UnitAddCircle.norm_eq]
  simpa using round_le t 0

theorem eucDist_sub_mk_le (x x₀ : Torus d) (w : Euc d) :
    Torus.eucDist (x - Torus.mk w) x₀ ≤ Torus.eucDist x x₀ + ‖w‖ := by
  set a : Euc d := WithLp.toLp 2 (fun i => ‖x i - x₀ i‖) with ha
  set b : Euc d := WithLp.toLp 2 (fun i => |w i|) with hb
  have hna : ‖a‖ = Torus.eucDist x x₀ := by
    rw [EuclideanSpace.norm_eq]; simp [ha, Torus.eucDist]
  have hnb : ‖b‖ = ‖w‖ := by
    rw [EuclideanSpace.norm_eq w, EuclideanSpace.norm_eq]; simp [hb]
  have hle : Torus.eucDist (x - Torus.mk w) x₀ ≤ ‖a + b‖ := by
    unfold Torus.eucDist
    rw [EuclideanSpace.norm_eq]
    refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun i _ => ?_)
    have h1 : ‖(x - Torus.mk w) i - x₀ i‖ ≤ ‖x i - x₀ i‖ + |w i| := by
      have : (x - Torus.mk w) i - x₀ i = (x i - x₀ i) - ((w i : ℝ) : UnitAddCircle) := by
        simp [Torus.mk]; abel
      rw [this]
      have h2 := norm_sub_le (x i - x₀ i) ((w i : ℝ) : UnitAddCircle)
      have h3 := norm_coe_circle_le (w i)
      linarith
    have hab : (a + b) i = ‖x i - x₀ i‖ + |w i| := by simp [ha, hb]
    rw [hab, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ (norm_nonneg _) h1 2
  calc _ ≤ ‖a + b‖ := hle
    _ ≤ ‖a‖ + ‖b‖ := norm_add_le _ _
    _ = _ := by rw [hna, hnb]

theorem continuous_eucDist (x₀ : Torus d) : Continuous (fun x : Torus d => Torus.eucDist x x₀) := by
  unfold Torus.eucDist
  refine Real.continuous_sqrt.comp (continuous_finsetSum _ fun i _ => ?_)
  exact ((continuous_norm.comp ((continuous_apply i).sub continuous_const))).pow 2

theorem eucDist_self (x : Torus d) : Torus.eucDist x x = 0 := by
  simp [Torus.eucDist]

end Geometry



section Sing

variable {d : ℕ}

theorem exists_sing_lower {s : ℝ} (hd : 2 ≤ d) (hs0 : 0 < s) (hsd : s < d) :
    ∃ (R δ : ℝ), 0 < δ ∧ ∀ w : Euc d, ‖w‖ < δ → w ≠ 0 →
      ‖w‖ ^ (-s) - R ≤ periodicRiesz d s (Torus.mk w) := by
  obtain ⟨r, δ, hδ, hr, hsing⟩ := periodicRiesz_local_singularity hd hs0 hsd
  have hrc : Continuous r := PoleCavityAux.continuous_of_lift' (show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift r) from hr).continuous
  have hbdd : BddBelow (Set.range r) := (isCompact_range hrc).bddBelow
  obtain ⟨b, hb⟩ := hbdd
  refine ⟨-b, δ, hδ, fun w hw hw0 => ?_⟩
  rw [hsing w hw hw0]
  have := hb ⟨Torus.mk w, rfl⟩
  linarith

theorem volume_pos_of_open (hd : 1 ≤ d) {U : Set (Torus d)} (hU : IsOpen U) (hne : U.Nonempty) :
    0 < (volume : Measure (Torus d)) U := by
  rw [Torus.volume_eq_pi_haar]
  exact hU.measure_pos _ hne

end Sing



section EnergyLower

variable {d : ℕ}

theorem energy_lower {g : Torus d → ℝ} {μ : Measure (Torus d)} {N : ℕ} (hN : 2 ≤ N)
    {B M : ℝ} (hB0 : 0 ≤ B) (hB : ∀ z, -B ≤ g z) (heven : ∀ z, g (-z) = g z)
    (hM : ∀ x, ∫ y, g (x - y) ∂μ ≤ M)
    (hD : -M ≤ ∫ x, ∫ y, g (x - y) ∂μ ∂μ) (X : Config d N) :
    g (X ⟨0, by omega⟩ - X ⟨1, by omega⟩) / (N : ℝ) ^ 2 - B / 2 - M - M / 2 ≤
      modulatedEnergyKernel g X μ := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  set i0 : Fin N := ⟨0, by omega⟩
  set i1 : Fin N := ⟨1, by omega⟩
  have hne : i0 ≠ i1 := by simp [i0, i1, Fin.ext_iff]
  -- pair sum
  have hP : 2 * g (X i0 - X i1) + 2 * B - B * ((N : ℝ) * ((N : ℝ) - 1)) ≤
      ∑ i, ∑ j ∈ Finset.univ.erase i, g (X i - X j) := by
    have hnn : ∀ i j, 0 ≤ g (X i - X j) + B := fun i j => by linarith [hB (X i - X j)]
    have h1 : (g (X i0 - X i1) + B) + (g (X i1 - X i0) + B) ≤
        ∑ i, ∑ j ∈ Finset.univ.erase i, (g (X i - X j) + B) := by
      have hin : ∀ i, 0 ≤ ∑ j ∈ Finset.univ.erase i, (g (X i - X j) + B) :=
        fun i => Finset.sum_nonneg fun j _ => hnn i j
      have ha : g (X i0 - X i1) + B ≤ ∑ j ∈ Finset.univ.erase i0, (g (X i0 - X j) + B) :=
        Finset.single_le_sum (f := fun j => g (X i0 - X j) + B) (fun j _ => hnn i0 j)
          (Finset.mem_erase.2 ⟨hne.symm, Finset.mem_univ _⟩)
      have hb : g (X i1 - X i0) + B ≤ ∑ j ∈ Finset.univ.erase i1, (g (X i1 - X j) + B) :=
        Finset.single_le_sum (f := fun j => g (X i1 - X j) + B) (fun j _ => hnn i1 j)
          (Finset.mem_erase.2 ⟨hne, Finset.mem_univ _⟩)
      calc _ ≤ ∑ j ∈ Finset.univ.erase i0, (g (X i0 - X j) + B) +
            ∑ j ∈ Finset.univ.erase i1, (g (X i1 - X j) + B) := add_le_add ha hb
        _ = ∑ i ∈ ({i0, i1} : Finset (Fin N)), ∑ j ∈ Finset.univ.erase i, (g (X i - X j) + B) := by
            rw [Finset.sum_pair hne]
        _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            (fun i _ _ => hin i)
    have h2 : ∑ i, ∑ j ∈ Finset.univ.erase i, (g (X i - X j) + B) =
        ∑ i, ∑ j ∈ Finset.univ.erase i, g (X i - X j) + B * ((N : ℝ) * ((N : ℝ) - 1)) := by
      simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _),
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [Nat.cast_sub (by omega : 1 ≤ N)]
      simp
      ring
    have h3 : g (X i1 - X i0) = g (X i0 - X i1) := by
      rw [← heven (X i0 - X i1)]; congr 1; abel
    rw [h2, h3] at h1
    linarith
  -- convolution sum
  have hC : ∑ i, ∫ y, g (X i - y) ∂μ ≤ N * M := by
    calc _ ≤ ∑ _i : Fin N, M := Finset.sum_le_sum fun i _ => hM (X i)
      _ = N * M := by simp
  unfold modulatedEnergyKernel modulatedEnergy
  have hN2 : (0 : ℝ) < 2 * (N : ℝ) ^ 2 := by positivity
  have e1 : (1 / (2 * (N : ℝ) ^ 2)) * (∑ i, ∑ j ∈ Finset.univ.erase i, g (X i - X j)) ≥
      (1 / (2 * (N : ℝ) ^ 2)) * (2 * g (X i0 - X i1) + 2 * B - B * ((N : ℝ) * ((N : ℝ) - 1))) :=
    mul_le_mul_of_nonneg_left hP (by positivity)
  have e2 : (1 / (N : ℝ)) * ∑ i, ∫ y, g (X i - y) ∂μ ≤ (1 / (N : ℝ)) * (N * M) :=
    mul_le_mul_of_nonneg_left hC (by positivity)
  have e3 : (1 / (N : ℝ)) * (N * M) = M := by field_simp
  have e4 : (1 / (2 * (N : ℝ) ^ 2)) * (2 * g (X i0 - X i1) + 2 * B - B * ((N : ℝ) * ((N : ℝ) - 1))) =
      g (X i0 - X i1) / (N : ℝ) ^ 2 + (2 * B - B * ((N : ℝ) * ((N : ℝ) - 1))) / (2 * (N : ℝ) ^ 2) := by
    field_simp
    ring
  have e5 : -(B / 2) ≤ (2 * B - B * ((N : ℝ) * ((N : ℝ) - 1))) / (2 * (N : ℝ) ^ 2) := by
    rw [le_div_iff₀ hN2]
    nlinarith [mul_nonneg hB0 (sq_nonneg (N : ℝ)), mul_nonneg hB0 hNpos.le]
  linarith

end EnergyLower




section Final

variable {d : ℕ}

theorem conv_bound {g : Torus d → ℝ} (hg : Measurable g) (hgi : Integrable g) (ρ : Torus d → ℝ)
    (Λ : ℝ) (hΛ : ∀ x, ρ x ≤ Λ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x : Torus d, |∫ y, g (x - y) ∂(withDensityReal ρ)| ≤ M := by
  set L : ℝ≥0∞ := ∫⁻ y, ENNReal.ofReal |g y| with hL
  have hLfin : L < ∞ := by
    have := hgi.norm.lintegral_lt_top
    simpa [hL] using this
  refine ⟨(ENNReal.ofReal Λ * L).toReal, ENNReal.toReal_nonneg, fun x => ?_⟩
  have h1 : |∫ y, g (x - y) ∂(withDensityReal ρ)| ≤ ∫ y, |g (x - y)| ∂(withDensityReal ρ) := by
    simpa [Real.norm_eq_abs] using
      norm_integral_le_integral_norm (μ := withDensityReal ρ) (fun y => g (x - y))
  refine h1.trans ?_
  have hm : Measurable (fun y : Torus d => |g (x - y)|) :=
    (hg.comp (measurable_const.sub measurable_id)).abs
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun y => abs_nonneg _)
    hm.aestronglyMeasurable]
  refine ENNReal.toReal_mono ?_ ?_
  · exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hLfin.ne
  · exact KernelAux2.lintegral_conv_le ρ Λ hΛ (fun z => ENNReal.ofReal |g z|) x

theorem inner_eq_top {s : ℝ} (hd : 2 ≤ d) (hs0 : 0 < s) (hsd : s < d) (ρ : Torus d → ℝ)
    (hρm : Measurable ρ) (x₀ : Torus d) (r c : ℝ) (hr : 0 < r) (hc : 0 < c)
    (hball : ∀ x, Torus.eucDist x x₀ < r → c ≤ ρ x) (κ : ℝ) (hκ : 0 < κ) (x : Torus d)
    (hx : Torus.eucDist x x₀ < r / 2) :
    ∫⁻ y, ENNReal.ofReal (Real.exp (κ * periodicRiesz d s (x - y))) ∂(withDensityReal ρ) = ⊤ := by
  have hg : Measurable (periodicRiesz d s) := PoleCavityAux.measurable_periodicRiesz hd hs0.le hsd
  obtain ⟨R, δ, hδ, hsing⟩ := exists_sing_lower hd hs0 hsd
  set ε : ℝ := min (min δ (1 / 2)) (r / 2) with hε
  have hε0 : 0 < ε := lt_min (lt_min hδ (by norm_num)) (by linarith)
  have hεδ : ε ≤ δ := (min_le_left _ _).trans (min_le_left _ _)
  have hε2 : ε ≤ 1 / 2 := (min_le_left _ _).trans (min_le_right _ _)
  have hεr : ε ≤ r / 2 := min_le_right _ _
  set Fx : Torus d → ℝ≥0∞ := fun y => ENNReal.ofReal (Real.exp (κ * periodicRiesz d s (x - y))) with hFx
  have hFxm : Measurable Fx :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
      (measurable_const.mul (hg.comp (measurable_const.sub measurable_id))))
  set Bs : Set (Torus d) := {y | Torus.eucDist y x₀ < r} with hBs
  have hBsm : MeasurableSet Bs :=
    (isOpen_lt (continuous_eucDist x₀) continuous_const).measurableSet
  -- step 1: pass to volume
  have hρ' : Measurable (fun y => ENNReal.ofReal (ρ y)) := ENNReal.measurable_ofReal.comp hρm
  have e1 : ∫⁻ y, Fx y ∂(withDensityReal ρ) = ∫⁻ y, ENNReal.ofReal (ρ y) * Fx y := by
    unfold withDensityReal
    exact lintegral_withDensity_eq_lintegral_mul _ hρ' hFxm
  -- step 2: lower bound by indicator
  set f₂ : Torus d → ℝ≥0∞ := fun z =>
    {z : Torus d | x - z ∈ Bs}.indicator
      (fun z => ENNReal.ofReal c * ENNReal.ofReal (Real.exp (κ * periodicRiesz d s z))) z with hf₂
  have h2 : ∀ y, f₂ (x - y) ≤ ENNReal.ofReal (ρ y) * Fx y := by
    intro y
    simp only [hf₂, hFx, Set.indicator, Set.mem_ofPred_eq, sub_sub_cancel]
    split_ifs with h
    · exact mul_le_mul' (ENNReal.ofReal_le_ofReal (hball y h)) le_rfl
    · exact bot_le
  have h3 : ∫⁻ y, f₂ (x - y) = ∫⁻ z, f₂ z := KernelAux2.lintegral_sub_left_torus f₂ x
  -- step 3: ball integral
  have h4 : ∫⁻ w in ball (0 : Euc d) ε,
      ENNReal.ofReal c * ENNReal.ofReal (Real.exp (κ * (‖w‖ ^ (-s) - R))) ≤ ∫⁻ z, f₂ z := by
    refine lintegral_ball_le_torus (by omega) hε2 f₂ _ fun w hw hw0 => ?_
    have hgw := hsing w (hw.trans_le hεδ) hw0
    have hmem : x - Torus.mk w ∈ Bs := by
      show Torus.eucDist (x - Torus.mk w) x₀ < r
      have := eucDist_sub_mk_le x x₀ w
      linarith
    simp only [hf₂, Set.indicator, Set.mem_ofPred_eq, hmem, ite_true]
    exact mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2
      (mul_le_mul_of_nonneg_left hgw hκ.le)))
  have h5 : ∫⁻ w in ball (0 : Euc d) ε,
      ENNReal.ofReal c * ENNReal.ofReal (Real.exp (κ * (‖w‖ ^ (-s) - R))) = ⊤ := by
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      lintegral_ball_exp_rpow_eq_top (by omega) hs0 κ R ε hκ hε0]
    exact ENNReal.mul_top (ENNReal.ofReal_pos.2 hc).ne'
  rw [e1]
  refine eq_top_iff.2 ?_
  calc (⊤ : ℝ≥0∞) = ∫⁻ w in ball (0 : Euc d) ε,
      ENNReal.ofReal c * ENNReal.ofReal (Real.exp (κ * (‖w‖ ^ (-s) - R))) := h5.symm
    _ ≤ ∫⁻ z, f₂ z := h4
    _ = ∫⁻ y, f₂ (x - y) := h3.symm
    _ ≤ _ := lintegral_mono h2

theorem KE_neg_eq_top {s : ℝ} (hd : 2 ≤ d) (hs0 : 0 < s) (hsd : s < d)
    (ρ : Torus d → ℝ) (hρ : IsProbDensity ρ) (Λ : ℝ) (hΛ : ∀ x, ρ x ≤ Λ) (x₀ : Torus d)
    (r c : ℝ) (hr : 0 < r) (hc : 0 < c) (hball : ∀ x, Torus.eucDist x x₀ < r → c ≤ ρ x)
    (a : ℝ) (ha : 0 < a) (N : ℕ) (hN : 2 ≤ N) :
    KE (periodicRiesz d s) N (-a) (withDensityReal ρ) = ∞ := by
  set g := periodicRiesz d s with hgdef
  set μ := withDensityReal ρ with hμ
  haveI : IsProbabilityMeasure μ := isProb_withDensityReal hρ
  have hg : Measurable g := PoleCavityAux.measurable_periodicRiesz hd hs0.le hsd
  have hgi : Integrable g := KernelAux.integrable_periodicRiesz hd hs0.le hsd
  obtain ⟨B0, hB0⟩ := periodicRiesz_ge (d := d) (s := s) hd hs0.le hsd
  have hB : ∀ z, -|B0| ≤ g z := fun z => by
    have := hB0 z; have := le_abs_self B0; linarith
  obtain ⟨M, hM0, hM⟩ := conv_bound hg hgi ρ Λ hΛ
  have hD : -M ≤ ∫ x, ∫ y, g (x - y) ∂μ ∂μ := by
    have h := norm_integral_le_of_norm_le_const (μ := μ) (f := fun x => ∫ y, g (x - y) ∂μ) (C := M)
      (Filter.Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hM x)
    simp only [Measure.real, measure_univ, ENNReal.toReal_one, mul_one] at h
    exact (abs_le.1 (by simpa [Real.norm_eq_abs] using h)).1
  have hev : ∀ z, g (-z) = g z := fun z => periodicRiesz_neg z
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  set i0 : Fin N := ⟨0, by omega⟩
  set i1 : Fin N := ⟨1, by omega⟩
  have hne : i0 ≠ i1 := by simp [i0, i1, Fin.ext_iff]
  set κ : ℝ := a / N with hκ
  have hκ0 : 0 < κ := by positivity
  set K0 : ℝ := a * N * (|B0| / 2 + M + M / 2) with hK0
  set ν : Measure (Config d N) := Measure.pi fun _ : Fin N => μ with hν
  have hpt : ∀ X : Config d N, κ * g (X i0 - X i1) - K0 ≤ -(-a) * N * modulatedEnergyKernel g X μ := by
    intro X
    have h := energy_lower (μ := μ) hN (abs_nonneg B0) hB hev
      (fun x => le_trans (le_abs_self _) (hM x)) hD X
    have h2 : a * N * (g (X i0 - X i1) / (N : ℝ) ^ 2 - |B0| / 2 - M - M / 2) ≤
        a * N * modulatedEnergyKernel g X μ := mul_le_mul_of_nonneg_left h (by positivity)
    have h3 : a * N * (g (X i0 - X i1) / (N : ℝ) ^ 2 - |B0| / 2 - M - M / 2) =
        κ * g (X i0 - X i1) - K0 := by
      simp only [hκ, hK0]; field_simp; ring
    rw [h3] at h2
    simpa using h2
  set Ψ : Torus d × Torus d → ℝ≥0∞ := fun p => ENNReal.ofReal (Real.exp (κ * g (p.1 - p.2))) with hΨ
  have hΨm : Measurable Ψ :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
      (measurable_const.mul (hg.comp (measurable_fst.sub measurable_snd))))
  -- lower bound by pair integral
  have step1 : ENNReal.ofReal (Real.exp (-K0)) * ∫⁻ p, Ψ p ∂(μ.prod μ) ≤ KE g N (-a) μ := by
    have hmap : ∫⁻ p, Ψ p ∂(μ.prod μ) = ∫⁻ X, Ψ (X i0, X i1) ∂ν := by
      rw [← pi_map_pair μ hne, lintegral_map hΨm
        ((measurable_pi_apply i0).prodMk (measurable_pi_apply i1))]
    rw [hmap, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, KE_eq]
    refine lintegral_mono fun X => ?_
    simp only [hΨ]
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
    have := hpt X
    have hW : a * Wen g N μ X = a * N * modulatedEnergyKernel g X μ := by
      simp only [Wen]; ring
    simp only [neg_neg] at this ⊢
    linarith
  -- the pair integral is infinite
  set U : Set (Torus d) := {x | Torus.eucDist x x₀ < r / 2} with hU
  have hUo : IsOpen U := isOpen_lt (continuous_eucDist x₀) continuous_const
  have hUne : U.Nonempty := ⟨x₀, by simp [hU, eucDist_self]; linarith⟩
  have hρm : Measurable ρ := hρ.measurable
  have hμU : μ U ≠ 0 := by
    have hvol := volume_pos_of_open (by omega) hUo hUne
    have h1 : ENNReal.ofReal c * volume U ≤ μ U := by
      rw [hμ, withDensityReal, withDensity_apply _ hUo.measurableSet]
      calc ENNReal.ofReal c * volume U = ∫⁻ _x in U, ENNReal.ofReal c := by
            rw [setLIntegral_const]
        _ ≤ _ := by
            refine setLIntegral_mono' hUo.measurableSet fun x hx => ?_
            exact ENNReal.ofReal_le_ofReal (hball x (lt_of_lt_of_le hx (by linarith)))
    refine fun h0 => ?_
    rw [h0] at h1
    have := le_antisymm h1 bot_le
    rcases mul_eq_zero.1 this with h | h
    · exact (ENNReal.ofReal_pos.2 hc).ne' h
    · exact hvol.ne' h
  have step2 : ∫⁻ p, Ψ p ∂(μ.prod μ) = ⊤ := by
    rw [lintegral_prod _ hΨm.aemeasurable]
    refine eq_top_iff.2 ?_
    calc (⊤ : ℝ≥0∞) = ∫⁻ x, U.indicator (fun _ => (⊤ : ℝ≥0∞)) x ∂μ := by
          rw [lintegral_indicator_const hUo.measurableSet]
          exact (ENNReal.top_mul hμU).symm
      _ ≤ _ := by
          refine lintegral_mono fun x => ?_
          by_cases hx : x ∈ U
          · rw [Set.indicator_of_mem hx]
            exact (inner_eq_top hd hs0 hsd ρ hρm x₀ r c hr hc hball κ hκ0 x hx).ge
          · rw [Set.indicator_of_notMem hx]; exact bot_le
  rw [step2, ENNReal.mul_top (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne'] at step1
  exact top_le_iff.1 step1

end Final




section Uniform

variable {d : ℕ} {g : Torus d → ℝ} {μ : Measure (Torus d)} [IsProbabilityMeasure μ] {N : ℕ}

/-- `Q_{β₀} = Q_β.withDensity (K_β/K_{β₀} e^{(β-β₀)W})`. -/
theorem gibbs_eq_withDensity (hg : Measurable g) {β β₀ : ℝ} (hfin : KE g N β μ ≠ ∞)
    (hfin₀ : KE g N β₀ μ ≠ ∞) :
    modulatedGibbs g N β₀ μ = (modulatedGibbs g N β μ).withDensity
      (fun X => ENNReal.ofReal (Zf (Measure.pi fun _ : Fin N => μ) (Wen g N μ) β /
          Zf (Measure.pi fun _ : Fin N => μ) (Wen g N μ) β₀) *
        ENNReal.ofReal (Real.exp ((β - β₀) * Wen g N μ X))) := by
  set ν : Measure (Config d N) := Measure.pi fun _ : Fin N => μ with hν
  set W := Wen g N μ with hWdef
  have hW : Measurable W := measurable_Wen hg μ
  have hZβ := Zf_pos hg hfin
  have hZ0 := Zf_pos hg hfin₀
  set φ' : Config d N → ℝ≥0∞ := fun X =>
    ENNReal.ofReal (Zf ν W β / Zf ν W β₀) * ENNReal.ofReal (Real.exp ((β - β₀) * W X)) with hφ'
  have hφ'm : Measurable φ' :=
    measurable_const.mul (ENNReal.measurable_ofReal.comp
      (Real.measurable_exp.comp (measurable_const.mul hW)))
  have hmβ : Measurable (fun X : Config d N => ENNReal.ofReal (Real.exp (-β * W X))) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (measurable_const.mul hW))
  show modulatedGibbs g N β₀ μ = (modulatedGibbs g N β μ).withDensity φ'
  rw [modulatedGibbs_eq, modulatedGibbs_eq, withDensity_smul_measure,
    ← withDensity_mul _ hmβ hφ'm]
  have hpt : (fun X => ENNReal.ofReal (Real.exp (-β * W X))) * φ' =
      ENNReal.ofReal (Zf ν W β / Zf ν W β₀) •
        fun X => ENNReal.ofReal (Real.exp (-β₀ * W X)) := by
    funext X
    simp only [Pi.mul_apply, Pi.smul_apply, hφ', smul_eq_mul]
    rw [mul_left_comm, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    congr 3; ring
  rw [hpt, withDensity_smul' _ _ ENNReal.ofReal_ne_top, smul_smul]
  congr 1
  rw [ENNReal.ofReal_div_of_pos hZ0, div_eq_mul_inv, ← mul_assoc,
    ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.2 hZβ).ne' ENNReal.ofReal_ne_top, one_mul]

theorem lintegral_rnDeriv_rpow (hg : Measurable g) {β β₀ p : ℝ} (hp : 1 ≤ p)
    (hfin : KE g N β μ ≠ ∞) (hfin₀ : KE g N β₀ μ ≠ ∞) :
    modulatedGibbs g N β₀ μ ≪ modulatedGibbs g N β μ ∧
      ∫⁻ X, ((modulatedGibbs g N β₀ μ).rnDeriv (modulatedGibbs g N β μ) X) ^ p
          ∂(modulatedGibbs g N β μ) =
        (ENNReal.ofReal (Zf (Measure.pi fun _ : Fin N => μ) (Wen g N μ) β))⁻¹ *
          (ENNReal.ofReal ((Zf (Measure.pi fun _ : Fin N => μ) (Wen g N μ) β /
              Zf (Measure.pi fun _ : Fin N => μ) (Wen g N μ) β₀) ^ p) *
            ∫⁻ X, ENNReal.ofReal (Real.exp (-(β - p * (β - β₀)) * Wen g N μ X))
              ∂(Measure.pi fun _ : Fin N => μ)) := by
  set ν : Measure (Config d N) := Measure.pi fun _ : Fin N => μ with hν
  set W := Wen g N μ with hWdef
  have hW : Measurable W := measurable_Wen hg μ
  have hZβ := Zf_pos hg hfin
  have hZ0 := Zf_pos hg hfin₀
  have hQ0eq := gibbs_eq_withDensity (N := N) hg hfin hfin₀
  have := isProb_modulatedGibbs hg hfin
  set φ' : Config d N → ℝ≥0∞ := fun X =>
    ENNReal.ofReal (Zf ν W β / Zf ν W β₀) * ENNReal.ofReal (Real.exp ((β - β₀) * W X)) with hφ'
  have hφ'm : Measurable φ' :=
    measurable_const.mul (ENNReal.measurable_ofReal.comp
      (Real.measurable_exp.comp (measurable_const.mul hW)))
  have hmβ : Measurable (fun X : Config d N => ENNReal.ofReal (Real.exp (-β * W X))) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (measurable_const.mul hW))
  refine ⟨?_, ?_⟩
  · rw [hQ0eq]; exact withDensity_absolutelyContinuous _ _
  · have hrn : (modulatedGibbs g N β₀ μ).rnDeriv (modulatedGibbs g N β μ) =ᵐ[modulatedGibbs g N β μ] φ' := by
      conv_lhs => rw [hQ0eq]
      exact Measure.rnDeriv_withDensity _ hφ'm
    rw [lintegral_congr_ae (hrn.mono fun X hX => by rw [hX])]
    rw [modulatedGibbs_eq β, lintegral_smul_measure]
    have hm2 : Measurable (fun X => φ' X ^ p) := hφ'm.pow_const p
    rw [lintegral_withDensity_eq_lintegral_mul _ hmβ hm2]
    congr 1
    have : ∀ X : Config d N, (ENNReal.ofReal (Real.exp (-β * W X)) * φ' X ^ p) =
        ENNReal.ofReal ((Zf ν W β / Zf ν W β₀) ^ p) *
          ENNReal.ofReal (Real.exp (-(β - p * (β - β₀)) * W X)) := by
      intro X
      simp only [hφ']
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by linarith),
        ENNReal.ofReal_rpow_of_nonneg (div_pos hZβ hZ0).le (by linarith),
        ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le (by linarith),
        ← Real.exp_mul, mul_left_comm, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
      congr 3; ring
    simp only [Pi.mul_apply, this]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

theorem real_ineq {Zb Zb0 Zg Cp m p : ℝ} (hZb : 0 < Zb) (hm : 0 < m) (hZb0 : m ≤ Zb0) (hp : 1 ≤ p)
    (hZb' : Zb ≤ Cp) (hZg0 : 0 < Zg) (hZg : Zg ≤ Cp) :
    Zb⁻¹ * ((Zb / Zb0) ^ p * Zg) ≤ Cp ^ (p - 1) * Cp / m ^ p := by
  have hZb0pos : 0 < Zb0 := lt_of_lt_of_le hm hZb0
  have hCp : 0 < Cp := lt_of_lt_of_le hZb hZb'
  rw [Real.div_rpow hZb.le hZb0pos.le]
  have h1 : Zb⁻¹ * (Zb ^ p / Zb0 ^ p * Zg) = Zb ^ (p - 1) * Zg / Zb0 ^ p := by
    rw [Real.rpow_sub_one hZb.ne']; field_simp
  rw [h1]
  have h2 : Zb ^ (p - 1) ≤ Cp ^ (p - 1) := Real.rpow_le_rpow hZb.le hZb' (by linarith)
  have h3 : m ^ p ≤ Zb0 ^ p := Real.rpow_le_rpow hm.le hZb0 (by linarith)
  have h4 : 0 < m ^ p := Real.rpow_pos_of_pos hm p
  have h5 : 0 < Cp ^ (p - 1) := Real.rpow_pos_of_pos hCp _
  rw [div_le_div_iff₀ (lt_of_lt_of_le h4 h3) h4]
  calc Zb ^ (p - 1) * Zg * m ^ p ≤ Cp ^ (p - 1) * Cp * Zb0 ^ p := by
        have := mul_le_mul h2 hZg hZg0.le h5.le
        exact mul_le_mul this h3 h4.le (by positivity)
    _ = _ := by ring

theorem uniform_of_small_negative (hg : Measurable g)
    (hI : Integrable (fun p : Torus d × Torus d => g (p.1 - p.2)) (μ.prod μ))
    (hT1 : ∃ a : ℝ, 0 < a ∧ ∀ B₀ : ℝ, ∃ C : ℝ, ∀ N : ℕ, 2 ≤ N → ∀ γ ∈ Set.Icc (-a) B₀,
      KE g N γ μ ≤ ENNReal.ofReal C) (B B₀ : ℝ) :
    ∃ p : ℝ, 1 < p ∧ ∃ C : ℝ, ∀ N : ℕ, 2 ≤ N → ∀ β ∈ Set.Icc (0 : ℝ) B,
      ∀ β₀ ∈ Set.Icc (0 : ℝ) B₀,
        modulatedGibbs g N β₀ μ ≪ modulatedGibbs g N β μ ∧
          ∫⁻ X, ((modulatedGibbs g N β₀ μ).rnDeriv (modulatedGibbs g N β μ) X) ^ p
              ∂(modulatedGibbs g N β μ) ≤ ENNReal.ofReal C := by
  obtain ⟨a, ha, hC⟩ := hT1
  set q : ℝ := a / (2 * (|B| + 1)) with hq
  have hq0 : 0 < q := by positivity
  set p : ℝ := 1 + q with hp
  have hp1 : 1 < p := by linarith
  set B₁ : ℝ := p * |B₀| + |B| with hB₁
  obtain ⟨C₁, hC₁⟩ := hC B₁
  set G := ∫ p : Torus d × Torus d, g (p.1 - p.2) ∂(μ.prod μ) with hG
  set m : ℝ := Real.exp (-(|B₀| * |G| / 2)) with hm
  have hm0 : 0 < m := Real.exp_pos _
  set Cp : ℝ := max C₁ 1 with hCp
  have hCp1 : 1 ≤ Cp := le_max_right _ _
  refine ⟨p, hp1, Cp ^ (p - 1) * Cp / m ^ p, fun N hN β hβ β₀ hβ₀ => ?_⟩
  obtain ⟨hβ1, hβ2⟩ := hβ
  obtain ⟨hβ₀1, hβ₀2⟩ := hβ₀
  have hB0abs : 0 ≤ |B₀| := abs_nonneg _
  have hBabs : 0 ≤ |B| := abs_nonneg _
  have hp0 : 0 ≤ p := by linarith
  -- range facts
  have hpB : 0 ≤ p * |B₀| := by positivity
  have hβB1 : β ∈ Set.Icc (-a) B₁ := ⟨by linarith, by have := le_abs_self B; linarith⟩
  have hβ₀B1 : β₀ ∈ Set.Icc (-a) B₁ := ⟨by linarith, by
    have h1 := le_abs_self B₀
    have h2 : |B₀| ≤ p * |B₀| := by nlinarith
    linarith⟩
  have hγ : β - p * (β - β₀) ∈ Set.Icc (-a) B₁ := by
    have e : β - p * (β - β₀) = p * β₀ - q * β := by rw [hp]; ring
    rw [e]
    constructor
    · have h1 : q * β ≤ q * |B| := mul_le_mul_of_nonneg_left (hβ2.trans (le_abs_self B)) hq0.le
      have h2 : q * |B| ≤ a := by
        rw [hq]
        rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
        nlinarith
      have h3 : 0 ≤ p * β₀ := by positivity
      linarith
    · have h1 : p * β₀ ≤ p * |B₀| := mul_le_mul_of_nonneg_left (hβ₀2.trans (le_abs_self B₀)) hp0
      have h2 : 0 ≤ q * β := by positivity
      linarith
  have hfin : ∀ γ ∈ Set.Icc (-a) B₁, KE g N γ μ ≠ ∞ := fun γ hγ =>
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hC₁ N hN γ hγ)
  have hZle : ∀ γ ∈ Set.Icc (-a) B₁, Zf (Measure.pi fun _ : Fin N => μ) (Wen g N μ) γ ≤ Cp := by
    intro γ hγ
    rw [← toReal_KE hg]
    calc (KE g N γ μ).toReal ≤ (ENNReal.ofReal C₁).toReal :=
          ENNReal.toReal_mono ENNReal.ofReal_ne_top (hC₁ N hN γ hγ)
      _ = max C₁ 0 := ENNReal.toReal_ofReal' 
      _ ≤ Cp := max_le_max le_rfl zero_le_one
  have hf0 := log_Zf_ge hg hI (by omega : 1 ≤ N) (hfin β₀ hβ₀B1)
  rw [← hG] at hf0
  have hZ0ge : m ≤ Zf (Measure.pi fun _ : Fin N => μ) (Wen g N μ) β₀ := by
    have hZpos := Zf_pos hg (hfin β₀ hβ₀B1)
    have h1 : -(|B₀| * |G| / 2) ≤ Real.log (Zf (Measure.pi fun _ : Fin N => μ) (Wen g N μ) β₀) := by
      have h2 : -(β₀ * (|G| / 2)) ≤ β₀ * (G / 2) := by
        have := neg_abs_le G
        nlinarith
      have h3 : β₀ * (|G| / 2) ≤ |B₀| * |G| / 2 := by
        have := hβ₀2.trans (le_abs_self B₀)
        have : 0 ≤ |G| := abs_nonneg _
        nlinarith
      linarith
    calc m = Real.exp (-(|B₀| * |G| / 2)) := rfl
      _ ≤ Real.exp (Real.log _) := Real.exp_le_exp.2 h1
      _ = _ := Real.exp_log hZpos
  obtain ⟨hac, hint⟩ := lintegral_rnDeriv_rpow (N := N) hg hp1.le (hfin β hβB1) (hfin β₀ hβ₀B1)
  refine ⟨hac, ?_⟩
  rw [hint, ← KE_eq]
  have hKγ : KE g N (β - p * (β - β₀)) μ =
      ENNReal.ofReal (Zf (Measure.pi fun _ : Fin N => μ) (Wen g N μ) (β - p * (β - β₀))) := by
    rw [← toReal_KE hg, ENNReal.ofReal_toReal (hfin _ hγ)]
  have hZb := Zf_pos hg (hfin β hβB1)
  have hZg := Zf_pos hg (hfin _ hγ)
  have hZ0pos : 0 < Zf (Measure.pi fun _ : Fin N => μ) (Wen g N μ) β₀ := lt_of_lt_of_le hm0 hZ0ge
  rw [hKγ, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_inv_of_pos hZb,
    ← ENNReal.ofReal_mul (by positivity)]
  exact ENNReal.ofReal_le_ofReal
    (real_ineq hZb hm0 hZ0ge hp1.le (hZle β hβB1) hZg (hZle _ hγ))

theorem integrable_pair_withDensity {g : Torus d → ℝ} (hg : Measurable g) (hgi : Integrable g)
    (ρ : Torus d → ℝ) (Λ : ℝ) (hΛ : ∀ x, ρ x ≤ Λ) {ν : Measure (Torus d)} (hν : ν = withDensityReal ρ)
    [IsProbabilityMeasure ν] :
    Integrable (fun p : Torus d × Torus d => g (p.1 - p.2)) (ν.prod ν) := by
  subst hν
  refine ⟨(hg.comp (measurable_fst.sub measurable_snd)).aestronglyMeasurable, ?_⟩
  have hL : ∫⁻ y, ‖g y‖ₑ < ∞ := hgi.2
  unfold HasFiniteIntegral
  have hm : Measurable (fun p : Torus d × Torus d => ‖g (p.1 - p.2)‖ₑ) :=
    (hg.comp (measurable_fst.sub measurable_snd)).enorm
  show ∫⁻ p : Torus d × Torus d, ‖g (p.1 - p.2)‖ₑ ∂(withDensityReal ρ).prod (withDensityReal ρ) < ∞
  rw [lintegral_prod _ hm.aemeasurable]
  calc ∫⁻ x, ∫⁻ y, ‖g (x - y)‖ₑ ∂withDensityReal ρ ∂withDensityReal ρ
      ≤ ∫⁻ _x, (ENNReal.ofReal Λ * ∫⁻ y, ‖g y‖ₑ) ∂withDensityReal ρ :=
        lintegral_mono fun x => KernelAux2.lintegral_conv_le ρ Λ hΛ (fun z => ‖g z‖ₑ) x
    _ = ENNReal.ofReal Λ * ∫⁻ y, ‖g y‖ₑ := by rw [lintegral_const, measure_univ, mul_one]
    _ < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hL

end Uniform


end HRS.PreparationAux
