import HRS.Whole.Bias

/-!
# HRS.MS.WrCavAux1 -- cavity and pole laws on `Euc d`: potential bound, tilt calculus, well-definedness (WR-13a, part 1)

Packet WR-13a (T7 of `docs/WR_B_PLAN.md`), first helper file.  Everything is for the Euclidean kernel
`g = rieszKernel d s` with `0 < s < d` and a probability density `ρ ≤ M` (no lower bound on `ρ`).

* `wr13a_potential_bound`: `g*μ ≤ potentialBound d s M` and `0 ≤ g*μ`, with integrability of `g(x-·)`, for the whole range
  `0 < s < d` (the `d/2 < s` hypothesis of `Bias.convolution_bounded_potential` is not needed).
* the exponents `wr13a_E` (cavity weight) and `wr13a_Ep` (cavity weight times pole tilt) with their `Fin.cons`
  splittings, the upper bound `exp Ep(cons y Y) ≤ exp(β Mg) exp(-tλ g(x-y)) exp Ep(Y)` and the Jensen lower bound
  `∫ exp Ep (m+1 particles) ≥ exp(-λ (t+m) Mg) ∫ exp Ep (m particles)`;
* `wr13a_tilt`, the normalised exponential tilt, and the identifications `cavityLaw = wr13a_tilt ..`,
  `poleLaw = wr13a_tilt ..`;
* `wr13a_cavityWellDefined`: `CavityWellDefined d s N β μ x t` for `β ≥ 0`, `t ≥ 0` (no Jensen is needed for positivity;
  the Jensen bound is used for the uniform constants in `WrCavAux2`).

Helper lemmas carry the prefix `wr13a_`.  No frozen file is edited.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open MeasureTheory
open scoped ENNReal BigOperators

noncomputable section

namespace HRS.MS.Wr

open HRS.Whole

variable {d : ℕ} {s : ℝ}

/-! ### The kernel -/

theorem wr13a_g_nonneg (hs0 : 0 < s) (z : Euc d) : 0 ≤ rieszKernel d s z := by
  rw [Q34.rieszKernel_eq hs0.ne']
  exact Real.rpow_nonneg (norm_nonneg _) _

theorem wr13a_g_meas (hs0 : 0 < s) : Measurable (rieszKernel d s) :=
  Q34.measurable_rieszKernel hs0.ne'

theorem wr13a_g_sub_swap (z y : Euc d) : rieszKernel d s (y - z) = rieszKernel d s (z - y) := by
  rw [← neg_sub z y]
  exact rieszKernel_neg _

/-- Item 1: `0 ≤ g*μ ≤ M_g` for all `0 < s < d`, and `g(x-·)` is `μ`-integrable. -/
theorem wr13a_potential_bound (hd : 1 ≤ d) (hs0 : 0 < s) (hsd : s < d) {ρ : Euc d → ℝ}
    (hρ : HRS.Whole.IsProbDensity ρ) {M : ℝ} (hM : ∀ x, ρ x ≤ M) (x : Euc d) :
    Integrable (fun y => rieszKernel d s (x - y)) (HRS.Whole.withDensityReal ρ) ∧
      0 ≤ HRS.Whole.convMeasure (rieszKernel d s) (HRS.Whole.withDensityReal ρ) x ∧
      HRS.Whole.convMeasure (rieszKernel d s) (HRS.Whole.withDensityReal ρ) x ≤ potentialBound d s M := by
  have hM0 : 0 ≤ M := (hρ.nonneg 0).trans (hM 0)
  have hL := Q34.lintegral_kernel_le hd hs0 hsd hρ hM x
  have hrk : ∀ z : Euc d, rieszKernel d s z = ‖z‖ ^ (-s) := Q34.rieszKernel_eq hs0.ne'
  have hnn : ∀ y : Euc d, 0 ≤ rieszKernel d s (x - y) := fun y => wr13a_g_nonneg hs0 _
  have hmeas : Measurable (fun y : Euc d => rieszKernel d s (x - y)) :=
    (wr13a_g_meas hs0).comp (measurable_const.sub measurable_id)
  have hpos : 0 ≤ M * sphereArea d / ((d : ℝ) - s) + 1 := by
    have := Q34.sphereArea_nonneg hd
    have : 0 < (d : ℝ) - s := by linarith
    positivity
  have hL' : ∫⁻ y, ENNReal.ofReal (rieszKernel d s (x - y)) ∂(HRS.Whole.withDensityReal ρ) ≤
      ENNReal.ofReal (M * sphereArea d / ((d : ℝ) - s) + 1) := by
    simpa only [hrk] using hL
  obtain ⟨hi, hb⟩ := Q34.integrable_of_lintegral_le hmeas hnn hpos hL'
  exact ⟨hi, integral_nonneg hnn, hb⟩

theorem wr13a_conv_meas (hs0 : 0 < s) (μ : Measure (Euc d)) [SFinite μ] :
    Measurable (HRS.Whole.convMeasure (rieszKernel d s) μ) := by
  unfold HRS.Whole.convMeasure
  have : StronglyMeasurable (Function.uncurry fun x y : Euc d => rieszKernel d s (x - y)) :=
    ((wr13a_g_meas hs0).comp (measurable_fst.sub measurable_snd)).stronglyMeasurable
  exact (this.integral_prod_right' (ν := μ)).measurable

theorem wr13a_conv_nonneg (hs0 : 0 < s) (μ : Measure (Euc d)) (x : Euc d) :
    0 ≤ HRS.Whole.convMeasure (rieszKernel d s) μ x :=
  integral_nonneg fun y => wr13a_g_nonneg hs0 _

/-! ### Splitting off a coordinate -/

theorem wr13a_lintegral_pi_succ {E : Type*} [MeasurableSpace E] (μ : Measure E) [SigmaFinite μ] {n : ℕ}
    (F : (Fin (n + 1) → E) → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ X, F X ∂(Measure.pi fun _ : Fin (n + 1) => μ) =
      ∫⁻ x, ∫⁻ Y, F (Fin.cons x Y) ∂(Measure.pi fun _ : Fin n => μ) ∂μ := by
  have e := (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μ) 0).symm
  have h1 := e.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _) F
  rw [← h1]
  have hm : Measurable fun p : E × (Fin n → E) =>
      F ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => E) 0).symm p) :=
    hF.comp (MeasurableEquiv.measurable _)
  rw [lintegral_prod _ hm.aemeasurable]
  congr 1
  funext x
  congr 1
  funext Y
  congr 1
  rw [MeasurableEquiv.piFinSuccAbove_symm_apply]
  exact Fin.insertNth_zero' x Y

/-! ### Exponents -/

/-- `∑_{i<j} g(y_i - y_j)`. -/
def wr13a_pairSum (g : Euc d → ℝ) {n : ℕ} (Y : EucConfig d n) : ℝ :=
  ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j), g (Y i - Y j)

/-- The exponent `-λ ∑_{i<j} g(y_i-y_j) + β ∑_i (g*μ)(y_i)` of the cavity weight. -/
def wr13a_E (d : ℕ) (s : ℝ) (μ : Measure (Euc d)) (lam β : ℝ) {n : ℕ} (Y : EucConfig d n) : ℝ :=
  -lam * wr13a_pairSum (rieszKernel d s) Y + β * ∑ i, HRS.Whole.convMeasure (rieszKernel d s) μ (Y i)

/-- The exponent of cavity weight times the pole tilt `e^{-tλ ∑_i g(x - y_i)}`. -/
def wr13a_Ep (d : ℕ) (s : ℝ) (μ : Measure (Euc d)) (lam β : ℝ) (x : Euc d) (t : ℝ) {n : ℕ}
    (Y : EucConfig d n) : ℝ :=
  wr13a_E d s μ lam β Y - t * lam * ∑ i, rieszKernel d s (x - Y i)

theorem wr13a_pairSum_cons (g : Euc d → ℝ) {n : ℕ} (x : Euc d) (Y : EucConfig d n) :
    wr13a_pairSum g (Fin.cons x Y : EucConfig d (n + 1)) = ∑ j, g (x - Y j) + wr13a_pairSum g Y := by
  unfold wr13a_pairSum
  rw [Fin.sum_univ_succ]
  congr 1
  · rw [Finset.sum_filter, Fin.sum_univ_succ]
    simp
  · refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Fin.cons_succ]
    rw [Finset.sum_filter, Finset.sum_filter, Fin.sum_univ_succ]
    simp

theorem wr13a_E_cons (μ : Measure (Euc d)) (lam β : ℝ) {n : ℕ} (y : Euc d) (Y : EucConfig d n) :
    wr13a_E d s μ lam β (Fin.cons y Y : EucConfig d (n + 1)) =
      (β * HRS.Whole.convMeasure (rieszKernel d s) μ y - lam * ∑ j, rieszKernel d s (y - Y j)) +
        wr13a_E d s μ lam β Y := by
  unfold wr13a_E
  rw [wr13a_pairSum_cons, Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
  ring

theorem wr13a_Ep_cons (μ : Measure (Euc d)) (lam β : ℝ) (x : Euc d) (t : ℝ) {n : ℕ} (y : Euc d)
    (Y : EucConfig d n) :
    wr13a_Ep d s μ lam β x t (Fin.cons y Y : EucConfig d (n + 1)) =
      (β * HRS.Whole.convMeasure (rieszKernel d s) μ y - lam * ∑ j, rieszKernel d s (y - Y j)
          - t * lam * rieszKernel d s (x - y)) + wr13a_Ep d s μ lam β x t Y := by
  unfold wr13a_Ep
  rw [wr13a_E_cons, Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
  ring

theorem wr13a_Ep_zero (μ : Measure (Euc d)) (lam β : ℝ) (x : Euc d) {n : ℕ} (Y : EucConfig d n) :
    wr13a_Ep d s μ lam β x 0 Y = wr13a_E d s μ lam β Y := by
  simp [wr13a_Ep]

theorem wr13a_pairSum_meas {g : Euc d → ℝ} (hg : Measurable g) {n : ℕ} :
    Measurable (fun Y : EucConfig d n => wr13a_pairSum g Y) := by
  unfold wr13a_pairSum
  refine Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ => ?_
  exact hg.comp ((measurable_pi_apply i).sub (measurable_pi_apply j))

theorem wr13a_E_meas (hs0 : 0 < s) (μ : Measure (Euc d)) [SFinite μ] (lam β : ℝ) {n : ℕ} :
    Measurable (fun Y : EucConfig d n => wr13a_E d s μ lam β Y) := by
  unfold wr13a_E
  exact ((wr13a_pairSum_meas (wr13a_g_meas hs0)).const_mul _).add
    ((Finset.measurable_sum _ fun i _ =>
      (wr13a_conv_meas hs0 μ).comp (measurable_pi_apply i)).const_mul _)

theorem wr13a_Ep_meas (hs0 : 0 < s) (μ : Measure (Euc d)) [SFinite μ] (lam β : ℝ) (x : Euc d) (t : ℝ)
    {n : ℕ} : Measurable (fun Y : EucConfig d n => wr13a_Ep d s μ lam β x t Y) := by
  unfold wr13a_Ep
  exact (wr13a_E_meas hs0 μ lam β).sub
    ((Finset.measurable_sum _ fun i _ =>
      (wr13a_g_meas hs0).comp (measurable_const.sub (measurable_pi_apply i))).const_mul _)


/-! ### Bounds -/

section Bounds

variable {μ : Measure (Euc d)} {Mg lam β t : ℝ}

theorem wr13a_pairSum_nonneg (hs0 : 0 < s) {n : ℕ} (Y : EucConfig d n) :
    0 ≤ wr13a_pairSum (rieszKernel d s) Y :=
  Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => wr13a_g_nonneg hs0 _

theorem wr13a_sum_conv_le (hconv : ∀ z, HRS.Whole.convMeasure (rieszKernel d s) μ z ≤ Mg) {n : ℕ}
    (Y : EucConfig d n) : ∑ i, HRS.Whole.convMeasure (rieszKernel d s) μ (Y i) ≤ n * Mg := by
  have h1 : ∑ i, HRS.Whole.convMeasure (rieszKernel d s) μ (Y i) ≤ ∑ _i : Fin n, Mg :=
    Finset.sum_le_sum fun i _ => hconv _
  simpa using h1

theorem wr13a_sum_g_nonneg (hs0 : 0 < s) (x : Euc d) {n : ℕ} (Y : EucConfig d n) :
    0 ≤ ∑ i, rieszKernel d s (x - Y i) :=
  Finset.sum_nonneg fun i _ => wr13a_g_nonneg hs0 _

theorem wr13a_Ep_le (hs0 : 0 < s) (hconv : ∀ z, HRS.Whole.convMeasure (rieszKernel d s) μ z ≤ Mg)
    (hlam : 0 ≤ lam) (hβ : 0 ≤ β) (ht : 0 ≤ t) (x : Euc d) {n : ℕ} (Y : EucConfig d n) :
    wr13a_Ep d s μ lam β x t Y ≤ β * n * Mg := by
  unfold wr13a_Ep wr13a_E
  have h1 := wr13a_pairSum_nonneg hs0 Y
  have h2 := wr13a_sum_conv_le hconv Y
  have h3 := wr13a_sum_g_nonneg hs0 x Y
  have h4 : 0 ≤ lam * wr13a_pairSum (rieszKernel d s) Y := mul_nonneg hlam h1
  have h5 : 0 ≤ t * lam * ∑ i, rieszKernel d s (x - Y i) := mul_nonneg (mul_nonneg ht hlam) h3
  have h6 : β * ∑ i, HRS.Whole.convMeasure (rieszKernel d s) μ (Y i) ≤ β * (n * Mg) :=
    mul_le_mul_of_nonneg_left h2 hβ
  nlinarith

theorem wr13a_Ep_cons_le (hs0 : 0 < s) (hconv : ∀ z, HRS.Whole.convMeasure (rieszKernel d s) μ z ≤ Mg)
    (hlam : 0 ≤ lam) (hβ : 0 ≤ β) (x y : Euc d) {n : ℕ} (Y : EucConfig d n) :
    wr13a_Ep d s μ lam β x t (Fin.cons y Y : EucConfig d (n + 1)) ≤
      β * Mg - t * lam * rieszKernel d s (x - y) + wr13a_Ep d s μ lam β x t Y := by
  rw [wr13a_Ep_cons]
  have h1 : 0 ≤ lam * ∑ j, rieszKernel d s (y - Y j) :=
    mul_nonneg hlam (Finset.sum_nonneg fun j _ => wr13a_g_nonneg hs0 _)
  have h2 : β * HRS.Whole.convMeasure (rieszKernel d s) μ y ≤ β * Mg :=
    mul_le_mul_of_nonneg_left (hconv y) hβ
  linarith

/-! ### Jensen -/

theorem wr13a_jensen {α : Type*} [MeasurableSpace α] (P : Measure α) [IsProbabilityMeasure P]
    {u : α → ℝ} (hu : Integrable u P) (hu0 : ∀ a, 0 ≤ u a) {K : ℝ} (hK : ∫ a, u a ∂P ≤ K) :
    Real.exp (-K) ≤ ∫ a, Real.exp (-u a) ∂P := by
  have hI : Integrable (fun a => Real.exp (-K) * ((1 + K) - u a)) P :=
    (integrable_const _ |>.sub hu).const_mul _
  have hbound : ∀ a, Real.exp (-K) * ((1 + K) - u a) ≤ Real.exp (-u a) := by
    intro a
    have h := Real.add_one_le_exp (K - u a)
    have : Real.exp (-u a) = Real.exp (-K) * Real.exp (K - u a) := by
      rw [← Real.exp_add]; ring_nf
    rw [this]
    exact mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos _).le
  have hJ : Integrable (fun a => Real.exp (-u a)) P := by
    refine Integrable.of_bound (C := 1)
      (Real.continuous_exp.comp_aestronglyMeasurable hu.aestronglyMeasurable.neg)
      (Filter.Eventually.of_forall fun a => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.2 (by linarith [hu0 a])
  have := integral_mono hI hJ hbound
  have h2 : ∫ a, Real.exp (-K) * ((1 + K) - u a) ∂P = Real.exp (-K) * ((1 + K) - ∫ a, u a ∂P) := by
    rw [integral_const_mul, integral_sub (integrable_const _) hu]
    simp
  rw [h2] at this
  refine le_trans ?_ this
  have : (1 + K) - ∫ a, u a ∂P ≥ 1 := by linarith
  nlinarith [Real.exp_pos (-K)]

end Bounds


/-! ### The Jensen lower step -/

section Step

variable {μ : Measure (Euc d)} [IsProbabilityMeasure μ] {Mg lam β t : ℝ}

theorem wr13a_u_integral (hs0 : 0 < s) (hint : ∀ z, Integrable (fun y => rieszKernel d s (z - y)) μ)
    (hconv : ∀ z, HRS.Whole.convMeasure (rieszKernel d s) μ z ≤ Mg) (hlam : 0 ≤ lam) (ht : 0 ≤ t)
    (x : Euc d) {m : ℕ} (Y : EucConfig d m) :
    Integrable (fun y => lam * ∑ j, rieszKernel d s (y - Y j) + t * lam * rieszKernel d s (x - y)) μ ∧
    ∫ y, (lam * ∑ j, rieszKernel d s (y - Y j) + t * lam * rieszKernel d s (x - y)) ∂μ ≤
      lam * (t + m) * Mg := by
  have hj : ∀ j, Integrable (fun y => rieszKernel d s (y - Y j)) μ := fun j => by
    have : (fun y => rieszKernel d s (y - Y j)) = fun y => rieszKernel d s (Y j - y) :=
      funext fun y => wr13a_g_sub_swap _ _
    rw [this]; exact hint _
  have h1 : Integrable (fun y => lam * ∑ j, rieszKernel d s (y - Y j)) μ :=
    (integrable_finset_sum _ fun j _ => hj j).const_mul _
  have h2 : Integrable (fun y => t * lam * rieszKernel d s (x - y)) μ := (hint x).const_mul _
  refine ⟨h1.add h2, ?_⟩
  rw [integral_add h1 h2, integral_const_mul, integral_const_mul, integral_finset_sum _ fun j _ => hj j]
  have hc : ∀ j, ∫ y, rieszKernel d s (y - Y j) ∂μ = HRS.Whole.convMeasure (rieszKernel d s) μ (Y j) :=
    fun j => by
      unfold HRS.Whole.convMeasure
      exact integral_congr_ae (Filter.Eventually.of_forall fun y => wr13a_g_sub_swap _ _)
  simp_rw [hc]
  have h3 := wr13a_sum_conv_le hconv Y
  have h4 : ∫ y, rieszKernel d s (x - y) ∂μ ≤ Mg := hconv x
  have h5 : lam * ∑ j, HRS.Whole.convMeasure (rieszKernel d s) μ (Y j) ≤ lam * (m * Mg) :=
    mul_le_mul_of_nonneg_left h3 hlam
  have h6 : t * lam * ∫ y, rieszKernel d s (x - y) ∂μ ≤ t * lam * Mg :=
    mul_le_mul_of_nonneg_left h4 (mul_nonneg ht hlam)
  nlinarith

theorem wr13a_lower_step (hs0 : 0 < s) (hint : ∀ z, Integrable (fun y => rieszKernel d s (z - y)) μ)
    (hconv : ∀ z, HRS.Whole.convMeasure (rieszKernel d s) μ z ≤ Mg) (hlam : 0 ≤ lam) (hβ : 0 ≤ β)
    (ht : 0 ≤ t) (x : Euc d) (m : ℕ) :
    ENNReal.ofReal (Real.exp (-(lam * (t + m) * Mg))) *
        ∫⁻ Y, ENNReal.ofReal (Real.exp (wr13a_Ep d s μ lam β x t Y))
          ∂(Measure.pi fun _ : Fin m => μ) ≤
      ∫⁻ Y, ENNReal.ofReal (Real.exp (wr13a_Ep d s μ lam β x t Y))
        ∂(Measure.pi fun _ : Fin (m + 1) => μ) := by
  have hgm : Measurable (rieszKernel d s) := wr13a_g_meas hs0
  have hFm : Measurable fun Y : EucConfig d (m + 1) =>
      ENNReal.ofReal (Real.exp (wr13a_Ep d s μ lam β x t Y)) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (wr13a_Ep_meas hs0 μ lam β x t))
  have hCm : Measurable fun Y : EucConfig d m =>
      ENNReal.ofReal (Real.exp (wr13a_Ep d s μ lam β x t Y)) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (wr13a_Ep_meas hs0 μ lam β x t))
  rw [wr13a_lintegral_pi_succ μ _ hFm]
  set u : Euc d → EucConfig d m → ℝ := fun y Y =>
    lam * ∑ j, rieszKernel d s (y - Y j) + t * lam * rieszKernel d s (x - y) with hu
  have hu2 : Measurable (fun p : EucConfig d m × Euc d => u p.2 p.1) :=
    ((Finset.measurable_sum _ fun j _ =>
      hgm.comp (measurable_snd.sub ((measurable_pi_apply j).comp measurable_fst))).const_mul _).add
      ((hgm.comp (measurable_const.sub measurable_snd)).const_mul _)
  have hu1 : ∀ Y : EucConfig d m, Measurable (fun y => u y Y) := fun Y =>
    ((Finset.measurable_sum _ fun j _ =>
      hgm.comp (measurable_id.sub measurable_const)).const_mul _).add
      ((hgm.comp (measurable_const.sub measurable_id)).const_mul _)
  have hKJ : ∀ Y : EucConfig d m, ENNReal.ofReal (Real.exp (-(lam * (t + m) * Mg))) ≤
      ∫⁻ y, ENNReal.ofReal (Real.exp (-(u y Y))) ∂μ := by
    intro Y
    obtain ⟨hui, huK⟩ := wr13a_u_integral hs0 hint hconv hlam ht x Y
    have hu0 : ∀ y, 0 ≤ u y Y := fun y => by
      simp only [hu]
      exact add_nonneg (mul_nonneg hlam (Finset.sum_nonneg fun j _ => wr13a_g_nonneg hs0 _))
        (mul_nonneg (mul_nonneg ht hlam) (wr13a_g_nonneg hs0 _))
    have hj := wr13a_jensen μ hui hu0 huK
    have hint2 : Integrable (fun y => Real.exp (-(u y Y))) μ :=
      Integrable.of_bound (C := 1) ((Real.measurable_exp.comp (hu1 Y).neg).aestronglyMeasurable)
        (Filter.Eventually.of_forall fun y => by
          rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
          exact Real.exp_le_one_iff.2 (by linarith [hu0 y]))
    calc ENNReal.ofReal (Real.exp (-(lam * (t + m) * Mg))) ≤
          ENNReal.ofReal (∫ y, Real.exp (-(u y Y)) ∂μ) := ENNReal.ofReal_le_ofReal hj
      _ = _ := ofReal_integral_eq_lintegral_ofReal hint2
          (Filter.Eventually.of_forall fun y => (Real.exp_pos _).le)
  calc ENNReal.ofReal (Real.exp (-(lam * (t + m) * Mg))) *
        ∫⁻ Y, ENNReal.ofReal (Real.exp (wr13a_Ep d s μ lam β x t Y))
          ∂(Measure.pi fun _ : Fin m => μ)
      = ∫⁻ Y, ENNReal.ofReal (Real.exp (-(lam * (t + m) * Mg))) *
          ENNReal.ofReal (Real.exp (wr13a_Ep d s μ lam β x t Y))
          ∂(Measure.pi fun _ : Fin m => μ) := (lintegral_const_mul _ hCm).symm
    _ ≤ ∫⁻ Y, (∫⁻ y, ENNReal.ofReal (Real.exp (-(u y Y))) ∂μ) *
          ENNReal.ofReal (Real.exp (wr13a_Ep d s μ lam β x t Y))
          ∂(Measure.pi fun _ : Fin m => μ) :=
        lintegral_mono fun Y => mul_le_mul_left (hKJ Y) _
    _ = ∫⁻ Y, ∫⁻ y, ENNReal.ofReal (Real.exp (-(u y Y))) *
          ENNReal.ofReal (Real.exp (wr13a_Ep d s μ lam β x t Y)) ∂μ
          ∂(Measure.pi fun _ : Fin m => μ) := by
        refine lintegral_congr fun Y => ?_
        have hf : Measurable fun y => ENNReal.ofReal (Real.exp (-(u y Y))) :=
          ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (hu1 Y).neg)
        rw [lintegral_mul_const _ hf]
    _ = ∫⁻ y, ∫⁻ Y, ENNReal.ofReal (Real.exp (-(u y Y))) *
          ENNReal.ofReal (Real.exp (wr13a_Ep d s μ lam β x t Y))
          ∂(Measure.pi fun _ : Fin m => μ) ∂μ := by
        rw [lintegral_lintegral_swap]
        exact ((ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp hu2.neg)).mul
          (hCm.comp measurable_fst)).aemeasurable
    _ ≤ ∫⁻ y, ∫⁻ Y, ENNReal.ofReal (Real.exp (wr13a_Ep d s μ lam β x t
          (Fin.cons y Y : EucConfig d (m + 1)))) ∂(Measure.pi fun _ : Fin m => μ) ∂μ := by
        refine lintegral_mono fun y => lintegral_mono fun Y => ?_
        rw [wr13a_Ep_cons, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
        refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
        have := mul_nonneg hβ (wr13a_conv_nonneg hs0 μ y)
        simp only [hu]
        linarith

end Step


/-! ### Normalised exponential tilts -/

/-- `P` tilted by `exp w` and normalised (the normaliser is the `ℝ≥0∞`-valued integral, so a
non-integrable weight gives the zero measure, never a junk positive multiple). -/
def wr13a_tilt {α : Type*} [MeasurableSpace α] (P : Measure α) (w : α → ℝ) : Measure α :=
  (∫⁻ a, ENNReal.ofReal (Real.exp (w a)) ∂P)⁻¹ •
    P.withDensity fun a => ENNReal.ofReal (Real.exp (w a))

theorem wr13a_tilt_ne {α : Type*} [MeasurableSpace α] (P : Measure α) [IsProbabilityMeasure P]
    {w : α → ℝ} (hw : Measurable w) {W : ℝ} (hW : ∀ a, w a ≤ W) :
    (∫⁻ a, ENNReal.ofReal (Real.exp (w a)) ∂P) ≠ 0 ∧ (∫⁻ a, ENNReal.ofReal (Real.exp (w a)) ∂P) ≠ ∞ := by
  have hZfin : (∫⁻ a, ENNReal.ofReal (Real.exp (w a)) ∂P) ≠ ∞ := by
    apply ne_of_lt
    calc (∫⁻ a, ENNReal.ofReal (Real.exp (w a)) ∂P) ≤ ∫⁻ _a, ENNReal.ofReal (Real.exp W) ∂P :=
          lintegral_mono fun a => ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (hW a))
      _ = ENNReal.ofReal (Real.exp W) := by simp
      _ < ∞ := ENNReal.ofReal_lt_top
  refine ⟨?_, hZfin⟩
  intro h0
  have hm : Measurable fun a => ENNReal.ofReal (Real.exp (w a)) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp hw)
  rw [lintegral_eq_zero_iff hm] at h0
  have h1 : ∀ᵐ a ∂P, False := h0.mono fun a ha => by
    have := (ENNReal.ofReal_eq_zero.1 ha)
    exact absurd this (not_le.2 (Real.exp_pos _))
  obtain ⟨a, ha⟩ := h1.exists
  exact ha

theorem wr13a_tilt_isProb {α : Type*} [MeasurableSpace α] (P : Measure α) [IsProbabilityMeasure P]
    {w : α → ℝ} (hw : Measurable w) {W : ℝ} (hW : ∀ a, w a ≤ W) :
    IsProbabilityMeasure (wr13a_tilt P w) := by
  obtain ⟨h0, h1⟩ := wr13a_tilt_ne P hw hW
  refine ⟨?_⟩
  unfold wr13a_tilt
  rw [Measure.smul_apply, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, smul_eq_mul]
  exact ENNReal.inv_mul_cancel h0 h1

theorem wr13a_lintegral_tilt {α : Type*} [MeasurableSpace α] (P : Measure α) {w : α → ℝ}
    (hw : Measurable w) (F : α → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ a, F a ∂(wr13a_tilt P w) =
      (∫⁻ a, ENNReal.ofReal (Real.exp (w a)) ∂P)⁻¹ *
        ∫⁻ a, F a * ENNReal.ofReal (Real.exp (w a)) ∂P := by
  have hm : Measurable fun a => ENNReal.ofReal (Real.exp (w a)) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp hw)
  unfold wr13a_tilt
  rw [lintegral_smul_measure, lintegral_withDensity_eq_lintegral_mul _ hm hF, smul_eq_mul]
  congr 1
  refine lintegral_congr fun a => ?_
  rw [Pi.mul_apply, mul_comm]


/-! ### `cavityLaw` and `poleLaw` as tilts -/

section Laws

variable {μ : Measure (Euc d)} [IsProbabilityMeasure μ] {Mg β t : ℝ}

theorem wr13a_cavityWeight_eq (N : ℕ) (Y : EucConfig d (N - 1)) :
    cavityWeight d s N β μ Y = Real.exp (wr13a_E d s μ (β / N) β Y) := rfl

theorem wr13a_poleWeight_eq (N : ℕ) (x : Euc d) (t : ℝ) (Y : EucConfig d (N - 1)) :
    poleWeight d s N β x t Y = Real.exp (-(t * (β / N)) * ∑ i, rieszKernel d s (x - Y i)) := rfl

theorem wr13a_exp_Ep (N : ℕ) (x : Euc d) (t : ℝ) (Y : EucConfig d (N - 1)) :
    Real.exp (wr13a_Ep d s μ (β / N) β x t Y) =
      Real.exp (wr13a_E d s μ (β / N) β Y) * poleWeight d s N β x t Y := by
  rw [wr13a_poleWeight_eq, ← Real.exp_add]
  congr 1
  unfold wr13a_Ep
  ring

theorem wr13a_E_le (hs0 : 0 < s) (hconv : ∀ z, HRS.Whole.convMeasure (rieszKernel d s) μ z ≤ Mg)
    {lam : ℝ} (hlam : 0 ≤ lam) (hβ : 0 ≤ β) {n : ℕ} (Y : EucConfig d n) :
    wr13a_E d s μ lam β Y ≤ β * n * Mg := by
  have := wr13a_Ep_le hs0 hconv hlam hβ (le_refl (0 : ℝ)) (0 : Euc d) Y
  rwa [wr13a_Ep_zero] at this

theorem wr13a_cavityWeight_integrable (hs0 : 0 < s)
    (hconv : ∀ z, HRS.Whole.convMeasure (rieszKernel d s) μ z ≤ Mg) (hβ : 0 ≤ β) (N : ℕ) :
    Integrable (fun Y : EucConfig d (N - 1) => Real.exp (wr13a_E d s μ (β / N) β Y))
      (Measure.pi fun _ : Fin (N - 1) => μ) := by
  have hlam : 0 ≤ β / N := div_nonneg hβ (Nat.cast_nonneg _)
  have hEm := wr13a_E_meas hs0 μ (β / N) β (n := N - 1)
  exact Integrable.of_bound (C := Real.exp (β * ((N - 1 : ℕ) : ℝ) * Mg))
      (Real.measurable_exp.comp hEm).aestronglyMeasurable
      (Filter.Eventually.of_forall fun Y => by
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        exact Real.exp_le_exp.2 (wr13a_E_le hs0 hconv hlam hβ Y))

theorem wr13a_ofReal_cavityNormalizer (hs0 : 0 < s)
    (hconv : ∀ z, HRS.Whole.convMeasure (rieszKernel d s) μ z ≤ Mg) (hβ : 0 ≤ β) (N : ℕ) :
    ENNReal.ofReal (cavityNormalizer d s N β μ) =
      ∫⁻ Y, ENNReal.ofReal (Real.exp (wr13a_E d s μ (β / N) β Y))
        ∂(Measure.pi fun _ : Fin (N - 1) => μ) :=
  ofReal_integral_eq_lintegral_ofReal (wr13a_cavityWeight_integrable hs0 hconv hβ N)
    (Filter.Eventually.of_forall fun Y => (Real.exp_pos _).le)

theorem wr13a_cavityLaw_eq (hs0 : 0 < s)
    (hconv : ∀ z, HRS.Whole.convMeasure (rieszKernel d s) μ z ≤ Mg) (hβ : 0 ≤ β) (N : ℕ) :
    HRS.Whole.cavityLaw d s N β μ =
      wr13a_tilt (Measure.pi fun _ : Fin (N - 1) => μ) (wr13a_E d s μ (β / N) β) := by
  have hZ := wr13a_ofReal_cavityNormalizer hs0 hconv hβ N
  unfold HRS.Whole.cavityLaw wr13a_tilt
  rw [hZ]
  rfl

theorem wr13a_cavityLaw_isProb (hs0 : 0 < s)
    (hconv : ∀ z, HRS.Whole.convMeasure (rieszKernel d s) μ z ≤ Mg) (hβ : 0 ≤ β) (N : ℕ) :
    IsProbabilityMeasure (HRS.Whole.cavityLaw d s N β μ) := by
  have hlam : 0 ≤ β / N := div_nonneg hβ (Nat.cast_nonneg _)
  rw [wr13a_cavityLaw_eq hs0 hconv hβ N]
  exact wr13a_tilt_isProb _ (wr13a_E_meas hs0 μ (β / N) β)
    (fun Y => wr13a_E_le hs0 hconv hlam hβ Y)

theorem wr13a_poleWeight_pos (N : ℕ) (x : Euc d) (t : ℝ) (Y : EucConfig d (N - 1)) :
    0 < poleWeight d s N β x t Y := Real.exp_pos _

theorem wr13a_poleWeight_le_one (hs0 : 0 < s) (hβ : 0 ≤ β) (ht : 0 ≤ t) (N : ℕ) (x : Euc d)
    (Y : EucConfig d (N - 1)) : poleWeight d s N β x t Y ≤ 1 := by
  rw [wr13a_poleWeight_eq, Real.exp_le_one_iff]
  have h1 : 0 ≤ t * (β / N) := mul_nonneg ht (div_nonneg hβ (Nat.cast_nonneg _))
  have h2 := wr13a_sum_g_nonneg hs0 x Y
  nlinarith

theorem wr13a_poleWeight_meas (hs0 : 0 < s) (N : ℕ) (x : Euc d) (t : ℝ) :
    Measurable (fun Y : EucConfig d (N - 1) => poleWeight d s N β x t Y) := by
  simp only [wr13a_poleWeight_eq]
  exact Real.measurable_exp.comp
    ((Finset.measurable_sum _ fun i _ =>
      (wr13a_g_meas hs0).comp (measurable_const.sub (measurable_pi_apply i))).const_mul _)

theorem wr13a_pole_formulas (hs0 : 0 < s)
    (hconv : ∀ z, HRS.Whole.convMeasure (rieszKernel d s) μ z ≤ Mg) (hβ : 0 ≤ β) (ht : 0 ≤ t)
    (N : ℕ) (x : Euc d) :
    HRS.Whole.poleLaw d s N β μ x t =
      wr13a_tilt (Measure.pi fun _ : Fin (N - 1) => μ) (wr13a_Ep d s μ (β / N) β x t) ∧
    ENNReal.ofReal (poleNormalizer d s N β μ x t) =
      (∫⁻ Y, ENNReal.ofReal (Real.exp (wr13a_E d s μ (β / N) β Y))
        ∂(Measure.pi fun _ : Fin (N - 1) => μ))⁻¹ *
      ∫⁻ Y, ENNReal.ofReal (Real.exp (wr13a_Ep d s μ (β / N) β x t Y))
        ∂(Measure.pi fun _ : Fin (N - 1) => μ) := by
  have hlam : 0 ≤ β / N := div_nonneg hβ (Nat.cast_nonneg _)
  set P : Measure (EucConfig d (N - 1)) := Measure.pi fun _ : Fin (N - 1) => μ with hP
  have hEm := wr13a_E_meas hs0 μ (β / N) β (n := N - 1)
  have hEpm := wr13a_Ep_meas hs0 μ (β / N) β x t (n := N - 1)
  have hcav := wr13a_cavityLaw_eq hs0 hconv hβ N
  haveI := wr13a_cavityLaw_isProb hs0 hconv hβ N
  obtain ⟨hZ0, hZ0'⟩ := wr13a_tilt_ne P hEm (fun Y => wr13a_E_le hs0 hconv hlam hβ Y)
  obtain ⟨hZp, hZp'⟩ := wr13a_tilt_ne P hEpm (fun Y => wr13a_Ep_le hs0 hconv hlam hβ ht x Y)
  set Z0 := ∫⁻ Y, ENNReal.ofReal (Real.exp (wr13a_E d s μ (β / N) β Y)) ∂P with hZ0def
  set Zp := ∫⁻ Y, ENNReal.ofReal (Real.exp (wr13a_Ep d s μ (β / N) β x t Y)) ∂P with hZpdef
  have hW0m : Measurable fun Y : EucConfig d (N - 1) => ENNReal.ofReal (Real.exp (wr13a_E d s μ (β / N) β Y)) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp hEm)
  have hPWm : Measurable fun Y : EucConfig d (N - 1) => ENNReal.ofReal (poleWeight d s N β x t Y) :=
    ENNReal.measurable_ofReal.comp (wr13a_poleWeight_meas hs0 N x t)
  have hpwint : Integrable (fun Y : EucConfig d (N - 1) => poleWeight d s N β x t Y) (HRS.Whole.cavityLaw d s N β μ) :=
    Integrable.of_bound (C := 1) (wr13a_poleWeight_meas hs0 N x t).aestronglyMeasurable
      (Filter.Eventually.of_forall fun Y => by
        rw [Real.norm_eq_abs, abs_of_pos (wr13a_poleWeight_pos N x t Y)]
        exact wr13a_poleWeight_le_one hs0 hβ ht N x Y)
  have hprod : ∀ Y : EucConfig d (N - 1), ENNReal.ofReal (poleWeight d s N β x t Y) *
      ENNReal.ofReal (Real.exp (wr13a_E d s μ (β / N) β Y)) =
      ENNReal.ofReal (Real.exp (wr13a_Ep d s μ (β / N) β x t Y)) := by
    intro Y
    rw [← ENNReal.ofReal_mul (wr13a_poleWeight_pos N x t Y).le, wr13a_exp_Ep, mul_comm]
  have hnorm : ENNReal.ofReal (poleNormalizer d s N β μ x t) = Z0⁻¹ * Zp := by
    have h1 : ENNReal.ofReal (poleNormalizer d s N β μ x t) =
        ∫⁻ Y, ENNReal.ofReal (poleWeight d s N β x t Y) ∂(HRS.Whole.cavityLaw d s N β μ) :=
      ofReal_integral_eq_lintegral_ofReal hpwint
        (Filter.Eventually.of_forall fun Y => (wr13a_poleWeight_pos N x t Y).le)
    rw [h1, hcav, wr13a_lintegral_tilt P hEm _ hPWm]
    congr 1
    exact lintegral_congr hprod
  refine ⟨?_, hnorm⟩
  unfold HRS.Whole.poleLaw
  rw [hnorm, hcav]
  unfold wr13a_tilt
  rw [withDensity_smul_measure, ← withDensity_mul P hW0m hPWm, smul_smul]
  have hf : (fun Y : EucConfig d (N - 1) => ENNReal.ofReal (Real.exp (wr13a_Ep d s μ (β / N) β x t Y))) =
      (fun Y => ENNReal.ofReal (Real.exp (wr13a_E d s μ (β / N) β Y))) * fun Y => ENNReal.ofReal (poleWeight d s N β x t Y) := by
    funext Y
    rw [Pi.mul_apply, mul_comm]
    exact (hprod Y).symm
  rw [← hZpdef, ← hf]
  congr 1
  have hinv0 : Z0⁻¹ ≠ 0 := ENNReal.inv_ne_zero.2 hZ0'
  have hinvt : Z0⁻¹ ≠ ∞ := ENNReal.inv_ne_top.2 hZ0
  rw [ENNReal.mul_inv (Or.inl hinv0) (Or.inl hinvt), inv_inv, mul_right_comm,
    ENNReal.mul_inv_cancel hZ0 hZ0', one_mul]

theorem wr13a_poleLaw_eq (hs0 : 0 < s)
    (hconv : ∀ z, HRS.Whole.convMeasure (rieszKernel d s) μ z ≤ Mg) (hβ : 0 ≤ β) (ht : 0 ≤ t)
    (N : ℕ) (x : Euc d) :
    HRS.Whole.poleLaw d s N β μ x t =
      wr13a_tilt (Measure.pi fun _ : Fin (N - 1) => μ) (wr13a_Ep d s μ (β / N) β x t) :=
  (wr13a_pole_formulas hs0 hconv hβ ht N x).1

/-- Item 2: `CavityWellDefined` (for `β ≥ 0`, `t ≥ 0`; no `N ≥ 2` is needed). -/
theorem wr13a_cavityWellDefined (hs0 : 0 < s)
    (hconv : ∀ z, HRS.Whole.convMeasure (rieszKernel d s) μ z ≤ Mg) (hβ : 0 ≤ β) (ht : 0 ≤ t)
    (N : ℕ) (x : Euc d) : CavityWellDefined d s N β μ x t := by
  have hlam : 0 ≤ β / N := div_nonneg hβ (Nat.cast_nonneg _)
  haveI := wr13a_cavityLaw_isProb hs0 hconv hβ N
  obtain ⟨hZ0, hZ0'⟩ := wr13a_tilt_ne (Measure.pi fun _ : Fin (N - 1) => μ)
    (wr13a_E_meas hs0 μ (β / N) β) (fun Y => wr13a_E_le hs0 hconv hlam hβ Y)
  obtain ⟨hZp, hZp'⟩ := wr13a_tilt_ne (Measure.pi fun _ : Fin (N - 1) => μ)
    (wr13a_Ep_meas hs0 μ (β / N) β x t) (fun Y => wr13a_Ep_le hs0 hconv hlam hβ ht x Y)
  refine ⟨wr13a_cavityWeight_integrable hs0 hconv hβ N, ?_, ?_, ?_⟩
  · have := wr13a_ofReal_cavityNormalizer hs0 hconv hβ N
    exact ENNReal.ofReal_pos.1 (this ▸ pos_iff_ne_zero.2 hZ0)
  · exact Integrable.of_bound (C := 1) (wr13a_poleWeight_meas hs0 N x t).aestronglyMeasurable
      (Filter.Eventually.of_forall fun Y => by
        rw [Real.norm_eq_abs, abs_of_pos (wr13a_poleWeight_pos N x t Y)]
        exact wr13a_poleWeight_le_one hs0 hβ ht N x Y)
  · have h := (wr13a_pole_formulas hs0 hconv hβ ht N x).2
    refine ENNReal.ofReal_pos.1 (h ▸ ?_)
    exact pos_iff_ne_zero.2 (mul_ne_zero (ENNReal.inv_ne_zero.2 hZ0') hZp)

end Laws


/-! ### Density-level statements (items 1 and 2) -/

theorem wr13a_isProb_density {ρ : Euc d → ℝ} (hρ : HRS.Whole.IsProbDensity ρ) :
    IsProbabilityMeasure (HRS.Whole.withDensityReal ρ) :=
  Q34.isProbabilityMeasure_nu hρ

/-- The pointwise bound `g*μ ≤ M_g` in the shape used by the helper lemmas. -/
theorem wr13a_conv_le_density (hd : 1 ≤ d) (hs0 : 0 < s) (hsd : s < d) {ρ : Euc d → ℝ}
    (hρ : HRS.Whole.IsProbDensity ρ) {M : ℝ} (hM : ∀ x, ρ x ≤ M) (z : Euc d) :
    HRS.Whole.convMeasure (rieszKernel d s) (HRS.Whole.withDensityReal ρ) z ≤ potentialBound d s M :=
  (wr13a_potential_bound hd hs0 hsd hρ hM z).2.2

theorem wr13a_potentialBound_nonneg (hd : 1 ≤ d) (hs0 : 0 < s) (hsd : s < d) {ρ : Euc d → ℝ}
    (hρ : HRS.Whole.IsProbDensity ρ) {M : ℝ} (hM : ∀ x, ρ x ≤ M) : 0 ≤ potentialBound d s M :=
  le_trans (wr13a_potential_bound hd hs0 hsd hρ hM 0).2.1 (wr13a_potential_bound hd hs0 hsd hρ hM 0).2.2

/-- Item 2: `CavityWellDefined d s N β μ x t` for `μ = ρ dx`, `ρ ≤ M` a probability density,
`β ≥ 0`, `t ∈ [0,1]`, `N ≥ 2` (the proof does not use `N ≥ 2`, nor `t ≤ 1`). -/
theorem wr13a_cavityWellDefined_density (hd : 2 ≤ d) (hs0 : 0 < s) (hsd : s < d)
    {ρ : Euc d → ℝ} (hρ : HRS.Whole.IsProbDensity ρ) {M : ℝ} (hM : ∀ x, ρ x ≤ M) {β : ℝ}
    (hβ : 0 ≤ β) (N : ℕ) (_hN : 2 ≤ N) (x : Euc d) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    CavityWellDefined d s N β (HRS.Whole.withDensityReal ρ) x t := by
  haveI := wr13a_isProb_density hρ
  exact wr13a_cavityWellDefined hs0 (wr13a_conv_le_density (by omega) hs0 hsd hρ hM) hβ ht.1 N x

end HRS.MS.Wr
