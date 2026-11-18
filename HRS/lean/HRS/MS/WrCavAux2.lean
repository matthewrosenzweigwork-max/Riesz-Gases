import HRS.MS.WrCavAux1

/-!
# HRS.MS.WrCavAux2 -- exact cavity identity and pole / one-particle density bounds (WR-13a, part 2)

Second helper file of packet WR-13a (T7 of `docs/WR_B_PLAN.md`), `0 < s < d`, `μ = ρ dx` with `ρ ≤ M`.

* `wr13a_modulatedGibbs_eq`: `modulatedGibbs g (n+1) β μ` is the normalised tilt of `μ^{⊗(n+1)}` by
  `exp(-λ ∑_{i<j} g + β ∑ g*μ)`, `λ = β/(n+1)` (the energy differs from this exponent by a constant).
* `wr13a_cavity_disintegration`: the exact cavity identity, `Q = ∫ poleLaw(x, 1) dπ_N(x)` in the form
  `∫⁻ F(X 0, tail X) dQ = ∫⁻ ∫⁻ F(x, Y) d(poleLaw d s (n+1) β μ x 1)(Y) d(firstMarginal Q)(x)`.
* `wr13a_firstMarginal_eq`: `firstMarginal Q = μ.withDensity (exp(β g*μ) Φ_x / ∫ exp(β g*μ) Φ)`, with
  `Φ_x = poleNormalizer d s (n+1) β μ x 1`, and the pointwise bound `dπ_N/dμ ≤ C` (conjunct 3, sup part).
* `wr13a_pole_one_le`, `wr13a_pole_two_le`: `firstMarginal (poleLaw ..) ≤ μ.withDensity (C e^{-tλ g(x-·)})` and the
  two-particle analogue (`3 ≤ N`).
* `wr13a_pole_bundle`: the pole and cavity conjuncts of `Bias.StaticInputConclusion` (everything except the pole
  variance, which is WR-13b, and the cavity TV bound), for all `0 < s < d`, uniformly in `β ∈ [0, βp]`.

Statement adjustments with respect to the sketches (all harmless): `β` ranges over `[0, βp]` (the proofs only use
`β ≥ 0`), which contains `[βm, βp]`; the constants depend only on `d, s, βp, M` and are quantified before
`ρ, β, N, x, t`.  Helper lemmas carry the prefix `wr13a_`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open MeasureTheory
open scoped ENNReal BigOperators

noncomputable section

namespace HRS.MS.Wr

open HRS.Whole

variable {d : ℕ} {s : ℝ}

/-! ### Tilts and constants -/

theorem wr13a_tilt_add_const {α : Type*} [MeasurableSpace α] (P : Measure α) {w : α → ℝ}
    (hw : Measurable w) (c : ℝ) (h0 : (∫⁻ a, ENNReal.ofReal (Real.exp (w a)) ∂P) ≠ 0)
    (h1 : (∫⁻ a, ENNReal.ofReal (Real.exp (w a)) ∂P) ≠ ∞) :
    wr13a_tilt P (fun a => w a + c) = wr13a_tilt P w := by
  have hm : Measurable fun a => ENNReal.ofReal (Real.exp (w a)) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp hw)
  set k : ℝ≥0∞ := ENNReal.ofReal (Real.exp c) with hk
  have hk0 : k ≠ 0 := (ENNReal.ofReal_pos.2 (Real.exp_pos c)).ne'
  have hkt : k ≠ ∞ := ENNReal.ofReal_ne_top
  have hfun : (fun a => ENNReal.ofReal (Real.exp (w a + c))) =
      k • fun a => ENNReal.ofReal (Real.exp (w a)) := by
    funext a
    simp only [hk, Pi.smul_apply, smul_eq_mul, Real.exp_add]
    rw [ENNReal.ofReal_mul (Real.exp_pos _).le, mul_comm]
  have hZ : ∫⁻ a, ENNReal.ofReal (Real.exp (w a + c)) ∂P =
      k * ∫⁻ a, ENNReal.ofReal (Real.exp (w a)) ∂P := by
    rw [← lintegral_const_mul _ hm]
    exact lintegral_congr fun a => congrFun hfun a
  have hD : P.withDensity (fun a => ENNReal.ofReal (Real.exp (w a + c))) =
      k • P.withDensity (fun a => ENNReal.ofReal (Real.exp (w a))) := by
    rw [← withDensity_smul' k _ hkt]
    exact congrArg P.withDensity hfun
  have hc : (k * ∫⁻ a, ENNReal.ofReal (Real.exp (w a)) ∂P)⁻¹ * k =
      (∫⁻ a, ENNReal.ofReal (Real.exp (w a)) ∂P)⁻¹ := by
    rw [ENNReal.mul_inv (Or.inl hk0) (Or.inl hkt), mul_right_comm, ENNReal.inv_mul_cancel hk0 hkt,
      one_mul]
  unfold wr13a_tilt
  rw [hZ, hD, smul_smul, hc]


/-! ### `modulatedGibbs` is a tilt of the product measure -/

section Q

variable {μ : Measure (Euc d)} [IsProbabilityMeasure μ] {Mg β : ℝ}

theorem wr13a_exp_E_integrable (hs0 : 0 < s)
    (hconv : ∀ z, HRS.Whole.convMeasure (rieszKernel d s) μ z ≤ Mg) {lam : ℝ} (hlam : 0 ≤ lam)
    (hβ : 0 ≤ β) (c : ℝ) (n : ℕ) :
    Integrable (fun Y : EucConfig d n => Real.exp (wr13a_E d s μ lam β Y + c))
      (Measure.pi fun _ : Fin n => μ) :=
  Integrable.of_bound (C := Real.exp (β * n * Mg + c))
    (Real.measurable_exp.comp ((wr13a_E_meas hs0 μ lam β).add_const c)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun Y => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.2 (by linarith [wr13a_E_le hs0 hconv hlam hβ Y]))

theorem wr13a_modulatedGibbs_eq (hs0 : 0 < s)
    (hconv : ∀ z, HRS.Whole.convMeasure (rieszKernel d s) μ z ≤ Mg) (hβ : 0 ≤ β) (n : ℕ) :
    HRS.Whole.modulatedGibbs (rieszKernel d s) (n + 1) β μ =
      wr13a_tilt (Measure.pi fun _ : Fin (n + 1) => μ)
        (wr13a_E d s μ (β / ((n + 1 : ℕ) : ℝ)) β) := by
  have hlam : 0 ≤ β / ((n + 1 : ℕ) : ℝ) := div_nonneg hβ (Nat.cast_nonneg _)
  have hN0 : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  set c0 : ℝ := -β * ((n + 1 : ℕ) : ℝ) *
    ((1 / 2) * HRS.Whole.energyPairing (rieszKernel d s) μ μ) with hc0
  have hw : ∀ X : EucConfig d (n + 1), -β * ((n + 1 : ℕ) : ℝ) *
      HRS.Whole.modulatedEnergy (rieszKernel d s) X μ =
      wr13a_E d s μ (β / ((n + 1 : ℕ) : ℝ)) β X + c0 := by
    intro X
    rw [modulatedEnergy_eq_sum_lt (rieszKernel d s) (fun z => rieszKernel_neg z) X μ]
    unfold wr13a_E wr13a_pairSum
    simp only [hc0]
    field_simp
    ring
  have hint := wr13a_exp_E_integrable hs0 hconv hlam hβ c0 (n + 1)
  have hZ : ENNReal.ofReal (HRS.Whole.gibbsNormalizer (rieszKernel d s) (n + 1) β μ) =
      ∫⁻ X, ENNReal.ofReal (Real.exp (wr13a_E d s μ (β / ((n + 1 : ℕ) : ℝ)) β X + c0))
        ∂(Measure.pi fun _ : Fin (n + 1) => μ) := by
    unfold HRS.Whole.gibbsNormalizer
    simp only [hw]
    exact ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun Y => (Real.exp_pos _).le)
  have hQ : HRS.Whole.modulatedGibbs (rieszKernel d s) (n + 1) β μ =
      wr13a_tilt (Measure.pi fun _ : Fin (n + 1) => μ)
        (fun X => wr13a_E d s μ (β / ((n + 1 : ℕ) : ℝ)) β X + c0) := by
    unfold HRS.Whole.modulatedGibbs wr13a_tilt
    rw [hZ]
    simp only [hw]
  rw [hQ]
  obtain ⟨h0, h1⟩ := wr13a_tilt_ne (Measure.pi fun _ : Fin (n + 1) => μ)
    (wr13a_E_meas hs0 μ (β / ((n + 1 : ℕ) : ℝ)) β) (fun Y => wr13a_E_le hs0 hconv hlam hβ Y)
  exact wr13a_tilt_add_const _ (wr13a_E_meas hs0 μ (β / ((n + 1 : ℕ) : ℝ)) β) c0 h0 h1

end Q


/-! ### The exact cavity identity -/

/-- `Z_n = ∫⁻ exp(E) dμ^{⊗n}`: the normaliser of the cavity weight with `n` particles. -/
def wr13a_Z (d : ℕ) (s : ℝ) (μ : Measure (Euc d)) (lam β : ℝ) (n : ℕ) : ℝ≥0∞ :=
  ∫⁻ Y : EucConfig d n, ENNReal.ofReal (Real.exp (wr13a_E d s μ lam β Y))
    ∂(Measure.pi fun _ : Fin n => μ)

/-- `J_n(x,t) = ∫⁻ exp(Ep) dμ^{⊗n}`: the normaliser of the pole-tilted cavity weight. -/
def wr13a_J (d : ℕ) (s : ℝ) (μ : Measure (Euc d)) (lam β t : ℝ) (n : ℕ) (x : Euc d) : ℝ≥0∞ :=
  ∫⁻ Y : EucConfig d n, ENNReal.ofReal (Real.exp (wr13a_Ep d s μ lam β x t Y))
    ∂(Measure.pi fun _ : Fin n => μ)

section Disint

variable {μ : Measure (Euc d)} [IsProbabilityMeasure μ] {Mg β t : ℝ}

theorem wr13a_Ep_meas2 (hs0 : 0 < s) (lam β t : ℝ) {n : ℕ} :
    Measurable (fun p : Euc d × EucConfig d n => wr13a_Ep d s μ lam β p.1 t p.2) := by
  unfold wr13a_Ep
  exact ((wr13a_E_meas hs0 μ lam β).comp measurable_snd).sub
    ((Finset.measurable_sum _ fun i _ =>
      (wr13a_g_meas hs0).comp (measurable_fst.sub ((measurable_pi_apply i).comp measurable_snd))).const_mul _)

theorem wr13a_J_meas (hs0 : 0 < s) (lam β t : ℝ) (n : ℕ) :
    Measurable (wr13a_J d s μ lam β t n) := by
  unfold wr13a_J
  exact Measurable.lintegral_prod_right'
    (f := fun p : Euc d × EucConfig d n => ENNReal.ofReal (Real.exp (wr13a_Ep d s μ lam β p.1 t p.2)))
    (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (wr13a_Ep_meas2 hs0 lam β t)))

theorem wr13a_J_ne (hs0 : 0 < s) (hconv : ∀ z, HRS.Whole.convMeasure (rieszKernel d s) μ z ≤ Mg)
    {lam : ℝ} (hlam : 0 ≤ lam) (hβ : 0 ≤ β) (ht : 0 ≤ t) (n : ℕ) (x : Euc d) :
    wr13a_J d s μ lam β t n x ≠ 0 ∧ wr13a_J d s μ lam β t n x ≠ ∞ :=
  wr13a_tilt_ne (Measure.pi fun _ : Fin n => μ) (wr13a_Ep_meas hs0 μ lam β x t)
    (fun Y => wr13a_Ep_le hs0 hconv hlam hβ ht x Y)

theorem wr13a_Z_ne (hs0 : 0 < s) (hconv : ∀ z, HRS.Whole.convMeasure (rieszKernel d s) μ z ≤ Mg)
    {lam : ℝ} (hlam : 0 ≤ lam) (hβ : 0 ≤ β) (n : ℕ) :
    wr13a_Z d s μ lam β n ≠ 0 ∧ wr13a_Z d s μ lam β n ≠ ∞ :=
  wr13a_tilt_ne (Measure.pi fun _ : Fin n => μ) (wr13a_E_meas hs0 μ lam β)
    (fun Y => wr13a_E_le hs0 hconv hlam hβ Y)

theorem wr13a_E_cons_eq (lam β : ℝ) (x : Euc d) {n : ℕ} (Y : EucConfig d n) :
    wr13a_E d s μ lam β (Fin.cons x Y : EucConfig d (n + 1)) =
      β * HRS.Whole.convMeasure (rieszKernel d s) μ x + wr13a_Ep d s μ lam β x 1 Y := by
  rw [wr13a_E_cons]
  unfold wr13a_Ep
  ring

/-- `∫⁻ F(X 0, tail X) dQ` in terms of `μ ⊗ μ^{⊗n}`. -/
theorem wr13a_lintegral_Q (hs0 : 0 < s)
    (hconv : ∀ z, HRS.Whole.convMeasure (rieszKernel d s) μ z ≤ Mg) (hβ : 0 ≤ β) (n : ℕ)
    (F : Euc d × EucConfig d n → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ X : EucConfig d (n + 1), F (X 0, Fin.tail X)
        ∂(HRS.Whole.modulatedGibbs (rieszKernel d s) (n + 1) β μ) =
      (wr13a_Z d s μ (β / ((n + 1 : ℕ) : ℝ)) β (n + 1))⁻¹ *
        ∫⁻ x, ENNReal.ofReal (Real.exp (β * HRS.Whole.convMeasure (rieszKernel d s) μ x)) *
          ∫⁻ Y : EucConfig d n, F (x, Y) *
            ENNReal.ofReal (Real.exp (wr13a_Ep d s μ (β / ((n + 1 : ℕ) : ℝ)) β x 1 Y))
              ∂(Measure.pi fun _ : Fin n => μ) ∂μ := by
  have hEm := wr13a_E_meas hs0 μ (β / ((n + 1 : ℕ) : ℝ)) β (n := n + 1)
  have hT : Measurable fun X : EucConfig d (n + 1) => (X 0, Fin.tail X) :=
    (measurable_pi_apply 0).prodMk (measurable_pi_iff.2 fun j => measurable_pi_apply _)
  have hWm : Measurable fun X : EucConfig d (n + 1) =>
      ENNReal.ofReal (Real.exp (wr13a_E d s μ (β / ((n + 1 : ℕ) : ℝ)) β X)) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp hEm)
  have hFT : Measurable fun X : EucConfig d (n + 1) => F (X 0, Fin.tail X) := hF.comp hT
  rw [wr13a_modulatedGibbs_eq hs0 hconv hβ n,
    wr13a_lintegral_tilt _ hEm (fun X : EucConfig d (n + 1) => F (X 0, Fin.tail X)) hFT]
  unfold wr13a_Z
  congr 1
  rw [wr13a_lintegral_pi_succ μ (fun X : EucConfig d (n + 1) => F (X 0, Fin.tail X) *
    ENNReal.ofReal (Real.exp (wr13a_E d s μ (β / ((n + 1 : ℕ) : ℝ)) β X))) (hFT.mul hWm)]
  refine lintegral_congr fun x => ?_
  have hFx : Measurable fun Y : EucConfig d n => F (x, Y) := hF.comp measurable_prodMk_left
  have hWx : Measurable fun Y : EucConfig d n =>
      ENNReal.ofReal (Real.exp (wr13a_Ep d s μ (β / ((n + 1 : ℕ) : ℝ)) β x 1 Y)) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (wr13a_Ep_meas hs0 μ _ β x 1))
  have hFW : Measurable fun Y : EucConfig d n => F (x, Y) *
      ENNReal.ofReal (Real.exp (wr13a_Ep d s μ (β / ((n + 1 : ℕ) : ℝ)) β x 1 Y)) := hFx.mul hWx
  rw [← lintegral_const_mul _ hFW]
  refine lintegral_congr fun Y => ?_
  simp only [Fin.cons_zero, Fin.tail_cons]
  rw [wr13a_E_cons_eq, Real.exp_add, ENNReal.ofReal_mul (Real.exp_pos _).le]
  ring


theorem wr13a_lintegral_pole (hs0 : 0 < s)
    (hconv : ∀ z, HRS.Whole.convMeasure (rieszKernel d s) μ z ≤ Mg) (hβ : 0 ≤ β) (n : ℕ) (x : Euc d)
    (H : EucConfig d n → ℝ≥0∞) (hH : Measurable H) :
    ∫⁻ Y : EucConfig d n, H Y ∂(HRS.Whole.poleLaw d s (n + 1) β μ x 1) =
      (wr13a_J d s μ (β / ((n + 1 : ℕ) : ℝ)) β 1 n x)⁻¹ *
        ∫⁻ Y : EucConfig d n, H Y *
          ENNReal.ofReal (Real.exp (wr13a_Ep d s μ (β / ((n + 1 : ℕ) : ℝ)) β x 1 Y))
            ∂(Measure.pi fun _ : Fin n => μ) := by
  have h : HRS.Whole.poleLaw d s (n + 1) β μ x 1 =
      wr13a_tilt (Measure.pi fun _ : Fin n => μ) (wr13a_Ep d s μ (β / ((n + 1 : ℕ) : ℝ)) β x 1) :=
    wr13a_poleLaw_eq hs0 hconv hβ zero_le_one (n + 1) x
  rw [h, wr13a_lintegral_tilt _ (wr13a_Ep_meas hs0 μ _ β x 1) H hH]
  rfl

theorem wr13a_firstMarginal_Q (hs0 : 0 < s)
    (hconv : ∀ z, HRS.Whole.convMeasure (rieszKernel d s) μ z ≤ Mg) (hβ : 0 ≤ β) (n : ℕ) :
    HRS.Whole.firstMarginal (HRS.Whole.modulatedGibbs (rieszKernel d s) (n + 1) β μ) =
      μ.withDensity fun x =>
        (wr13a_Z d s μ (β / ((n + 1 : ℕ) : ℝ)) β (n + 1))⁻¹ *
          ENNReal.ofReal (Real.exp (β * HRS.Whole.convMeasure (rieszKernel d s) μ x)) *
            wr13a_J d s μ (β / ((n + 1 : ℕ) : ℝ)) β 1 n x := by
  set Q := HRS.Whole.modulatedGibbs (rieszKernel d s) (n + 1) β μ with hQ
  have hlam : 0 ≤ β / ((n + 1 : ℕ) : ℝ) := div_nonneg hβ (Nat.cast_nonneg _)
  obtain ⟨hZ0, hZt⟩ := wr13a_Z_ne hs0 hconv hlam hβ (n + 1)
  have hfm : HRS.Whole.firstMarginal Q = Q.map (fun X : EucConfig d (n + 1) => X 0) := by
    unfold HRS.Whole.firstMarginal
    rw [dif_pos (Nat.succ_pos n)]
    rfl
  ext A hA
  rw [hfm, Measure.map_apply (measurable_pi_apply 0) hA, withDensity_apply _ hA,
    ← lintegral_indicator hA]
  set F : Euc d × EucConfig d n → ℝ≥0∞ := fun p => A.indicator 1 p.1 with hF
  have hFm : Measurable F := (measurable_one.indicator hA).comp measurable_fst
  have h1 : Q ((fun X : EucConfig d (n + 1) => X 0) ⁻¹' A) =
      ∫⁻ X : EucConfig d (n + 1), F (X 0, Fin.tail X) ∂Q := by
    rw [← lintegral_indicator_one ((measurable_pi_apply 0) hA)]
    refine lintegral_congr fun X => ?_
    by_cases h : X 0 ∈ A <;> simp [Set.indicator, hF, h]
  rw [h1, wr13a_lintegral_Q hs0 hconv hβ n F hFm, ← lintegral_const_mul' _ _
    (ENNReal.inv_ne_top.2 hZ0)]
  refine lintegral_congr fun x => ?_
  by_cases h : x ∈ A
  · have : ∀ Y : EucConfig d n, F (x, Y) = 1 := fun Y => by simp [hF, h]
    simp only [this, one_mul, Set.indicator_of_mem h]
    rw [mul_assoc]
    rfl
  · have : ∀ Y : EucConfig d n, F (x, Y) = 0 := fun Y => by simp [hF, h]
    simp [this, Set.indicator_of_notMem h]


/-- **Item 3, exact cavity identity.**  The law `Q = modulatedGibbs g (n+1) β μ`, disintegrated over
the first particle `x_1 = X 0`, is `∫ poleLaw d s (n+1) β μ x 1 d(π_N)(x)`, `π_N = firstMarginal Q`:
for every measurable `F ≥ 0` on `ℝ^d × (ℝ^d)^n`,
`∫ F(X 0, tail X) dQ = ∫ (∫ F(x, Y) d(poleLaw x 1)(Y)) dπ_N(x)`. -/
theorem wr13a_cavity_disintegration (hs0 : 0 < s)
    (hconv : ∀ z, HRS.Whole.convMeasure (rieszKernel d s) μ z ≤ Mg) (hβ : 0 ≤ β) (n : ℕ)
    (F : Euc d × EucConfig d n → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ X : EucConfig d (n + 1), F (X 0, Fin.tail X)
        ∂(HRS.Whole.modulatedGibbs (rieszKernel d s) (n + 1) β μ) =
      ∫⁻ x, ∫⁻ Y : EucConfig d n, F (x, Y) ∂(HRS.Whole.poleLaw d s (n + 1) β μ x 1)
        ∂(HRS.Whole.firstMarginal (HRS.Whole.modulatedGibbs (rieszKernel d s) (n + 1) β μ)) := by
  have hlam : 0 ≤ β / ((n + 1 : ℕ) : ℝ) := div_nonneg hβ (Nat.cast_nonneg _)
  obtain ⟨hZ0, hZt⟩ := wr13a_Z_ne hs0 hconv hlam hβ (n + 1)
  rw [wr13a_firstMarginal_Q hs0 hconv hβ n]
  have hJm := wr13a_J_meas (μ := μ) hs0 (β / ((n + 1 : ℕ) : ℝ)) β 1 n
  have hφm : Measurable fun x =>
      (wr13a_Z d s μ (β / ((n + 1 : ℕ) : ℝ)) β (n + 1))⁻¹ *
        ENNReal.ofReal (Real.exp (β * HRS.Whole.convMeasure (rieszKernel d s) μ x)) *
          wr13a_J d s μ (β / ((n + 1 : ℕ) : ℝ)) β 1 n x :=
    (measurable_const.mul (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
      ((wr13a_conv_meas hs0 μ).const_mul β)))).mul hJm
  have hWm : Measurable fun p : Euc d × EucConfig d n => F p *
      ENNReal.ofReal (Real.exp (wr13a_Ep d s μ (β / ((n + 1 : ℕ) : ℝ)) β p.1 1 p.2)) :=
    hF.mul (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (wr13a_Ep_meas2 hs0 _ β 1)))
  have hIm : Measurable fun x : Euc d => ∫⁻ Y : EucConfig d n, F (x, Y) *
      ENNReal.ofReal (Real.exp (wr13a_Ep d s μ (β / ((n + 1 : ℕ) : ℝ)) β x 1 Y))
        ∂(Measure.pi fun _ : Fin n => μ) :=
    Measurable.lintegral_prod_right' (f := fun p : Euc d × EucConfig d n => F p *
      ENNReal.ofReal (Real.exp (wr13a_Ep d s μ (β / ((n + 1 : ℕ) : ℝ)) β p.1 1 p.2))) hWm
  have hG : ∀ x : Euc d, ∫⁻ Y : EucConfig d n, F (x, Y) ∂(HRS.Whole.poleLaw d s (n + 1) β μ x 1) =
      (wr13a_J d s μ (β / ((n + 1 : ℕ) : ℝ)) β 1 n x)⁻¹ *
        ∫⁻ Y : EucConfig d n, F (x, Y) *
          ENNReal.ofReal (Real.exp (wr13a_Ep d s μ (β / ((n + 1 : ℕ) : ℝ)) β x 1 Y))
            ∂(Measure.pi fun _ : Fin n => μ) := fun x =>
    wr13a_lintegral_pole hs0 hconv hβ n x (fun Y => F (x, Y)) (hF.comp measurable_prodMk_left)
  have hGm : Measurable fun x : Euc d =>
      ∫⁻ Y : EucConfig d n, F (x, Y) ∂(HRS.Whole.poleLaw d s (n + 1) β μ x 1) := by
    simp_rw [hG]
    exact hJm.inv.mul hIm
  rw [lintegral_withDensity_eq_lintegral_mul _ hφm hGm,
    wr13a_lintegral_Q hs0 hconv hβ n F hF, ← lintegral_const_mul' _ _ (ENNReal.inv_ne_top.2 hZ0)]
  refine lintegral_congr fun x => ?_
  simp only [Pi.mul_apply, hG]
  obtain ⟨hJ0, hJt⟩ := wr13a_J_ne hs0 hconv hlam hβ zero_le_one n x
  have key : ∀ c A J I : ℝ≥0∞, J ≠ 0 → J ≠ ∞ → c * (A * I) = c * A * J * (J⁻¹ * I) := by
    intro c A J I h0 h1
    rw [mul_assoc (c * A) J, ← mul_assoc J, ENNReal.mul_inv_cancel h0 h1, one_mul, mul_assoc]
  exact key _ _ _ _ hJ0 hJt


/-! ### The first marginal: explicit density and the sup bound -/

theorem wr13a_firstMarginal_def (n : ℕ) (Q : Measure (EucConfig d (n + 1))) :
    HRS.Whole.firstMarginal Q = Q.map (fun X : EucConfig d (n + 1) => X 0) := by
  unfold HRS.Whole.firstMarginal
  rw [dif_pos (Nat.succ_pos n)]
  rfl

theorem wr13a_lam_mul_le (hβ : 0 ≤ β) (n : ℕ) : β / ((n + 1 : ℕ) : ℝ) * (n : ℝ) ≤ β := by
  have hpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  rw [div_mul_eq_mul_div, div_le_iff₀ hpos]
  push_cast
  nlinarith

theorem wr13a_J_le_Z (hs0 : 0 < s) {lam : ℝ} (hlam : 0 ≤ lam) (β : ℝ) (n : ℕ) (x : Euc d) :
    wr13a_J d s μ lam β 1 n x ≤ wr13a_Z d s μ lam β n := by
  refine lintegral_mono fun Y => ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
  unfold wr13a_Ep
  have := wr13a_sum_g_nonneg hs0 x Y
  nlinarith

/-- The density of `π_N` is bounded by `exp(2 β M_g)` pointwise. -/
theorem wr13a_phi_le (hs0 : 0 < s) (hint : ∀ z, Integrable (fun y => rieszKernel d s (z - y)) μ)
    (hconv : ∀ z, HRS.Whole.convMeasure (rieszKernel d s) μ z ≤ Mg) (hMg : 0 ≤ Mg) (hβ : 0 ≤ β)
    (n : ℕ) (x : Euc d) :
    (wr13a_Z d s μ (β / ((n + 1 : ℕ) : ℝ)) β (n + 1))⁻¹ *
        ENNReal.ofReal (Real.exp (β * HRS.Whole.convMeasure (rieszKernel d s) μ x)) *
          wr13a_J d s μ (β / ((n + 1 : ℕ) : ℝ)) β 1 n x ≤
      ENNReal.ofReal (Real.exp (2 * β * Mg)) := by
  set lam : ℝ := β / ((n + 1 : ℕ) : ℝ) with hlamdef
  have hlam : 0 ≤ lam := div_nonneg hβ (Nat.cast_nonneg _)
  obtain ⟨hZ0, hZt⟩ := wr13a_Z_ne hs0 hconv hlam hβ n
  set K : ℝ := lam * (0 + (n : ℝ)) * Mg with hK
  have hKle : K ≤ β * Mg := by
    have := wr13a_lam_mul_le hβ n
    rw [hK, zero_add]
    exact mul_le_mul_of_nonneg_right this hMg
  have hlow : ENNReal.ofReal (Real.exp (-K)) * wr13a_Z d s μ lam β n ≤
      wr13a_Z d s μ lam β (n + 1) := by
    have := wr13a_lower_step hs0 hint hconv hlam hβ (le_refl (0 : ℝ)) (0 : Euc d) n
    simp only [wr13a_Ep_zero] at this
    exact this
  have hc1 : ENNReal.ofReal (Real.exp (-K)) ≠ 0 := (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne'
  have hc1t : ENNReal.ofReal (Real.exp (-K)) ≠ ∞ := ENNReal.ofReal_ne_top
  have hinv : (wr13a_Z d s μ lam β (n + 1))⁻¹ ≤
      ENNReal.ofReal (Real.exp K) * (wr13a_Z d s μ lam β n)⁻¹ := by
    calc (wr13a_Z d s μ lam β (n + 1))⁻¹ ≤ (ENNReal.ofReal (Real.exp (-K)) * wr13a_Z d s μ lam β n)⁻¹ :=
          ENNReal.inv_le_inv.2 hlow
      _ = ENNReal.ofReal (Real.exp K) * (wr13a_Z d s μ lam β n)⁻¹ := by
          rw [ENNReal.mul_inv (Or.inl hc1) (Or.inl hc1t), ← ENNReal.ofReal_inv_of_pos (Real.exp_pos _),
            ← Real.exp_neg, neg_neg]
  have hA : ENNReal.ofReal (Real.exp (β * HRS.Whole.convMeasure (rieszKernel d s) μ x)) ≤
      ENNReal.ofReal (Real.exp (β * Mg)) :=
    ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (hconv x) hβ))
  calc (wr13a_Z d s μ lam β (n + 1))⁻¹ *
        ENNReal.ofReal (Real.exp (β * HRS.Whole.convMeasure (rieszKernel d s) μ x)) *
          wr13a_J d s μ lam β 1 n x
      ≤ (ENNReal.ofReal (Real.exp K) * (wr13a_Z d s μ lam β n)⁻¹) *
        ENNReal.ofReal (Real.exp (β * Mg)) * wr13a_Z d s μ lam β n :=
        mul_le_mul' (mul_le_mul' hinv hA) (wr13a_J_le_Z hs0 hlam β n x)
    _ = ENNReal.ofReal (Real.exp K) * ENNReal.ofReal (Real.exp (β * Mg)) := by
        rw [mul_assoc, mul_comm (ENNReal.ofReal (Real.exp (β * Mg))), ← mul_assoc,
          mul_assoc (ENNReal.ofReal (Real.exp K)), ENNReal.inv_mul_cancel hZ0 hZt, mul_one]
    _ ≤ ENNReal.ofReal (Real.exp (2 * β * Mg)) := by
        rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
        exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (by linarith))


theorem wr13a_ofReal_Phi (hs0 : 0 < s) (hconv : ∀ z, HRS.Whole.convMeasure (rieszKernel d s) μ z ≤ Mg)
    (hβ : 0 ≤ β) (n : ℕ) (x : Euc d) :
    ENNReal.ofReal (poleNormalizer d s (n + 1) β μ x 1) =
      (wr13a_Z d s μ (β / ((n + 1 : ℕ) : ℝ)) β n)⁻¹ *
        wr13a_J d s μ (β / ((n + 1 : ℕ) : ℝ)) β 1 n x :=
  (wr13a_pole_formulas hs0 hconv hβ zero_le_one (n + 1) x).2

theorem wr13a_Phi_nonneg (n : ℕ) (x : Euc d) : 0 ≤ poleNormalizer d s (n + 1) β μ x 1 :=
  integral_nonneg fun Y => (wr13a_poleWeight_pos (n + 1) x 1 Y).le

theorem wr13a_Phi_le_one (hs0 : 0 < s)
    (hconv : ∀ z, HRS.Whole.convMeasure (rieszKernel d s) μ z ≤ Mg) (hβ : 0 ≤ β) (n : ℕ) (x : Euc d) :
    poleNormalizer d s (n + 1) β μ x 1 ≤ 1 := by
  have hlam : 0 ≤ β / ((n + 1 : ℕ) : ℝ) := div_nonneg hβ (Nat.cast_nonneg _)
  obtain ⟨hZ0, hZt⟩ := wr13a_Z_ne hs0 hconv hlam hβ n
  have h1 : ENNReal.ofReal (poleNormalizer d s (n + 1) β μ x 1) ≤ 1 := by
    rw [wr13a_ofReal_Phi hs0 hconv hβ n x]
    calc (wr13a_Z d s μ (β / ((n + 1 : ℕ) : ℝ)) β n)⁻¹ *
          wr13a_J d s μ (β / ((n + 1 : ℕ) : ℝ)) β 1 n x ≤
        (wr13a_Z d s μ (β / ((n + 1 : ℕ) : ℝ)) β n)⁻¹ * wr13a_Z d s μ (β / ((n + 1 : ℕ) : ℝ)) β n :=
          mul_le_mul' le_rfl (wr13a_J_le_Z hs0 hlam β n x)
      _ = 1 := ENNReal.inv_mul_cancel hZ0 hZt
  exact (ENNReal.ofReal_le_one).1 h1

theorem wr13a_Phi_meas (hs0 : 0 < s) (hconv : ∀ z, HRS.Whole.convMeasure (rieszKernel d s) μ z ≤ Mg)
    (hβ : 0 ≤ β) (n : ℕ) :
    Measurable fun x => poleNormalizer d s (n + 1) β μ x 1 := by
  have : (fun x => poleNormalizer d s (n + 1) β μ x 1) = fun x =>
      ((wr13a_Z d s μ (β / ((n + 1 : ℕ) : ℝ)) β n)⁻¹ *
        wr13a_J d s μ (β / ((n + 1 : ℕ) : ℝ)) β 1 n x).toReal := by
    funext x
    rw [← wr13a_ofReal_Phi hs0 hconv hβ n x, ENNReal.toReal_ofReal (wr13a_Phi_nonneg n x)]
  rw [this]
  exact (measurable_const.mul (wr13a_J_meas hs0 _ β 1 n)).ennreal_toReal

/-- **Item 3, first marginal.**  `π_N = firstMarginal Q` has the density
`exp(β g*μ(x)) Φ_x / ∫ exp(β g*μ) Φ dμ` with respect to `μ`, `Φ_x = poleNormalizer d s (n+1) β μ x 1`
(`Φ_x = E_{P_n^0}[e^{-λ ∑_j g(x-y_j)}]`); the normalising integral is positive. -/
theorem wr13a_firstMarginal_eq (hs0 : 0 < s) (hint : ∀ z, Integrable (fun y => rieszKernel d s (z - y)) μ)
    (hconv : ∀ z, HRS.Whole.convMeasure (rieszKernel d s) μ z ≤ Mg) (hMg : 0 ≤ Mg) (hβ : 0 ≤ β)
    (n : ℕ) :
    0 < ∫ y, Real.exp (β * HRS.Whole.convMeasure (rieszKernel d s) μ y) *
        poleNormalizer d s (n + 1) β μ y 1 ∂μ ∧
    (∀ x, (wr13a_Z d s μ (β / ((n + 1 : ℕ) : ℝ)) β (n + 1))⁻¹ *
        ENNReal.ofReal (Real.exp (β * HRS.Whole.convMeasure (rieszKernel d s) μ x)) *
          wr13a_J d s μ (β / ((n + 1 : ℕ) : ℝ)) β 1 n x =
      ENNReal.ofReal
        (Real.exp (β * HRS.Whole.convMeasure (rieszKernel d s) μ x) *
          poleNormalizer d s (n + 1) β μ x 1 /
          ∫ y, Real.exp (β * HRS.Whole.convMeasure (rieszKernel d s) μ y) *
            poleNormalizer d s (n + 1) β μ y 1 ∂μ)) ∧
    HRS.Whole.firstMarginal (HRS.Whole.modulatedGibbs (rieszKernel d s) (n + 1) β μ) =
      μ.withDensity fun x => ENNReal.ofReal
        (Real.exp (β * HRS.Whole.convMeasure (rieszKernel d s) μ x) *
          poleNormalizer d s (n + 1) β μ x 1 /
          ∫ y, Real.exp (β * HRS.Whole.convMeasure (rieszKernel d s) μ y) *
            poleNormalizer d s (n + 1) β μ y 1 ∂μ) := by
  set Q := HRS.Whole.modulatedGibbs (rieszKernel d s) (n + 1) β μ with hQ
  set lam : ℝ := β / ((n + 1 : ℕ) : ℝ) with hlamdef
  have hlam : 0 ≤ lam := div_nonneg hβ (Nat.cast_nonneg _)
  obtain ⟨hZ0, hZt⟩ := wr13a_Z_ne hs0 hconv hlam hβ n
  obtain ⟨hZq0, hZqt⟩ := wr13a_Z_ne hs0 hconv hlam hβ (n + 1)
  set Zn := wr13a_Z d s μ lam β n with hZn
  set Zq := wr13a_Z d s μ lam β (n + 1) with hZq
  have hπ := wr13a_firstMarginal_Q hs0 hconv hβ n
  have hQprob : IsProbabilityMeasure Q := by
    rw [hQ, wr13a_modulatedGibbs_eq hs0 hconv hβ n]
    exact wr13a_tilt_isProb _ (wr13a_E_meas hs0 μ _ β) (fun Y => wr13a_E_le hs0 hconv hlam hβ Y)
  have hmass : (HRS.Whole.firstMarginal Q) Set.univ = 1 := by
    rw [wr13a_firstMarginal_def]
    exact measure_univ
  set h : Euc d → ℝ := fun y => Real.exp (β * HRS.Whole.convMeasure (rieszKernel d s) μ y) *
    poleNormalizer d s (n + 1) β μ y 1 with hh
  have hhm : Measurable h :=
    (Real.measurable_exp.comp ((wr13a_conv_meas hs0 μ).const_mul β)).mul (wr13a_Phi_meas hs0 hconv hβ n)
  have hh0 : ∀ y, 0 ≤ h y := fun y => mul_nonneg (Real.exp_pos _).le (wr13a_Phi_nonneg n y)
  have hhint : Integrable h μ :=
    Integrable.of_bound (C := Real.exp (β * Mg)) hhm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hh0 y)]
        calc h y ≤ Real.exp (β * Mg) * 1 :=
              mul_le_mul (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (hconv y) hβ))
                (wr13a_Phi_le_one hs0 hconv hβ n y) (wr13a_Phi_nonneg n y) (Real.exp_pos _).le
          _ = _ := mul_one _)
  have hpt : ∀ x, (Zq⁻¹ * ENNReal.ofReal (Real.exp (β * HRS.Whole.convMeasure (rieszKernel d s) μ x)) *
      wr13a_J d s μ lam β 1 n x) = (Zq⁻¹ * Zn) * ENNReal.ofReal (h x) := by
    intro x
    have hJ : wr13a_J d s μ lam β 1 n x = Zn * ENNReal.ofReal (poleNormalizer d s (n + 1) β μ x 1) := by
      rw [wr13a_ofReal_Phi hs0 hconv hβ n x, ← mul_assoc, ENNReal.mul_inv_cancel hZ0 hZt, one_mul]
    rw [hJ, hh, ENNReal.ofReal_mul (Real.exp_pos _).le]
    ring
  set κ : ℝ≥0∞ := Zq⁻¹ * Zn with hκ
  have hone : κ * ENNReal.ofReal (∫ y, h y ∂μ) = 1 := by
    have h1 := hmass
    rw [hπ, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at h1
    have h2 : ∫⁻ x, κ * ENNReal.ofReal (h x) ∂μ = 1 := by
      rw [← h1]
      exact lintegral_congr fun x => (hpt x).symm
    rw [lintegral_const_mul' _ _ (ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 hZq0) hZt),
      ← ofReal_integral_eq_lintegral_ofReal hhint (Filter.Eventually.of_forall hh0)] at h2
    exact h2
  have hZu : 0 < ∫ y, h y ∂μ := by
    by_contra hneg
    have : ENNReal.ofReal (∫ y, h y ∂μ) = 0 := ENNReal.ofReal_eq_zero.2 (not_lt.1 hneg)
    rw [this, mul_zero] at hone
    exact zero_ne_one hone
  have hκ' : κ = ENNReal.ofReal ((∫ y, h y ∂μ)⁻¹) := by
    rw [ENNReal.ofReal_inv_of_pos hZu]
    exact ENNReal.eq_inv_of_mul_eq_one_left hone
  have hfun : ∀ x, Zq⁻¹ * ENNReal.ofReal (Real.exp (β * HRS.Whole.convMeasure (rieszKernel d s) μ x)) *
      wr13a_J d s μ lam β 1 n x = ENNReal.ofReal (h x / ∫ y, h y ∂μ) := by
    intro x
    rw [hpt x, hκ', ← ENNReal.ofReal_mul (inv_nonneg.2 hZu.le), inv_mul_eq_div]
  refine ⟨hZu, hfun, ?_⟩
  rw [hπ]
  congr 1
  funext x
  exact hfun x


/-! ### Pole marginals -/

theorem wr13a_inv_mul_le {Zp Jm L B : ℝ≥0∞} {K : ℝ} (hJ0 : Jm ≠ 0) (hJt : Jm ≠ ∞)
    (hlow : ENNReal.ofReal (Real.exp (-K)) * Jm ≤ Zp) (hL : L ≤ B * Jm) :
    Zp⁻¹ * L ≤ ENNReal.ofReal (Real.exp K) * B := by
  have hc1 : ENNReal.ofReal (Real.exp (-K)) ≠ 0 := (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne'
  have hc1t : ENNReal.ofReal (Real.exp (-K)) ≠ ∞ := ENNReal.ofReal_ne_top
  calc Zp⁻¹ * L ≤ (ENNReal.ofReal (Real.exp (-K)) * Jm)⁻¹ * (B * Jm) :=
        mul_le_mul' (ENNReal.inv_le_inv.2 hlow) hL
    _ = ENNReal.ofReal (Real.exp K) * B := by
        rw [ENNReal.mul_inv (Or.inl hc1) (Or.inl hc1t), ← ENNReal.ofReal_inv_of_pos (Real.exp_pos _),
          ← Real.exp_neg, neg_neg]
        calc ENNReal.ofReal (Real.exp K) * Jm⁻¹ * (B * Jm)
            = ENNReal.ofReal (Real.exp K) * B * (Jm⁻¹ * Jm) := by ring
          _ = _ := by rw [ENNReal.inv_mul_cancel hJ0 hJt, mul_one]

theorem wr13a_lam_mul_le' {β r c : ℝ} (hβ : 0 ≤ β) {N : ℝ} (hN : 0 < N) (hr : r ≤ c * N) :
    β / N * r ≤ c * β := by
  rw [div_mul_eq_mul_div, div_le_iff₀ hN]
  nlinarith [mul_le_mul_of_nonneg_left hr hβ]

theorem wr13a_pole_weight_cons_le (hs0 : 0 < s)
    (hconv : ∀ z, HRS.Whole.convMeasure (rieszKernel d s) μ z ≤ Mg) {lam : ℝ} (hlam : 0 ≤ lam)
    (hβ : 0 ≤ β) (x y : Euc d) {n : ℕ} (Y : EucConfig d n) :
    ENNReal.ofReal (Real.exp (wr13a_Ep d s μ lam β x t (Fin.cons y Y : EucConfig d (n + 1)))) ≤
      ENNReal.ofReal (Real.exp (β * Mg)) * ENNReal.ofReal (Real.exp (-(t * lam) * rieszKernel d s (x - y))) *
        ENNReal.ofReal (Real.exp (wr13a_Ep d s μ lam β x t Y)) := by
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← ENNReal.ofReal_mul (by positivity), ← Real.exp_add,
    ← Real.exp_add]
  refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
  have := wr13a_Ep_cons_le (t := t) hs0 hconv hlam hβ x y Y
  linarith


/-- **Item 4, one-particle pole density**: `P^{x,t}_{(1)} ≤ μ.withDensity (C e^{-tλ g(x-·)})`,
`C = e^{2βM_g}`, for `N = m + 2 ≥ 2`, `0 ≤ t ≤ 1`, `λ = β/N`. -/
theorem wr13a_pole_one_le (hs0 : 0 < s) (hint : ∀ z, Integrable (fun y => rieszKernel d s (z - y)) μ)
    (hconv : ∀ z, HRS.Whole.convMeasure (rieszKernel d s) μ z ≤ Mg) (hMg : 0 ≤ Mg) (hβ : 0 ≤ β)
    (ht : 0 ≤ t) (ht1 : t ≤ 1) (m : ℕ) (x : Euc d) :
    HRS.Whole.firstMarginal (HRS.Whole.poleLaw d s (m + 2) β μ x t) ≤
      μ.withDensity fun y => ENNReal.ofReal (Real.exp (2 * β * Mg) *
        Real.exp (-(t * (β / ((m + 2 : ℕ) : ℝ))) * rieszKernel d s (x - y)) ) := by
  set lam : ℝ := β / ((m + 2 : ℕ) : ℝ) with hlamdef
  have hlam : 0 ≤ lam := div_nonneg hβ (Nat.cast_nonneg _)
  have hpl : HRS.Whole.poleLaw d s (m + 2) β μ x t =
      wr13a_tilt (Measure.pi fun _ : Fin (m + 1) => μ) (wr13a_Ep d s μ lam β x t) :=
    wr13a_poleLaw_eq hs0 hconv hβ ht (m + 2) x
  have hEpm := wr13a_Ep_meas hs0 μ lam β x t (n := m + 1)
  have hWm1 : Measurable fun X : EucConfig d (m + 1) =>
      ENNReal.ofReal (Real.exp (wr13a_Ep d s μ lam β x t X)) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp hEpm)
  have hWm0 : Measurable fun Y : EucConfig d m =>
      ENNReal.ofReal (Real.exp (wr13a_Ep d s μ lam β x t Y)) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (wr13a_Ep_meas hs0 μ lam β x t))
  obtain ⟨hJ0, hJt⟩ := wr13a_J_ne hs0 hconv hlam hβ ht m x
  set Jm := wr13a_J d s μ lam β t m x with hJm
  set B0 : Euc d → ℝ≥0∞ := fun y => ENNReal.ofReal (Real.exp (β * Mg)) *
    ENNReal.ofReal (Real.exp (-(t * lam) * rieszKernel d s (x - y))) with hB0
  have hB0m : Measurable B0 :=
    measurable_const.mul (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
      (((wr13a_g_meas hs0).comp (measurable_const.sub measurable_id)).const_mul _)))
  set K : ℝ := lam * (t + m) * Mg with hK
  have hKle : K ≤ β * Mg := by
    have h1 : lam * (t + m) ≤ β := by
      have := wr13a_lam_mul_le' (r := t + m) (c := 1) hβ (N := ((m + 2 : ℕ) : ℝ)) (by positivity)
        (by push_cast; linarith)
      linarith
    exact mul_le_mul_of_nonneg_right h1 hMg
  have hlow : ENNReal.ofReal (Real.exp (-K)) * Jm ≤
      ∫⁻ X : EucConfig d (m + 1), ENNReal.ofReal (Real.exp (wr13a_Ep d s μ lam β x t X))
        ∂(Measure.pi fun _ : Fin (m + 1) => μ) :=
    wr13a_lower_step hs0 hint hconv hlam hβ ht x m
  rw [hpl, wr13a_firstMarginal_def m]
  refine Measure.le_iff.2 fun A hA => ?_
  rw [Measure.map_apply (measurable_pi_apply 0) hA, withDensity_apply _ hA, ← lintegral_indicator hA]
  have hS : MeasurableSet ((fun X : EucConfig d (m + 1) => X 0) ⁻¹' A) := (measurable_pi_apply 0) hA
  rw [← lintegral_indicator_one hS, wr13a_lintegral_tilt _ hEpm _ (measurable_one.indicator hS)]
  -- the numerator
  have hNum : ∫⁻ X : EucConfig d (m + 1), ((fun X : EucConfig d (m + 1) => X 0) ⁻¹' A).indicator 1 X *
        ENNReal.ofReal (Real.exp (wr13a_Ep d s μ lam β x t X)) ∂(Measure.pi fun _ : Fin (m + 1) => μ) ≤
      (∫⁻ y, A.indicator B0 y ∂μ) * Jm := by
    rw [wr13a_lintegral_pi_succ μ (fun X : EucConfig d (m + 1) =>
      ((fun X : EucConfig d (m + 1) => X 0) ⁻¹' A).indicator 1 X *
        ENNReal.ofReal (Real.exp (wr13a_Ep d s μ lam β x t X))) ((measurable_one.indicator hS).mul hWm1)]
    calc _ ≤ ∫⁻ y, A.indicator B0 y * Jm ∂μ := by
          refine lintegral_mono fun y => ?_
          calc ∫⁻ Y : EucConfig d m, ((fun X : EucConfig d (m + 1) => X 0) ⁻¹' A).indicator 1
                  (Fin.cons y Y : EucConfig d (m + 1)) *
                ENNReal.ofReal (Real.exp (wr13a_Ep d s μ lam β x t (Fin.cons y Y : EucConfig d (m + 1))))
                ∂(Measure.pi fun _ : Fin m => μ)
              ≤ ∫⁻ Y : EucConfig d m, A.indicator B0 y *
                ENNReal.ofReal (Real.exp (wr13a_Ep d s μ lam β x t Y)) ∂(Measure.pi fun _ : Fin m => μ) := by
                refine lintegral_mono fun Y => ?_
                by_cases hy : y ∈ A
                · have hmem : (Fin.cons y Y : EucConfig d (m + 1)) ∈
                      (fun X : EucConfig d (m + 1) => X 0) ⁻¹' A := by simpa using hy
                  rw [Set.indicator_of_mem hmem, Pi.one_apply, one_mul, Set.indicator_of_mem hy]
                  exact wr13a_pole_weight_cons_le hs0 hconv hlam hβ x y Y
                · have hmem : (Fin.cons y Y : EucConfig d (m + 1)) ∉
                      (fun X : EucConfig d (m + 1) => X 0) ⁻¹' A := by simpa using hy
                  rw [Set.indicator_of_notMem hmem, zero_mul]
                  exact bot_le
            _ = A.indicator B0 y * Jm := lintegral_const_mul _ hWm0
      _ = (∫⁻ y, A.indicator B0 y ∂μ) * Jm := lintegral_mul_const' _ _ hJt
  have hfin := wr13a_inv_mul_le hJ0 hJt hlow hNum
  refine hfin.trans ?_
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun y => ?_
  by_cases hy : y ∈ A
  · simp only [Set.indicator_of_mem hy, hB0]
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← ENNReal.ofReal_mul (Real.exp_pos _).le]
    refine ENNReal.ofReal_le_ofReal ?_
    calc Real.exp K * (Real.exp (β * Mg) * Real.exp (-(t * lam) * rieszKernel d s (x - y)))
        = Real.exp (K + β * Mg) * Real.exp (-(t * lam) * rieszKernel d s (x - y)) := by
          rw [Real.exp_add]; ring
      _ ≤ Real.exp (2 * β * Mg) * Real.exp (-(t * lam) * rieszKernel d s (x - y)) :=
          mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 (by linarith)) (Real.exp_pos _).le
  · simp [Set.indicator_of_notMem hy]


theorem wr13a_secondMarginal_def (m : ℕ) (P : Measure (EucConfig d (m + 2))) :
    HRS.Whole.secondMarginal P =
      P.map (fun X : EucConfig d (m + 2) => (X 0, X (Fin.succ 0))) := by
  unfold HRS.Whole.secondMarginal
  rw [dif_pos (by omega : 2 ≤ m + 2)]
  rfl

theorem wr13a_meas_cons (y : Euc d) {n : ℕ} :
    Measurable (fun Y : EucConfig d n => (Fin.cons y Y : EucConfig d (n + 1))) := by
  refine measurable_pi_iff.2 fun j => ?_
  refine Fin.cases ?_ (fun i => ?_) j
  · simp only [Fin.cons_zero]
    exact measurable_const
  · simp only [Fin.cons_succ]
    exact measurable_pi_apply i

/-- Two-particle pole density for the tilt with `m + 2` particles (`N = m + 3`). -/
theorem wr13a_tilt_two_le (hs0 : 0 < s) (hint : ∀ z, Integrable (fun y => rieszKernel d s (z - y)) μ)
    (hconv : ∀ z, HRS.Whole.convMeasure (rieszKernel d s) μ z ≤ Mg) (hMg : 0 ≤ Mg) (hβ : 0 ≤ β)
    (ht : 0 ≤ t) (ht1 : t ≤ 1) (m : ℕ) (x : Euc d) :
    HRS.Whole.secondMarginal (wr13a_tilt (Measure.pi fun _ : Fin (m + 2) => μ)
        (wr13a_Ep d s μ (β / ((m + 3 : ℕ) : ℝ)) β x t)) ≤
      (μ.prod μ).withDensity fun yz => ENNReal.ofReal (Real.exp (4 * β * Mg) *
        Real.exp (-(t * (β / ((m + 3 : ℕ) : ℝ))) *
          (rieszKernel d s (x - yz.1) + rieszKernel d s (x - yz.2)))) := by
  set lam : ℝ := β / ((m + 3 : ℕ) : ℝ) with hlamdef
  have hlam : 0 ≤ lam := div_nonneg hβ (Nat.cast_nonneg _)
  have hgm := wr13a_g_meas (d := d) hs0
  have hWm2 : Measurable fun X : EucConfig d (m + 2) =>
      ENNReal.ofReal (Real.exp (wr13a_Ep d s μ lam β x t X)) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (wr13a_Ep_meas hs0 μ lam β x t))
  have hWm0 : Measurable fun Y : EucConfig d m =>
      ENNReal.ofReal (Real.exp (wr13a_Ep d s μ lam β x t Y)) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (wr13a_Ep_meas hs0 μ lam β x t))
  obtain ⟨hJ0, hJt⟩ := wr13a_J_ne hs0 hconv hlam hβ ht m x
  set Jm := wr13a_J d s μ lam β t m x with hJm
  set B0 : Euc d → ℝ≥0∞ := fun y => ENNReal.ofReal (Real.exp (β * Mg)) *
    ENNReal.ofReal (Real.exp (-(t * lam) * rieszKernel d s (x - y))) with hB0
  set Bp : Euc d × Euc d → ℝ≥0∞ := fun yz => B0 yz.1 * B0 yz.2 with hBp
  have hB0m : Measurable B0 :=
    measurable_const.mul (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
      ((hgm.comp (measurable_const.sub measurable_id)).const_mul _)))
  have hBpm : Measurable Bp := (hB0m.comp measurable_fst).mul (hB0m.comp measurable_snd)
  set K1 : ℝ := lam * (t + ((m + 1 : ℕ) : ℝ)) * Mg with hK1
  set K2 : ℝ := lam * (t + (m : ℝ)) * Mg with hK2
  have hKle : K1 + K2 ≤ 2 * β * Mg := by
    have h1 : lam * (2 * t + 2 * m + 1) ≤ 2 * β := by
      have := wr13a_lam_mul_le' (r := 2 * t + 2 * m + 1) (c := 2) hβ (N := ((m + 3 : ℕ) : ℝ))
        (by positivity) (by push_cast; linarith)
      linarith
    have h2 : K1 + K2 = lam * (2 * t + 2 * m + 1) * Mg := by
      simp only [hK1, hK2]; push_cast; ring
    rw [h2]
    exact mul_le_mul_of_nonneg_right h1 hMg
  have hlow : ENNReal.ofReal (Real.exp (-(K1 + K2))) * Jm ≤
      ∫⁻ X : EucConfig d (m + 2), ENNReal.ofReal (Real.exp (wr13a_Ep d s μ lam β x t X))
        ∂(Measure.pi fun _ : Fin (m + 2) => μ) := by
    have l1 := wr13a_lower_step hs0 hint hconv hlam hβ ht x m
    have l2 := wr13a_lower_step hs0 hint hconv hlam hβ ht x (m + 1)
    have e : ENNReal.ofReal (Real.exp (-(K1 + K2))) * Jm =
        ENNReal.ofReal (Real.exp (-K1)) * (ENNReal.ofReal (Real.exp (-K2)) * Jm) := by
      rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
      congr 3
      ring
    exact e.le.trans ((mul_le_mul' le_rfl l1).trans l2)
  have hT : Measurable (fun X : EucConfig d (m + 2) => (X 0, X (Fin.succ 0))) := by
    exact (measurable_pi_apply 0).prodMk (measurable_pi_apply _)
  rw [wr13a_secondMarginal_def]
  refine Measure.le_iff.2 fun A hA => ?_
  rw [Measure.map_apply hT hA, withDensity_apply _ hA, ← lintegral_indicator hA]
  have hS : MeasurableSet ((fun X : EucConfig d (m + 2) => (X 0, X (Fin.succ 0))) ⁻¹' A) := hT hA
  rw [← lintegral_indicator_one hS, wr13a_lintegral_tilt _ (wr13a_Ep_meas hs0 μ lam β x t) _
    (measurable_one.indicator hS)]
  have hNum : ∫⁻ X : EucConfig d (m + 2), ((fun X : EucConfig d (m + 2) => (X 0, X (Fin.succ 0))) ⁻¹' A).indicator 1 X *
        ENNReal.ofReal (Real.exp (wr13a_Ep d s μ lam β x t X)) ∂(Measure.pi fun _ : Fin (m + 2) => μ) ≤
      (∫⁻ yz, A.indicator Bp yz ∂(μ.prod μ)) * Jm := by
    rw [wr13a_lintegral_pi_succ μ (fun X : EucConfig d (m + 2) =>
      ((fun X : EucConfig d (m + 2) => (X 0, X (Fin.succ 0))) ⁻¹' A).indicator 1 X *
        ENNReal.ofReal (Real.exp (wr13a_Ep d s μ lam β x t X))) ((measurable_one.indicator hS).mul hWm2)]
    have hinner : ∀ y1 : Euc d, ∫⁻ Y1 : EucConfig d (m + 1),
        ((fun X : EucConfig d (m + 2) => (X 0, X (Fin.succ 0))) ⁻¹' A).indicator 1
          (Fin.cons y1 Y1 : EucConfig d (m + 2)) *
        ENNReal.ofReal (Real.exp (wr13a_Ep d s μ lam β x t (Fin.cons y1 Y1 : EucConfig d (m + 2))))
          ∂(Measure.pi fun _ : Fin (m + 1) => μ) ≤
        (∫⁻ y2, A.indicator Bp (y1, y2) ∂μ) * Jm := by
      intro y1
      have hmeas1 : Measurable fun Y1 : EucConfig d (m + 1) =>
          ((fun X : EucConfig d (m + 2) => (X 0, X (Fin.succ 0))) ⁻¹' A).indicator 1
            (Fin.cons y1 Y1 : EucConfig d (m + 2)) *
          ENNReal.ofReal (Real.exp (wr13a_Ep d s μ lam β x t (Fin.cons y1 Y1 : EucConfig d (m + 2)))) :=
        (((measurable_one.indicator hS).comp (wr13a_meas_cons y1)).mul
          (hWm2.comp (wr13a_meas_cons y1)))
      rw [wr13a_lintegral_pi_succ μ _ hmeas1]
      calc _ ≤ ∫⁻ y2, A.indicator Bp (y1, y2) * Jm ∂μ := by
            refine lintegral_mono fun y2 => ?_
            calc ∫⁻ Z : EucConfig d m, ((fun X : EucConfig d (m + 2) => (X 0, X (Fin.succ 0))) ⁻¹' A).indicator 1
                    (Fin.cons y1 (Fin.cons y2 Z : EucConfig d (m + 1)) : EucConfig d (m + 2)) *
                  ENNReal.ofReal (Real.exp (wr13a_Ep d s μ lam β x t
                    (Fin.cons y1 (Fin.cons y2 Z : EucConfig d (m + 1)) : EucConfig d (m + 2))))
                  ∂(Measure.pi fun _ : Fin m => μ)
                ≤ ∫⁻ Z : EucConfig d m, A.indicator Bp (y1, y2) *
                  ENNReal.ofReal (Real.exp (wr13a_Ep d s μ lam β x t Z)) ∂(Measure.pi fun _ : Fin m => μ) := by
                  refine lintegral_mono fun Z => ?_
                  by_cases hy : (y1, y2) ∈ A
                  · have hmem : (Fin.cons y1 (Fin.cons y2 Z : EucConfig d (m + 1)) : EucConfig d (m + 2)) ∈
                        (fun X : EucConfig d (m + 2) => (X 0, X (Fin.succ 0))) ⁻¹' A := by simpa using hy
                    rw [Set.indicator_of_mem hmem, Pi.one_apply, one_mul, Set.indicator_of_mem hy]
                    calc _ ≤ B0 y1 * ENNReal.ofReal (Real.exp (wr13a_Ep d s μ lam β x t
                          (Fin.cons y2 Z : EucConfig d (m + 1)))) :=
                          wr13a_pole_weight_cons_le hs0 hconv hlam hβ x y1 _
                      _ ≤ B0 y1 * (B0 y2 * ENNReal.ofReal (Real.exp (wr13a_Ep d s μ lam β x t Z))) :=
                          mul_le_mul' le_rfl (wr13a_pole_weight_cons_le hs0 hconv hlam hβ x y2 Z)
                      _ = Bp (y1, y2) * _ := by simp only [hBp, mul_assoc]
                  · have hmem : (Fin.cons y1 (Fin.cons y2 Z : EucConfig d (m + 1)) : EucConfig d (m + 2)) ∉
                        (fun X : EucConfig d (m + 2) => (X 0, X (Fin.succ 0))) ⁻¹' A := by simpa using hy
                    rw [Set.indicator_of_notMem hmem, zero_mul]
                    exact bot_le
              _ = A.indicator Bp (y1, y2) * Jm := lintegral_const_mul _ hWm0
        _ = (∫⁻ y2, A.indicator Bp (y1, y2) ∂μ) * Jm := lintegral_mul_const' _ _ hJt
    calc _ ≤ ∫⁻ y1, (∫⁻ y2, A.indicator Bp (y1, y2) ∂μ) * Jm ∂μ := lintegral_mono hinner
      _ = (∫⁻ y1, ∫⁻ y2, A.indicator Bp (y1, y2) ∂μ ∂μ) * Jm := lintegral_mul_const' _ _ hJt
      _ = (∫⁻ yz, A.indicator Bp yz ∂(μ.prod μ)) * Jm := by
          rw [lintegral_prod _ ((hBpm.indicator hA).aemeasurable)]
  have hfin := wr13a_inv_mul_le hJ0 hJt hlow hNum
  refine hfin.trans ?_
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun yz => ?_
  by_cases hy : yz ∈ A
  · simp only [Set.indicator_of_mem hy, hBp, hB0]
    simp (disch := positivity) only [← ENNReal.ofReal_mul]
    refine ENNReal.ofReal_le_ofReal ?_
    calc Real.exp (K1 + K2) * (Real.exp (β * Mg) * Real.exp (-(t * lam) * rieszKernel d s (x - yz.1)) *
          (Real.exp (β * Mg) * Real.exp (-(t * lam) * rieszKernel d s (x - yz.2))))
        = Real.exp ((K1 + K2) + (β * Mg + β * Mg) +
            (-(t * lam) * rieszKernel d s (x - yz.1) + -(t * lam) * rieszKernel d s (x - yz.2))) := by
          simp only [Real.exp_add]; ring
      _ ≤ Real.exp (4 * β * Mg + -(t * lam) * (rieszKernel d s (x - yz.1) + rieszKernel d s (x - yz.2))) :=
          Real.exp_le_exp.2 (by nlinarith)
      _ = _ := by rw [Real.exp_add]
  · simp [Set.indicator_of_notMem hy]


/-- **Item 4, two-particle pole density** (`N = m + 3 ≥ 3`). -/
theorem wr13a_pole_two_le (hs0 : 0 < s) (hint : ∀ z, Integrable (fun y => rieszKernel d s (z - y)) μ)
    (hconv : ∀ z, HRS.Whole.convMeasure (rieszKernel d s) μ z ≤ Mg) (hMg : 0 ≤ Mg) (hβ : 0 ≤ β)
    (ht : 0 ≤ t) (ht1 : t ≤ 1) (m : ℕ) (x : Euc d) :
    HRS.Whole.secondMarginal (HRS.Whole.poleLaw d s (m + 3) β μ x t) ≤
      (μ.prod μ).withDensity fun yz => ENNReal.ofReal (Real.exp (4 * β * Mg) *
        Real.exp (-(t * (β / ((m + 3 : ℕ) : ℝ))) *
          (rieszKernel d s (x - yz.1) + rieszKernel d s (x - yz.2)))) := by
  have hpl : HRS.Whole.poleLaw d s (m + 3) β μ x t =
      wr13a_tilt (Measure.pi fun _ : Fin (m + 2) => μ)
        (wr13a_Ep d s μ (β / ((m + 3 : ℕ) : ℝ)) β x t) :=
    wr13a_poleLaw_eq hs0 hconv hβ ht (m + 3) x
  rw [hpl]
  exact wr13a_tilt_two_le hs0 hint hconv hMg hβ ht ht1 m x

end Disint

/-! ### The bundle (interface C5, pole and cavity conjuncts for `0 < s < d`) -/

/-- **WR-13a bundle.**  For `d ≥ 2`, `0 < s < d`, `βp ≥ 0` and `M`, there is one constant `C ≥ 1`
(depending only on `d, s, βp, M`, quantified before `ρ, β, N, x, t`) such that for every probability
density `ρ ≤ M`, every `β ∈ [0, βp]` and every `N ≥ 2`, with `μ = ρ dx`, `Q = modulatedGibbs g N β μ`:

* `firstMarginal Q = μ.withDensity φ` with a measurable `0 ≤ φ ≤ C` everywhere (so `firstMarginal Q ≤ C • μ`;
  this is the sup part of `HasMarginalDensityBounds`);
* for every `x` and `t ∈ [0,1]`: `CavityWellDefined d s N β μ x t`, the one-particle pole density bound
  `firstMarginal (poleLaw ..) ≤ μ.withDensity (C e^{-tλ g(x-·)})`, and for `N ≥ 3` the two-particle bound
  `secondMarginal (poleLaw ..) ≤ (μ ⊗ μ).withDensity (C e^{-tλ (g(x-y) + g(x-z))})`, `λ = β/N`.

These are exactly the pole conjuncts of `Bias.StaticInputConclusion` (except the variance bound, WR-13b). -/
theorem wr13a_pole_bundle (hd : 2 ≤ d) (hs0 : 0 < s) (hsd : s < d) {βp : ℝ} (hβp : 0 ≤ βp) (M : ℝ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ ρ : Euc d → ℝ, HRS.Whole.IsProbDensity ρ → (∀ x, ρ x ≤ M) →
      ∀ β : ℝ, 0 ≤ β → β ≤ βp → ∀ N : ℕ, 2 ≤ N →
        (∃ φ : Euc d → ℝ, Measurable φ ∧
          HRS.Whole.firstMarginal (HRS.Whole.modulatedGibbs (rieszKernel d s) N β
              (HRS.Whole.withDensityReal ρ)) =
            (HRS.Whole.withDensityReal ρ).withDensity (fun x => ENNReal.ofReal (φ x)) ∧
          ∀ x, 0 ≤ φ x ∧ φ x ≤ C) ∧
        HRS.Whole.firstMarginal (HRS.Whole.modulatedGibbs (rieszKernel d s) N β
            (HRS.Whole.withDensityReal ρ)) ≤ ENNReal.ofReal C • HRS.Whole.withDensityReal ρ ∧
        ∀ x : Euc d, ∀ t ∈ Set.Icc (0 : ℝ) 1,
          CavityWellDefined d s N β (HRS.Whole.withDensityReal ρ) x t ∧
          HRS.Whole.firstMarginal (HRS.Whole.poleLaw d s N β (HRS.Whole.withDensityReal ρ) x t) ≤
            (HRS.Whole.withDensityReal ρ).withDensity
              (fun y => ENNReal.ofReal (C * Real.exp (-(t * (β / N)) * rieszKernel d s (x - y)))) ∧
          (3 ≤ N → HRS.Whole.secondMarginal
              (HRS.Whole.poleLaw d s N β (HRS.Whole.withDensityReal ρ) x t) ≤
            ((HRS.Whole.withDensityReal ρ).prod (HRS.Whole.withDensityReal ρ)).withDensity
              (fun yz => ENNReal.ofReal (C * Real.exp (-(t * (β / N)) *
                (rieszKernel d s (x - yz.1) + rieszKernel d s (x - yz.2)))))) := by
  have hd1 : 1 ≤ d := by omega
  refine ⟨Real.exp (4 * βp * |potentialBound d s M|), Real.one_le_exp (by positivity), ?_⟩
  intro ρ hρ hM β hβ hβp' N hN
  haveI := wr13a_isProb_density hρ
  set μ := HRS.Whole.withDensityReal ρ with hμ
  have hMg0 : 0 ≤ potentialBound d s M := wr13a_potentialBound_nonneg hd1 hs0 hsd hρ hM
  have hconv : ∀ z, HRS.Whole.convMeasure (rieszKernel d s) μ z ≤ potentialBound d s M :=
    wr13a_conv_le_density hd1 hs0 hsd hρ hM
  have hint : ∀ z, Integrable (fun y => rieszKernel d s (z - y)) μ := fun z =>
    (wr13a_potential_bound hd1 hs0 hsd hρ hM z).1
  have hC : ∀ k : ℝ, 0 ≤ k → k ≤ 4 →
      Real.exp (k * β * potentialBound d s M) ≤ Real.exp (4 * βp * |potentialBound d s M|) := by
    intro k hk0 hk4
    refine Real.exp_le_exp.2 ?_
    rw [abs_of_nonneg hMg0]
    have h1 : k * β ≤ 4 * βp := by nlinarith
    exact mul_le_mul_of_nonneg_right h1 hMg0
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 2 := ⟨N - 2, by omega⟩
  obtain ⟨hZu, hfun, hfm⟩ := wr13a_firstMarginal_eq hs0 hint hconv hMg0 hβ (m + 1)
  set φ : Euc d → ℝ := fun x => Real.exp (β * HRS.Whole.convMeasure (rieszKernel d s) μ x) *
    poleNormalizer d s (m + 1 + 1) β μ x 1 /
      ∫ y, Real.exp (β * HRS.Whole.convMeasure (rieszKernel d s) μ y) *
        poleNormalizer d s (m + 1 + 1) β μ y 1 ∂μ with hφ
  have hφm : Measurable φ :=
    ((Real.measurable_exp.comp ((wr13a_conv_meas hs0 μ).const_mul β)).mul
      (wr13a_Phi_meas hs0 hconv hβ (m + 1))).div_const _
  have hφ0 : ∀ x, 0 ≤ φ x := fun x =>
    div_nonneg (mul_nonneg (Real.exp_pos _).le (wr13a_Phi_nonneg (m + 1) x)) hZu.le
  have hφC : ∀ x, φ x ≤ Real.exp (4 * βp * |potentialBound d s M|) := by
    intro x
    have h1 : ENNReal.ofReal (φ x) ≤ ENNReal.ofReal (Real.exp (2 * β * potentialBound d s M)) := by
      rw [← hfun x]
      exact wr13a_phi_le hs0 hint hconv hMg0 hβ (m + 1) x
    exact ((ENNReal.ofReal_le_ofReal_iff (Real.exp_pos _).le).1 h1).trans (hC 2 (by norm_num) (by norm_num))
  have hQle : HRS.Whole.firstMarginal (HRS.Whole.modulatedGibbs (rieszKernel d s) (m + 2) β μ) ≤
      ENNReal.ofReal (Real.exp (4 * βp * |potentialBound d s M|)) • μ := by
    rw [hfm]
    refine Measure.le_iff.2 fun A hA => ?_
    rw [withDensity_apply _ hA, Measure.smul_apply, smul_eq_mul]
    calc ∫⁻ x in A, ENNReal.ofReal (φ x) ∂μ
        ≤ ∫⁻ _x in A, ENNReal.ofReal (Real.exp (4 * βp * |potentialBound d s M|)) ∂μ :=
          lintegral_mono fun x => ENNReal.ofReal_le_ofReal (hφC x)
      _ = _ := by rw [setLIntegral_const]
  refine ⟨⟨φ, hφm, hfm, fun x => ⟨hφ0 x, hφC x⟩⟩, hQle, ?_⟩
  intro x t ht
  refine ⟨wr13a_cavityWellDefined_density hd hs0 hsd hρ hM hβ (m + 2) hN x ht, ?_, ?_⟩
  · refine (wr13a_pole_one_le hs0 hint hconv hMg0 hβ ht.1 ht.2 m x).trans ?_
    refine withDensity_mono (Filter.Eventually.of_forall fun y => ?_)
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (hC 2 (by norm_num) (by norm_num))
      (Real.exp_pos _).le)
  · intro h3
    obtain ⟨k, hk⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    subst hk
    refine (wr13a_pole_two_le hs0 hint hconv hMg0 hβ ht.1 ht.2 k x).trans ?_
    refine withDensity_mono (Filter.Eventually.of_forall fun yz => ?_)
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (hC 4 (by norm_num) (by norm_num))
      (Real.exp_pos _).le)

/-! ### Density-level wrappers for the exact cavity identity and the first-marginal formula -/

/-- Item 3 for `μ = ρ dx`, `ρ ≤ M`, `β ≥ 0`: the exact cavity identity. -/
theorem wr13a_cavity_disintegration_density (hd : 2 ≤ d) (hs0 : 0 < s) (hsd : s < d)
    {ρ : Euc d → ℝ} (hρ : HRS.Whole.IsProbDensity ρ) {M : ℝ} (hM : ∀ x, ρ x ≤ M) {β : ℝ}
    (hβ : 0 ≤ β) (n : ℕ) (F : Euc d × EucConfig d n → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ X : EucConfig d (n + 1), F (X 0, Fin.tail X)
        ∂(HRS.Whole.modulatedGibbs (rieszKernel d s) (n + 1) β (HRS.Whole.withDensityReal ρ)) =
      ∫⁻ x, ∫⁻ Y : EucConfig d n, F (x, Y)
          ∂(HRS.Whole.poleLaw d s (n + 1) β (HRS.Whole.withDensityReal ρ) x 1)
        ∂(HRS.Whole.firstMarginal (HRS.Whole.modulatedGibbs (rieszKernel d s) (n + 1) β
          (HRS.Whole.withDensityReal ρ))) := by
  haveI := wr13a_isProb_density hρ
  exact wr13a_cavity_disintegration hs0
    (wr13a_conv_le_density (by omega) hs0 hsd hρ hM) hβ n F hF

/-- Item 3 for `μ = ρ dx`, `ρ ≤ M`, `β ≥ 0`: `π_N = μ.withDensity (e^{β g*μ} Φ_x / ∫ e^{β g*μ} Φ)`. -/
theorem wr13a_firstMarginal_eq_density (hd : 2 ≤ d) (hs0 : 0 < s) (hsd : s < d)
    {ρ : Euc d → ℝ} (hρ : HRS.Whole.IsProbDensity ρ) {M : ℝ} (hM : ∀ x, ρ x ≤ M) {β : ℝ}
    (hβ : 0 ≤ β) (n : ℕ) :
    HRS.Whole.firstMarginal (HRS.Whole.modulatedGibbs (rieszKernel d s) (n + 1) β
        (HRS.Whole.withDensityReal ρ)) =
      (HRS.Whole.withDensityReal ρ).withDensity fun x => ENNReal.ofReal
        (Real.exp (β * HRS.Whole.convMeasure (rieszKernel d s) (HRS.Whole.withDensityReal ρ) x) *
          poleNormalizer d s (n + 1) β (HRS.Whole.withDensityReal ρ) x 1 /
          ∫ y, Real.exp (β * HRS.Whole.convMeasure (rieszKernel d s) (HRS.Whole.withDensityReal ρ) y) *
            poleNormalizer d s (n + 1) β (HRS.Whole.withDensityReal ρ) y 1
              ∂(HRS.Whole.withDensityReal ρ)) := by
  haveI := wr13a_isProb_density hρ
  exact (wr13a_firstMarginal_eq hs0 (fun z => (wr13a_potential_bound (by omega) hs0 hsd hρ hM z).1)
    (wr13a_conv_le_density (by omega) hs0 hsd hρ hM)
    (wr13a_potentialBound_nonneg (by omega) hs0 hsd hρ hM) hβ n).2.2

end HRS.MS.Wr
