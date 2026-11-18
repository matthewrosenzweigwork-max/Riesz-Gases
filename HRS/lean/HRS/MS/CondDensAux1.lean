import HRS.MS.StaticInput

/-!
# HRS.MS.CondDensAux1 -- conditional density of the pole law: kernel computation (S74, part 1)

Packet S74 (S7.4 `HRS.Whole.conditional_density`), namespace `HRS.MS.Wr`, helper prefix `s74_`.

Notation: `N = m + 2`, `n = m + 1` cavity particles, `λ = β/(m+2)`, `μ^{⊗m}` the product law of the tail
`Y' = (y_2,…,y_n)`, and `u(Y',y) = λ ∑_j g(y - Y'_j) - β (g*μ)(y)` (`s74_u`; `condPotential` is `u (tail Y)`).

* `s74_condPotential_eq`: `condPotential d s (m+2) β μ Y y = s74_u .. (Fin.tail Y) y`.
* `s74_lintegral_pole`: for measurable `F` on `ℝ^d × (ℝ^d)^m`,
  `∫⁻ F(X 0, tail X) d(poleLaw ..) = J⁻¹ ∫⁻_y ∫⁻_{Y'} F(y,Y') e^{-u(Y',y) - tλ g(x-y)} e^{Ep(Y')}`.
* `s74_a`: the prefactor `a(y) = J⁻¹ ∫⁻_{Y'} e^{-u(Y',y)} e^{Ep(Y')}` (as an `ℝ≥0∞`-valued function), measurable,
  `a ≤ e^{2βM_g}`, and `firstMarginal (poleLaw ..) = μ.withDensity (e^{-tλ g(x-·)} a)`.
* `s74_a_eq_lintegral_ratio`: `a(y) = ∫⁻ e^{-u(tail Y,y)} Zc(tail Y)⁻¹ d(poleLaw ..)(Y)`, where
  `Zc(Y') = ∫⁻_z e^{-u(Y',z) - tλ g(x-z)} dμ(z)` (the conditional normaliser).

No frozen file is edited.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal BigOperators

noncomputable section

namespace HRS.MS.Wr

open HRS.Whole (rieszKernel EucConfig)

variable {d : ℕ} {s : ℝ}

/-- `u(Y',y) = λ ∑_j g(y - Y'_j) - β (g*μ)(y)`. -/
def s74_u (d : ℕ) (s : ℝ) (μ : Measure (Euc d)) (lam β : ℝ) {m : ℕ} (Y : EucConfig d m) (y : Euc d) : ℝ :=
  lam * ∑ j, rieszKernel d s (y - Y j) - β * HRS.Whole.convMeasure (rieszKernel d s) μ y

/-- The conditional normaliser `Zc(Y') = ∫⁻_z e^{-u(Y',z) - tλ g(x-z)} dμ(z)`. -/
def s74_Zc (d : ℕ) (s : ℝ) (μ : Measure (Euc d)) (lam β t : ℝ) (x : Euc d) {m : ℕ}
    (Y : EucConfig d m) : ℝ≥0∞ :=
  ∫⁻ z, ENNReal.ofReal (Real.exp (-(s74_u d s μ lam β Y z) - t * lam * rieszKernel d s (x - z))) ∂μ

/-- The numerator of the prefactor: `∫⁻_{Y'} e^{-u(Y',y)} e^{Ep(Y')} dμ^{⊗m}`. -/
def s74_aNum (d : ℕ) (s : ℝ) (μ : Measure (Euc d)) (lam β t : ℝ) (x : Euc d) (m : ℕ) (y : Euc d) : ℝ≥0∞ :=
  ∫⁻ Y : EucConfig d m, ENNReal.ofReal (Real.exp (-(s74_u d s μ lam β Y y))) *
    ENNReal.ofReal (Real.exp (wr13a_Ep d s μ lam β x t Y)) ∂(Measure.pi fun _ : Fin m => μ)

/-- The prefactor `a(y) = J_{m+1}(x,t)⁻¹ ∫⁻ e^{-u(Y',y)} e^{Ep(Y')} dμ^{⊗m}`. -/
def s74_a (d : ℕ) (s : ℝ) (μ : Measure (Euc d)) (lam β t : ℝ) (x : Euc d) (m : ℕ) (y : Euc d) : ℝ≥0∞ :=
  (wr13a_J d s μ lam β t (m + 1) x)⁻¹ * s74_aNum d s μ lam β t x m y

section Basic

variable {μ : Measure (Euc d)} {Mg lam β t : ℝ}

theorem s74_u_meas2 (hs0 : 0 < s) (μ : Measure (Euc d)) [SFinite μ] (lam β : ℝ) {m : ℕ} :
    Measurable (fun p : EucConfig d m × Euc d => s74_u d s μ lam β p.1 p.2) := by
  unfold s74_u
  refine Measurable.sub ?_ ?_
  · exact (Finset.measurable_sum _ fun j _ =>
      (wr13a_g_meas hs0).comp (measurable_snd.sub ((measurable_pi_apply j).comp measurable_fst))).const_mul _
  · exact ((wr13a_conv_meas hs0 μ).comp measurable_snd).const_mul _

theorem s74_u_meas_y (hs0 : 0 < s) (μ : Measure (Euc d)) [SFinite μ] (lam β : ℝ) {m : ℕ}
    (Y : EucConfig d m) : Measurable (fun y => s74_u d s μ lam β Y y) := by
  have h := (s74_u_meas2 hs0 μ lam β (m := m)).comp (measurable_prodMk_left (x := Y) (β := Euc d))
  exact h

theorem s74_u_meas_Y (hs0 : 0 < s) (μ : Measure (Euc d)) [SFinite μ] (lam β : ℝ) {m : ℕ}
    (y : Euc d) : Measurable (fun Y : EucConfig d m => s74_u d s μ lam β Y y) := by
  have h := (s74_u_meas2 hs0 μ lam β (m := m)).comp (measurable_prodMk_right (y := y) (α := EucConfig d m))
  exact h

theorem s74_neg_u_le (hs0 : 0 < s) (hconv : ∀ z, HRS.Whole.convMeasure (rieszKernel d s) μ z ≤ Mg)
    (hlam : 0 ≤ lam) (hβ : 0 ≤ β) {m : ℕ} (Y : EucConfig d m) (y : Euc d) :
    -(s74_u d s μ lam β Y y) ≤ β * Mg := by
  unfold s74_u
  have h1 : 0 ≤ lam * ∑ j, rieszKernel d s (y - Y j) :=
    mul_nonneg hlam (Finset.sum_nonneg fun j _ => wr13a_g_nonneg hs0 _)
  have h2 : β * HRS.Whole.convMeasure (rieszKernel d s) μ y ≤ β * Mg :=
    mul_le_mul_of_nonneg_left (hconv y) hβ
  linarith

theorem s74_Ep_cons (μ : Measure (Euc d)) (lam β : ℝ) (x : Euc d) (t : ℝ) {m : ℕ} (y : Euc d)
    (Y : EucConfig d m) :
    wr13a_Ep d s μ lam β x t (Fin.cons y Y : EucConfig d (m + 1)) =
      (-(s74_u d s μ lam β Y y) - t * lam * rieszKernel d s (x - y)) + wr13a_Ep d s μ lam β x t Y := by
  rw [wr13a_Ep_cons]
  unfold s74_u
  ring

theorem s74_condPotential_eq (μ : Measure (Euc d)) (β : ℝ) (m : ℕ) (Y : EucConfig d (m + 1))
    (y : Euc d) :
    HRS.Whole.condPotential d s (m + 2) β μ Y y =
      s74_u d s μ (β / ((m + 2 : ℕ) : ℝ)) β (Fin.tail Y) y := by
  have h : HRS.Whole.condPotential d s (m + 2) β μ Y y =
      (β / ((m + 2 : ℕ) : ℝ)) * ∑ j : Fin (m + 1),
        (if (j : ℕ) = 0 then 0 else rieszKernel d s (y - Y j)) -
        β * HRS.Whole.convMeasure (rieszKernel d s) μ y := rfl
  rw [h]
  unfold s74_u
  rw [Fin.sum_univ_succ]
  simp [Fin.tail, Fin.succ_ne_zero]

end Basic

section Pole

variable {μ : Measure (Euc d)} [IsProbabilityMeasure μ] {Mg β t : ℝ}

theorem s74_W_meas (hs0 : 0 < s) (μ : Measure (Euc d)) [SFinite μ] (lam β : ℝ) (x : Euc d) (t : ℝ) (m : ℕ) :
    Measurable fun Y : EucConfig d m => ENNReal.ofReal (Real.exp (wr13a_Ep d s μ lam β x t Y)) :=
  ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (wr13a_Ep_meas hs0 μ lam β x t))

theorem s74_u_meas2' (hs0 : 0 < s) (μ : Measure (Euc d)) [SFinite μ] (lam β : ℝ) {m : ℕ} :
    Measurable (fun p : Euc d × EucConfig d m => s74_u d s μ lam β p.2 p.1) := by
  have h := (s74_u_meas2 hs0 μ lam β (m := m)).comp (measurable_swap (α := Euc d) (β := EucConfig d m))
  exact h

theorem s74_lintegral_pole (hs0 : 0 < s)
    (hconv : ∀ z, HRS.Whole.convMeasure (rieszKernel d s) μ z ≤ Mg) (hβ : 0 ≤ β) (ht : 0 ≤ t) (m : ℕ)
    (x : Euc d) (F : Euc d × EucConfig d m → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ X : EucConfig d (m + 1), F (X 0, Fin.tail X) ∂(HRS.Whole.poleLaw d s (m + 2) β μ x t) =
      (wr13a_J d s μ (β / ((m + 2 : ℕ) : ℝ)) β t (m + 1) x)⁻¹ *
        ∫⁻ y, ∫⁻ Y : EucConfig d m, F (y, Y) *
          ENNReal.ofReal (Real.exp (-(s74_u d s μ (β / ((m + 2 : ℕ) : ℝ)) β Y y) -
            t * (β / ((m + 2 : ℕ) : ℝ)) * rieszKernel d s (x - y))) *
          ENNReal.ofReal (Real.exp (wr13a_Ep d s μ (β / ((m + 2 : ℕ) : ℝ)) β x t Y))
            ∂(Measure.pi fun _ : Fin m => μ) ∂μ := by
  set lam : ℝ := β / ((m + 2 : ℕ) : ℝ) with hlam
  have h : HRS.Whole.poleLaw d s (m + 2) β μ x t =
      wr13a_tilt (Measure.pi fun _ : Fin (m + 1) => μ) (wr13a_Ep d s μ lam β x t) :=
    wr13a_poleLaw_eq hs0 hconv hβ ht (m + 2) x
  have hEpm := wr13a_Ep_meas hs0 μ lam β x t (n := m + 1)
  have hT : Measurable fun X : EucConfig d (m + 1) => (X 0, Fin.tail X) :=
    (measurable_pi_apply 0).prodMk (measurable_pi_iff.2 fun j => measurable_pi_apply _)
  have hFT : Measurable fun X : EucConfig d (m + 1) => F (X 0, Fin.tail X) := hF.comp hT
  have hWm1 : Measurable fun X : EucConfig d (m + 1) =>
      ENNReal.ofReal (Real.exp (wr13a_Ep d s μ lam β x t X)) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp hEpm)
  rw [h, wr13a_lintegral_tilt _ hEpm _ hFT]
  show _ = (wr13a_J d s μ lam β t (m + 1) x)⁻¹ * _
  congr 1
  rw [wr13a_lintegral_pi_succ μ (fun X : EucConfig d (m + 1) => F (X 0, Fin.tail X) *
    ENNReal.ofReal (Real.exp (wr13a_Ep d s μ lam β x t X))) (hFT.mul hWm1)]
  refine lintegral_congr fun y => lintegral_congr fun Y => ?_
  simp only [Fin.cons_zero, Fin.tail_cons]
  rw [s74_Ep_cons, Real.exp_add, ENNReal.ofReal_mul (Real.exp_pos _).le]
  ring

/-- The conditional normaliser is at most `e^{βM_g}`. -/
theorem s74_Zc_le (hs0 : 0 < s) (hconv : ∀ z, HRS.Whole.convMeasure (rieszKernel d s) μ z ≤ Mg)
    {lam : ℝ} (hlam : 0 ≤ lam) (hβ : 0 ≤ β) (ht : 0 ≤ t) (x : Euc d) {m : ℕ} (Y : EucConfig d m) :
    s74_Zc d s μ lam β t x Y ≤ ENNReal.ofReal (Real.exp (β * Mg)) := by
  unfold s74_Zc
  calc ∫⁻ z, ENNReal.ofReal (Real.exp (-(s74_u d s μ lam β Y z) - t * lam * rieszKernel d s (x - z))) ∂μ
      ≤ ∫⁻ _z, ENNReal.ofReal (Real.exp (β * Mg)) ∂μ := by
        refine lintegral_mono fun z => ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
        have h1 := s74_neg_u_le hs0 hconv hlam hβ Y z
        have h2 : 0 ≤ t * lam * rieszKernel d s (x - z) :=
          mul_nonneg (mul_nonneg ht hlam) (wr13a_g_nonneg hs0 _)
        linarith
    _ = ENNReal.ofReal (Real.exp (β * Mg)) := by simp

/-- The conditional normaliser is at least `e^{-βM_g}` (Jensen). -/
theorem s74_Zc_ge (hs0 : 0 < s) (hint : ∀ z, Integrable (fun y => rieszKernel d s (z - y)) μ)
    (hconv : ∀ z, HRS.Whole.convMeasure (rieszKernel d s) μ z ≤ Mg) (hMg : 0 ≤ Mg)
    {lam : ℝ} (hlam : 0 ≤ lam) (hβ : 0 ≤ β) (ht : 0 ≤ t) (x : Euc d) {m : ℕ} (Y : EucConfig d m)
    (hK : lam * (t + m) ≤ β) :
    ENNReal.ofReal (Real.exp (-(β * Mg))) ≤ s74_Zc d s μ lam β t x Y := by
  have hgm : Measurable (rieszKernel d s) := wr13a_g_meas hs0
  set u : Euc d → ℝ := fun y => lam * ∑ j, rieszKernel d s (y - Y j) + t * lam * rieszKernel d s (x - y)
    with hu
  have hu1 : Measurable u :=
    ((Finset.measurable_sum _ fun j _ => hgm.comp (measurable_id.sub measurable_const)).const_mul _).add
      ((hgm.comp (measurable_const.sub measurable_id)).const_mul _)
  obtain ⟨hui, huK⟩ := wr13a_u_integral hs0 hint hconv hlam ht x Y
  have hu0 : ∀ y, 0 ≤ u y := fun y => by
    simp only [hu]
    exact add_nonneg (mul_nonneg hlam (Finset.sum_nonneg fun j _ => wr13a_g_nonneg hs0 _))
      (mul_nonneg (mul_nonneg ht hlam) (wr13a_g_nonneg hs0 _))
  have hj := wr13a_jensen μ hui hu0 huK
  have hint2 : Integrable (fun y => Real.exp (-(u y))) μ :=
    Integrable.of_bound (C := 1) ((Real.measurable_exp.comp hu1.neg).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        exact Real.exp_le_one_iff.2 (by linarith [hu0 y]))
  have hKle : lam * (t + m) * Mg ≤ β * Mg := mul_le_mul_of_nonneg_right hK hMg
  calc ENNReal.ofReal (Real.exp (-(β * Mg))) ≤ ENNReal.ofReal (Real.exp (-(lam * (t + m) * Mg))) :=
        ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (by linarith))
    _ ≤ ENNReal.ofReal (∫ y, Real.exp (-(u y)) ∂μ) := ENNReal.ofReal_le_ofReal hj
    _ = ∫⁻ y, ENNReal.ofReal (Real.exp (-(u y))) ∂μ :=
        ofReal_integral_eq_lintegral_ofReal hint2 (Filter.Eventually.of_forall fun y => (Real.exp_pos _).le)
    _ ≤ s74_Zc d s μ lam β t x Y := by
        unfold s74_Zc
        refine lintegral_mono fun z => ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
        have h3 := mul_nonneg hβ (wr13a_conv_nonneg hs0 μ z)
        simp only [hu, s74_u]
        linarith

theorem s74_Zc_meas (hs0 : 0 < s) (μ : Measure (Euc d)) [SFinite μ] (lam β t : ℝ) (x : Euc d) (m : ℕ) :
    Measurable (s74_Zc d s μ lam β t x (m := m)) := by
  unfold s74_Zc
  have h2 : Measurable (fun p : EucConfig d m × Euc d =>
      ENNReal.ofReal (Real.exp (-(s74_u d s μ lam β p.1 p.2) - t * lam * rieszKernel d s (x - p.2)))) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (((s74_u_meas2 hs0 μ lam β).neg).sub
      (((wr13a_g_meas hs0).comp (measurable_const.sub measurable_snd)).const_mul _)))
  exact Measurable.lintegral_prod_right' h2

theorem s74_aNum_meas (hs0 : 0 < s) (μ : Measure (Euc d)) [IsProbabilityMeasure μ] (lam β t : ℝ) (x : Euc d) (m : ℕ) :
    Measurable (s74_aNum d s μ lam β t x m) := by
  unfold s74_aNum
  have h2 : Measurable (fun p : Euc d × EucConfig d m =>
      ENNReal.ofReal (Real.exp (-(s74_u d s μ lam β p.2 p.1))) *
        ENNReal.ofReal (Real.exp (wr13a_Ep d s μ lam β x t p.2))) :=
    (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (s74_u_meas2' hs0 μ lam β).neg)).mul
      ((s74_W_meas hs0 μ lam β x t m).comp measurable_snd)
  exact Measurable.lintegral_prod_right' h2

theorem s74_a_meas (hs0 : 0 < s) (μ : Measure (Euc d)) [IsProbabilityMeasure μ] (lam β t : ℝ) (x : Euc d) (m : ℕ) :
    Measurable (s74_a d s μ lam β t x m) :=
  measurable_const.mul (s74_aNum_meas hs0 μ lam β t x m)

end Pole

section Pole2

variable {μ : Measure (Euc d)} [IsProbabilityMeasure μ] {Mg β t : ℝ}

theorem s74_inner (lam β t : ℝ) (x : Euc d) (y : Euc d) (m : ℕ) :
    ∫⁻ Y : EucConfig d m, ENNReal.ofReal (Real.exp (-(s74_u d s μ lam β Y y) -
        t * lam * rieszKernel d s (x - y))) *
      ENNReal.ofReal (Real.exp (wr13a_Ep d s μ lam β x t Y)) ∂(Measure.pi fun _ : Fin m => μ) =
    ENNReal.ofReal (Real.exp (-(t * lam) * rieszKernel d s (x - y))) * s74_aNum d s μ lam β t x m y := by
  unfold s74_aNum
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr fun Y => ?_
  have : -(s74_u d s μ lam β Y y) - t * lam * rieszKernel d s (x - y) =
      -(t * lam) * rieszKernel d s (x - y) + -(s74_u d s μ lam β Y y) := by ring
  rw [this, Real.exp_add, ENNReal.ofReal_mul (Real.exp_pos _).le]
  ring

theorem s74_firstMarginal_eq (hs0 : 0 < s)
    (hconv : ∀ z, HRS.Whole.convMeasure (rieszKernel d s) μ z ≤ Mg) (hβ : 0 ≤ β) (ht : 0 ≤ t) (m : ℕ)
    (x : Euc d) :
    HRS.Whole.firstMarginal (HRS.Whole.poleLaw d s (m + 2) β μ x t) =
      μ.withDensity fun y => ENNReal.ofReal
        (Real.exp (-(t * (β / ((m + 2 : ℕ) : ℝ))) * rieszKernel d s (x - y))) *
        s74_a d s μ (β / ((m + 2 : ℕ) : ℝ)) β t x m y := by
  set lam : ℝ := β / ((m + 2 : ℕ) : ℝ) with hlamdef
  have hlam : 0 ≤ lam := div_nonneg hβ (Nat.cast_nonneg _)
  obtain ⟨hJ0, hJt⟩ := wr13a_J_ne hs0 hconv hlam hβ ht (m + 1) x
  have hfm : HRS.Whole.firstMarginal (HRS.Whole.poleLaw d s (m + 2) β μ x t) =
      (HRS.Whole.poleLaw d s (m + 2) β μ x t).map (fun X : EucConfig d (m + 1) => X 0) := by
    unfold HRS.Whole.firstMarginal
    rw [dif_pos (by omega : 0 < m + 2 - 1)]
    rfl
  ext B hB
  rw [hfm, Measure.map_apply (measurable_pi_apply 0) hB, withDensity_apply _ hB,
    ← lintegral_indicator hB]
  set F : Euc d × EucConfig d m → ℝ≥0∞ := fun p => B.indicator 1 p.1 with hF
  have hFm : Measurable F := (measurable_one.indicator hB).comp measurable_fst
  have h1 : HRS.Whole.poleLaw d s (m + 2) β μ x t ((fun X : EucConfig d (m + 1) => X 0) ⁻¹' B) =
      ∫⁻ X : EucConfig d (m + 1), F (X 0, Fin.tail X) ∂(HRS.Whole.poleLaw d s (m + 2) β μ x t) := by
    have hS : MeasurableSet ((fun X : EucConfig d (m + 1) => X 0) ⁻¹' B) :=
      (measurable_pi_apply (0 : Fin (m + 1))) hB
    rw [← lintegral_indicator_one hS]
    refine lintegral_congr fun X => ?_
    by_cases h : X 0 ∈ B <;> simp [Set.indicator, hF, h]
  rw [h1, s74_lintegral_pole hs0 hconv hβ ht m x F hFm,
    ← lintegral_const_mul' _ _ (ENNReal.inv_ne_top.2 hJ0)]
  refine lintegral_congr fun y => ?_
  by_cases hy : y ∈ B
  · have hFy : ∀ Y : EucConfig d m, F (y, Y) = 1 := fun Y => by simp [hF, hy]
    simp only [hFy, one_mul, Set.indicator_of_mem hy]
    rw [s74_inner, s74_a]
    ring
  · have hFy : ∀ Y : EucConfig d m, F (y, Y) = 0 := fun Y => by simp [hF, hy]
    simp [hFy, Set.indicator_of_notMem hy]

theorem s74_a_le (hs0 : 0 < s) (hint : ∀ z, Integrable (fun y => rieszKernel d s (z - y)) μ)
    (hconv : ∀ z, HRS.Whole.convMeasure (rieszKernel d s) μ z ≤ Mg) (hMg : 0 ≤ Mg) (hβ : 0 ≤ β)
    (ht : 0 ≤ t) (ht1 : t ≤ 1) (m : ℕ) (x y : Euc d) :
    s74_a d s μ (β / ((m + 2 : ℕ) : ℝ)) β t x m y ≤ ENNReal.ofReal (Real.exp (2 * β * Mg)) := by
  set lam : ℝ := β / ((m + 2 : ℕ) : ℝ) with hlamdef
  have hlam : 0 ≤ lam := div_nonneg hβ (Nat.cast_nonneg _)
  obtain ⟨hJ0, hJt⟩ := wr13a_J_ne hs0 hconv hlam hβ ht m x
  set Jm := wr13a_J d s μ lam β t m x with hJm
  set K : ℝ := lam * (t + m) * Mg with hK
  have hKle : K ≤ β * Mg := by
    have h := wr13a_lam_mul_le' (r := t + m) (c := 1) hβ (N := ((m + 2 : ℕ) : ℝ)) (by positivity)
      (by push_cast; linarith)
    exact mul_le_mul_of_nonneg_right (by linarith) hMg
  have hlow : ENNReal.ofReal (Real.exp (-K)) * Jm ≤ wr13a_J d s μ lam β t (m + 1) x :=
    wr13a_lower_step hs0 hint hconv hlam hβ ht x m
  have hL : s74_aNum d s μ lam β t x m y ≤ ENNReal.ofReal (Real.exp (β * Mg)) * Jm := by
    unfold s74_aNum
    rw [hJm, wr13a_J, ← lintegral_const_mul _ (s74_W_meas hs0 μ lam β x t m)]
    refine lintegral_mono fun Y => ?_
    exact mul_le_mul_left (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2
      (s74_neg_u_le hs0 hconv hlam hβ Y y))) _
  have h := wr13a_inv_mul_le hJ0 hJt hlow hL
  calc s74_a d s μ lam β t x m y = (wr13a_J d s μ lam β t (m + 1) x)⁻¹ * s74_aNum d s μ lam β t x m y := rfl
    _ ≤ ENNReal.ofReal (Real.exp K) * ENNReal.ofReal (Real.exp (β * Mg)) := h
    _ ≤ ENNReal.ofReal (Real.exp (β * Mg)) * ENNReal.ofReal (Real.exp (β * Mg)) :=
        mul_le_mul_left (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 hKle)) _
    _ = ENNReal.ofReal (Real.exp (2 * β * Mg)) := by
        rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
        congr 2
        ring

/-- The prefactor as a real function. -/
def s74_A (d : ℕ) (s : ℝ) (μ : Measure (Euc d)) (lam β t : ℝ) (x : Euc d) (m : ℕ) (y : Euc d) : ℝ :=
  (s74_a d s μ lam β t x m y).toReal

theorem s74_ofReal_A (hs0 : 0 < s) (hint : ∀ z, Integrable (fun y => rieszKernel d s (z - y)) μ)
    (hconv : ∀ z, HRS.Whole.convMeasure (rieszKernel d s) μ z ≤ Mg) (hMg : 0 ≤ Mg) (hβ : 0 ≤ β)
    (ht : 0 ≤ t) (ht1 : t ≤ 1) (m : ℕ) (x y : Euc d) :
    ENNReal.ofReal (s74_A d s μ (β / ((m + 2 : ℕ) : ℝ)) β t x m y) =
      s74_a d s μ (β / ((m + 2 : ℕ) : ℝ)) β t x m y :=
  ENNReal.ofReal_toReal (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (s74_a_le hs0 hint hconv hMg hβ ht ht1 m x y))

theorem s74_A_nonneg (lam β t : ℝ) (x : Euc d) (m : ℕ) (y : Euc d) :
    0 ≤ s74_A d s μ lam β t x m y := ENNReal.toReal_nonneg

theorem s74_A_meas (hs0 : 0 < s) (lam β t : ℝ) (x : Euc d) (m : ℕ) :
    Measurable (s74_A d s μ lam β t x m) :=
  (s74_a_meas hs0 μ lam β t x m).ennreal_toReal

/-- The first marginal of the pole law has density `e^{-tλ g(x-y)} A(y)` with respect to `μ`. -/
theorem s74_firstMarginal_A (hs0 : 0 < s) (hint : ∀ z, Integrable (fun y => rieszKernel d s (z - y)) μ)
    (hconv : ∀ z, HRS.Whole.convMeasure (rieszKernel d s) μ z ≤ Mg) (hMg : 0 ≤ Mg) (hβ : 0 ≤ β)
    (ht : 0 ≤ t) (ht1 : t ≤ 1) (m : ℕ) (x : Euc d) :
    HRS.Whole.firstMarginal (HRS.Whole.poleLaw d s (m + 2) β μ x t) =
      μ.withDensity fun y => ENNReal.ofReal
        (Real.exp (-(t * (β / ((m + 2 : ℕ) : ℝ))) * rieszKernel d s (x - y)) *
          s74_A d s μ (β / ((m + 2 : ℕ) : ℝ)) β t x m y) := by
  rw [s74_firstMarginal_eq hs0 hconv hβ ht m x]
  congr 1
  funext y
  rw [ENNReal.ofReal_mul (Real.exp_pos _).le, s74_ofReal_A hs0 hint hconv hMg hβ ht ht1 m x y]

/-- The prefactor as an average of the conditional ratio over the pole law. -/
theorem s74_a_eq (hs0 : 0 < s) (hint : ∀ z, Integrable (fun y => rieszKernel d s (z - y)) μ)
    (hconv : ∀ z, HRS.Whole.convMeasure (rieszKernel d s) μ z ≤ Mg) (hMg : 0 ≤ Mg) (hβ : 0 ≤ β)
    (ht : 0 ≤ t) (ht1 : t ≤ 1) (m : ℕ) (x y : Euc d) :
    s74_a d s μ (β / ((m + 2 : ℕ) : ℝ)) β t x m y =
      ∫⁻ X : EucConfig d (m + 1), ENNReal.ofReal (Real.exp (-(s74_u d s μ (β / ((m + 2 : ℕ) : ℝ)) β
          (Fin.tail X) y))) *
        (s74_Zc d s μ (β / ((m + 2 : ℕ) : ℝ)) β t x (Fin.tail X))⁻¹
        ∂(HRS.Whole.poleLaw d s (m + 2) β μ x t) := by
  set lam : ℝ := β / ((m + 2 : ℕ) : ℝ) with hlamdef
  have hlam : 0 ≤ lam := div_nonneg hβ (Nat.cast_nonneg _)
  have hK : lam * (t + m) ≤ β := by
    have h := wr13a_lam_mul_le' (r := t + m) (c := 1) hβ (N := ((m + 2 : ℕ) : ℝ)) (by positivity)
      (by push_cast; linarith)
    linarith
  have hZ0 : ∀ Y : EucConfig d m, s74_Zc d s μ lam β t x Y ≠ 0 := fun Y => by
    have := s74_Zc_ge hs0 hint hconv hMg hlam hβ ht x Y hK
    exact (lt_of_lt_of_le (ENNReal.ofReal_pos.2 (Real.exp_pos _)) this).ne'
  have hZt : ∀ Y : EucConfig d m, s74_Zc d s μ lam β t x Y ≠ ∞ := fun Y =>
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (s74_Zc_le hs0 hconv hlam hβ ht x Y)
  set F : Euc d × EucConfig d m → ℝ≥0∞ := fun p =>
    ENNReal.ofReal (Real.exp (-(s74_u d s μ lam β p.2 y))) * (s74_Zc d s μ lam β t x p.2)⁻¹ with hF
  have hFm : Measurable F :=
    ((ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
      ((s74_u_meas_Y hs0 μ lam β y).neg))).mul (s74_Zc_meas hs0 μ lam β t x m).inv).comp measurable_snd
  rw [s74_lintegral_pole hs0 hconv hβ ht m x F hFm]
  unfold s74_a s74_aNum
  congr 1
  have hmeas : Measurable (fun p : Euc d × EucConfig d m => F p * ENNReal.ofReal (Real.exp
      (-(s74_u d s μ lam β p.2 p.1) - t * lam * rieszKernel d s (x - p.1))) *
      ENNReal.ofReal (Real.exp (wr13a_Ep d s μ lam β x t p.2))) :=
    (hFm.mul (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (((s74_u_meas2' hs0 μ lam β).neg).sub
      (((wr13a_g_meas hs0).comp (measurable_const.sub measurable_fst)).const_mul _))))).mul
      ((s74_W_meas hs0 μ lam β x t m).comp measurable_snd)
  rw [lintegral_lintegral_swap hmeas.aemeasurable]
  refine lintegral_congr fun Y => ?_
  have hzm : Measurable fun z : Euc d => ENNReal.ofReal (Real.exp
      (-(s74_u d s μ lam β Y z) - t * lam * rieszKernel d s (x - z))) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (((s74_u_meas_y hs0 μ lam β Y).neg).sub
      (((wr13a_g_meas hs0).comp (measurable_const.sub measurable_id)).const_mul _)))
  have hcalc : ∀ z : Euc d, F (z, Y) * ENNReal.ofReal (Real.exp
      (-(s74_u d s μ lam β Y z) - t * lam * rieszKernel d s (x - z))) *
      ENNReal.ofReal (Real.exp (wr13a_Ep d s μ lam β x t Y)) =
      (F (y, Y) * ENNReal.ofReal (Real.exp (wr13a_Ep d s μ lam β x t Y))) *
        ENNReal.ofReal (Real.exp (-(s74_u d s μ lam β Y z) - t * lam * rieszKernel d s (x - z))) := by
    intro z
    have hz : F (z, Y) = F (y, Y) := rfl
    rw [hz]; ring
  try simp only [← hlamdef]
  symm
  simp_rw [hcalc]
  rw [lintegral_const_mul _ hzm]
  have hZdef : ∫⁻ z, ENNReal.ofReal (Real.exp
      (-(s74_u d s μ lam β Y z) - t * lam * rieszKernel d s (x - z))) ∂μ = s74_Zc d s μ lam β t x Y := rfl
  rw [hZdef]
  have hcancel : (s74_Zc d s μ lam β t x Y)⁻¹ * s74_Zc d s μ lam β t x Y = 1 :=
    ENNReal.inv_mul_cancel (hZ0 Y) (hZt Y)
  simp only [hF]
  calc (ENNReal.ofReal (Real.exp (-(s74_u d s μ lam β Y y))) * (s74_Zc d s μ lam β t x Y)⁻¹ *
        ENNReal.ofReal (Real.exp (wr13a_Ep d s μ lam β x t Y))) * s74_Zc d s μ lam β t x Y
      = ENNReal.ofReal (Real.exp (-(s74_u d s μ lam β Y y))) *
        ENNReal.ofReal (Real.exp (wr13a_Ep d s μ lam β x t Y)) *
        ((s74_Zc d s μ lam β t x Y)⁻¹ * s74_Zc d s μ lam β t x Y) := by ring
    _ = _ := by rw [hcancel, mul_one]

end Pole2

end HRS.MS.Wr
