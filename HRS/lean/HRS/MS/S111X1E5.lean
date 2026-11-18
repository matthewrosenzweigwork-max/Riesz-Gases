import HRS.MS.S111X1E4

/-!
# S11.1 X1 (energy), part 5: the generator of the stationary model and the energy identity
-/

set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S111X1

open HRS HRS.Whole

variable {d : ℕ}

/-- The structure of the stationary model needed for the energy estimate. -/
structure EnData (d : ℕ) (s β : ℝ) (ρ : Euc d → ℝ) (M : ℝ) (C : WholeCoeff d) : Prop where
  K : KData d s ρ M
  hβ : 0 < β
  hν : C.ν = β⁻¹
  hs : C.s = s
  hρC : ∀ r, C.ρ r = ρ
  hMT : ∀ v : Euc d, Torus.matVec C.M.transpose v = -v
  smooth : ContDiff ℝ 2 ρ
  grad : ∀ r x, gradient ρ x = (β * ρ x) • C.drift r x
  mom : Integrable (fun x => ‖x‖ * ρ x)
  dgrow : ∃ c0 : ℝ, ∀ r x, ‖C.drift r x‖ ≤ c0 * (1 + ‖x‖)

/-- the generator on a `C²` function with bounded gradient -/
theorem gen_formula {s β : ℝ} {ρ : Euc d → ℝ} {M : ℝ} {C : WholeCoeff d} (E : EnData d s β ρ M C)
    {f : Euc d → ℝ} (hf : ContDiff ℝ 2 f) {B1 : ℝ} (hB1 : ∀ x, ‖gradient f x‖ ≤ B1) (r : ℝ) (x : Euc d) :
    generatorW C r f x = β⁻¹ * Laplacian.laplacian f x + inner ℝ (C.drift r x) (gradient f x) +
      ∫ y, ρ y * inner ℝ (gradient f y) (rieszKernelGrad d s (x - y)) := by
  have hgc : Continuous (gradient f) := by
    have : Continuous fun x => (InnerProductSpace.toDual ℝ (Euc d)).symm (fderiv ℝ f x) :=
      (InnerProductSpace.toDual ℝ (Euc d)).symm.continuous.comp (hf.continuous_fderiv (by norm_num))
    exact this
  have hnl := nl_plain E.K (a := fun y => -gradient f y) hgc.neg.measurable
    (Ba := B1) (fun y => by rw [norm_neg]; exact hB1 y) x
  unfold generatorW
  rw [E.hν, E.hs]
  simp_rw [E.hρC r, E.hMT]
  simp only [inner_neg_left, integral_neg, mul_neg] at hnl
  rw [hnl]
  ring

/-- bounds of a classical solution at fixed time -/
theorem classical_bounds {C : WholeCoeff d} {t : ℝ} {φ : Euc d → ℝ} {f : ℝ → Euc d → ℝ}
    (hf : IsClassicalAdjointW C t φ f) :
    ∃ B0 B1 B2 : ℝ, 0 ≤ B0 ∧ 0 ≤ B1 ∧ 0 ≤ B2 ∧ ∀ r ∈ Set.Icc (0 : ℝ) t, ∀ x,
      ‖f r x‖ ≤ B0 ∧ ‖fderiv ℝ (f r) x‖ ≤ B1 ∧ ‖fderiv ℝ (fderiv ℝ (f r)) x‖ ≤ B2 := by
  obtain ⟨B0, h0⟩ := hf.bdd 0 (by norm_num)
  obtain ⟨B1, h1⟩ := hf.bdd 1 (by norm_num)
  obtain ⟨B2, h2⟩ := hf.bdd 2 (by norm_num)
  refine ⟨max B0 0, max B1 0, max B2 0, le_max_right _ _, le_max_right _ _, le_max_right _ _,
    fun r hr x => ⟨?_, ?_, ?_⟩⟩
  · have := h0 r hr x
    rw [norm_iteratedFDeriv_zero] at this
    exact this.trans (le_max_left _ _)
  · have := h1 r hr x
    rw [norm_iteratedFDeriv_one] at this
    exact this.trans (le_max_left _ _)
  · have := h2 r hr x
    have e1 := norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (f := f r) (x := x) (n := 1)
    rw [norm_iteratedFDeriv_one] at e1
    rw [e1]
    exact this.trans (le_max_left _ _)

theorem local_identity {s β : ℝ} {ρ : Euc d → ℝ} {M : ℝ} {C : WholeCoeff d} (E : EnData d s β ρ M C)
    {t : ℝ} {φ : Euc d → ℝ} {f : ℝ → Euc d → ℝ} (hf : IsClassicalAdjointW C t φ f)
    {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) t) :
    ∫ x, f r x * ρ x * (β⁻¹ * Laplacian.laplacian (f r) x + inner ℝ (C.drift r x) (gradient (f r) x)) =
      -(β⁻¹ * ∫ x, inner ℝ (gradient (f r) x) (gradient (f r) x) * ρ x) := by
  obtain ⟨B0, B1, B2, hB0, hB1, hB2, hB⟩ := classical_bounds hf
  obtain ⟨c0, hc0⟩ := E.dgrow
  have hβ := E.hβ
  have hgn : Integrable (fun x => ‖gradient ρ x‖) := by
    have : Integrable (fun x => β * (c0 * ((1 + ‖x‖) * ρ x))) := by
      have h1 : Integrable (fun x => (1 + ‖x‖) * ρ x) := by
        have := E.K.int.add E.mom
        refine this.congr (Filter.Eventually.of_forall fun x => ?_)
        simp only [Pi.add_apply]; ring
      exact (h1.const_mul c0).const_mul β
    refine this.mono' ?_ (Filter.Eventually.of_forall fun x => ?_)
    · have hc : Continuous (gradient ρ) := by
        have : Continuous fun x => (InnerProductSpace.toDual ℝ (Euc d)).symm (fderiv ℝ ρ x) :=
          (InnerProductSpace.toDual ℝ (Euc d)).symm.continuous.comp
            (E.smooth.continuous_fderiv (by norm_num))
        exact this
      exact hc.norm.aestronglyMeasurable
    · rw [E.grad r x, norm_smul, Real.norm_of_nonneg (mul_nonneg hβ.le (E.K.nonneg x))]
      have := hc0 r x
      have h3 := E.K.nonneg x
      rw [Real.norm_of_nonneg (mul_nonneg (mul_nonneg hβ.le h3) (norm_nonneg _))]
      calc β * ρ x * ‖C.drift r x‖ ≤ β * ρ x * (c0 * (1 + ‖x‖)) := by gcongr
        _ = β * (c0 * ((1 + ‖x‖) * ρ x)) := by ring
  have key := ibp_weighted E.smooth E.K.int hgn (hf.c2 r hr) (fun x => (hB r hr x).1)
    (fun x => (hB r hr x).2.1) (fun x => (hB r hr x).2.2)
  have e : ∀ x, f r x * ρ x * (β⁻¹ * Laplacian.laplacian (f r) x + inner ℝ (C.drift r x) (gradient (f r) x)) =
      β⁻¹ * (f r x * (ρ x * Laplacian.laplacian (f r) x + inner ℝ (gradient ρ x) (gradient (f r) x))) := by
    intro x
    rw [E.grad r x, inner_smul_left]
    simp only [conj_trivial]
    field_simp
  simp_rw [e]
  rw [integral_const_mul, key]
  simp_rw [real_inner_self_eq_norm_sq, mul_comm (ρ _)]
  ring

/-- the nonlocal term of the generator -/
def Nnl (d : ℕ) (s : ℝ) (ρ : Euc d → ℝ) (a : Euc d → Euc d) (x : Euc d) : ℝ :=
  ∫ y, ρ y * inner ℝ (a y) (rieszKernelGrad d s (x - y))

theorem Nnl_bdd {s : ℝ} {ρ : Euc d → ℝ} {M : ℝ} (K : KData d s ρ M) {a : Euc d → Euc d} {Ba : ℝ}
    (hBa : ∀ y, ‖a y‖ ≤ Ba) (x : Euc d) : |Nnl d s ρ a x| ≤ Ba * kA d s M ρ := by
  have hw := kG_weighted K.hd K.hs0 K.hs1 K.meas K.nonneg K.int K.bdd x
  have hBa0 : 0 ≤ Ba := (norm_nonneg _).trans (hBa 0)
  unfold Nnl
  rw [← Real.norm_eq_abs]
  refine (norm_integral_le_of_norm_le (hw.1.const_mul Ba) (Filter.Eventually.of_forall fun y => ?_)).trans ?_
  · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (K.nonneg y)]
    have := abs_real_inner_le_norm (a y) (rieszKernelGrad d s (x - y))
    have h3 := K.nonneg y
    calc ρ y * |inner ℝ (a y) (rieszKernelGrad d s (x - y))| ≤ ρ y * (‖a y‖ * ‖rieszKernelGrad d s (x - y)‖) := by gcongr
      _ ≤ ρ y * (Ba * ‖rieszKernelGrad d s (x - y)‖) := by gcongr; exact hBa y
      _ = Ba * (ρ y * ‖rieszKernelGrad d s (x - y)‖) := by ring
  · rw [integral_const_mul]
    nlinarith [hw.2, hBa0]

theorem Nnl_meas {s : ℝ} {ρ : Euc d → ℝ} {M : ℝ} (K : KData d s ρ M) {a : Euc d → Euc d}
    (ham : Measurable a) : Measurable (Nnl d s ρ a) := by
  unfold Nnl
  have : Measurable fun p : Euc d × Euc d => ρ p.2 * inner ℝ (a p.2) (rieszKernelGrad d s (p.1 - p.2)) :=
    (K.meas.comp measurable_snd).mul (Measurable.inner (ham.comp measurable_snd)
      ((kG_measurable s).comp (measurable_fst.sub measurable_snd)))
  exact (this.stronglyMeasurable.integral_prod_right').measurable

end HRS.MS.S111X1
