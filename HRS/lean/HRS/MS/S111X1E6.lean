import HRS.MS.S111X1E5

/-!
# S11.1 X1 (energy), part 6: the derivative of the weighted `L²` norm along a classical solution
-/

set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S111X1

open HRS HRS.Whole

variable {d : ℕ}

theorem phi_deriv {s β : ℝ} {ρ : Euc d → ℝ} {M : ℝ} {C : WholeCoeff d} (E : EnData d s β ρ M C)
    {t : ℝ} {φ : Euc d → ℝ} {f : ℝ → Euc d → ℝ} (hf : IsClassicalAdjointW C t φ f)
    {r : ℝ} (hr : r ∈ Set.Ioo 0 t) :
    HasDerivAt (fun r' => ∫ x, f r' x ^ 2 * ρ x)
      (2 * β⁻¹ * (∫ x, inner ℝ (gradient (f r) x) (gradient (f r) x) * ρ x) -
        2 * ∫ x, f r x * ρ x * Nnl d s ρ (fun y => gradient (f r) y) x) r := by
  obtain ⟨B0, B1, B2, hB0, hB1, hB2, hB⟩ := classical_bounds hf
  obtain ⟨Bg, hBg⟩ := hf.bdd_time_deriv
  have hr' : r ∈ Set.Icc (0 : ℝ) t := ⟨hr.1.le, hr.2.le⟩
  have hmem : Set.Ioo (0 : ℝ) t ∈ 𝓝 r := Ioo_mem_nhds hr.1 hr.2
  have hIcc : ∀ r' ∈ Set.Ioo (0 : ℝ) t, r' ∈ Set.Icc (0 : ℝ) t := fun r' h => ⟨h.1.le, h.2.le⟩
  have hmom : Integrable (fun x => (1 + ‖x‖) * ρ x) := by
    have := E.K.int.add E.mom
    refine this.congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [Pi.add_apply]; ring
  have hfc : ∀ r' ∈ Set.Icc (0 : ℝ) t, Continuous (f r') := fun r' h => (hf.c2 r' h).continuous
  have hGc : ∀ r' ∈ Set.Icc (0 : ℝ) t, Continuous fun x => generatorW C r' (f r') x := by
    intro r' h
    have h1 : Continuous fun x : Euc d => ((⟨r', h⟩ : Set.Icc (0 : ℝ) t), x) :=
      continuous_const.prodMk continuous_id
    have h2 := hf.cont_time_deriv.comp h1
    exact h2
  have hρc : Continuous ρ := E.smooth.continuous
  have hρ0 := E.K.nonneg
  have hB0' : ∀ r' ∈ Set.Icc (0 : ℝ) t, ∀ x, |f r' x| ≤ B0 := fun r' h x => by
    rw [← Real.norm_eq_abs]; exact (hB r' h x).1
  have hFint : Integrable (fun x => f r x ^ 2 * ρ x) := by
    refine (E.K.int.mul_const (B0 ^ 2)).mono' (((hfc r hr').pow 2).mul hρc).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hρ0 x), abs_pow]
    have := hB0' r hr' x
    have hρx := hρ0 x
    calc |f r x| ^ 2 * ρ x ≤ B0 ^ 2 * ρ x := by gcongr
      _ = ρ x * B0 ^ 2 := by ring
  have hbint : Integrable (fun x => 2 * B0 * (Bg * ((1 + ‖x‖) * ρ x))) :=
    ((hmom.const_mul Bg).const_mul (2 * B0))
  have hF'meas : AEStronglyMeasurable (fun x => 2 * f r x * (-(generatorW C r (f r) x)) * ρ x) := by
    exact ((((continuous_const.mul (hfc r hr')).mul (hGc r hr').neg)).mul hρc).aestronglyMeasurable
  have hbound : ∀ᵐ x ∂(volume : Measure (Euc d)), ∀ r' ∈ Set.Ioo (0 : ℝ) t,
      ‖2 * f r' x * (-(generatorW C r' (f r') x)) * ρ x‖ ≤ 2 * B0 * (Bg * ((1 + ‖x‖) * ρ x)) := by
    refine Filter.Eventually.of_forall fun x r' h => ?_
    have hr2 := hIcc r' h
    have h1 := hB0' r' hr2 x
    have h2 := hBg r' hr2 x
    have h3 := hρ0 x
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_neg, abs_of_nonneg h3, abs_mul, abs_two]
    have hBg0 : 0 ≤ Bg * (1 + ‖x‖) := (abs_nonneg _).trans h2
    calc 2 * |f r' x| * |generatorW C r' (f r') x| * ρ x ≤ 2 * B0 * (Bg * (1 + ‖x‖)) * ρ x := by gcongr
      _ = 2 * B0 * (Bg * ((1 + ‖x‖) * ρ x)) := by ring
  have hdiff : ∀ᵐ x ∂(volume : Measure (Euc d)), ∀ r' ∈ Set.Ioo (0 : ℝ) t,
      HasDerivAt (fun r'' => f r'' x ^ 2 * ρ x) (2 * f r' x * (-(generatorW C r' (f r') x)) * ρ x) r' := by
    refine Filter.Eventually.of_forall fun x r' h => ?_
    have := ((hf.time_deriv x r' h).pow 2).mul_const (ρ x)
    convert this using 1
    simp
  have hD := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := (volume : Measure (Euc d)))
    (F := fun r' x => f r' x ^ 2 * ρ x) (F' := fun r' x => 2 * f r' x * (-(generatorW C r' (f r') x)) * ρ x)
    (x₀ := r) (bound := fun x => 2 * B0 * (Bg * ((1 + ‖x‖) * ρ x))) hmem
    (Filter.eventually_of_mem hmem fun r' h => (((hfc r' (hIcc r' h)).pow 2).mul hρc).aestronglyMeasurable)
    hFint hF'meas hbound hbint hdiff
  have hgb : ∀ x, ‖gradient (f r) x‖ ≤ B1 := fun x => by simpa [gradient] using (hB r hr' x).2.1
  have hform : ∀ x, generatorW C r (f r) x = β⁻¹ * Laplacian.laplacian (f r) x +
      inner ℝ (C.drift r x) (gradient (f r) x) + Nnl d s ρ (fun y => gradient (f r) y) x :=
    fun x => gen_formula E (hf.c2 r hr') hgb r x
  have hgc : Continuous (gradient (f r)) := by
    have : Continuous fun x => (InnerProductSpace.toDual ℝ (Euc d)).symm (fderiv ℝ (f r) x) :=
      (InnerProductSpace.toDual ℝ (Euc d)).symm.continuous.comp
        ((hf.c2 r hr').continuous_fderiv (by norm_num))
    exact this
  have hNb : ∀ x, |Nnl d s ρ (fun y => gradient (f r) y) x| ≤ B1 * kA d s M ρ :=
    fun x => Nnl_bdd E.K hgb x
  have I1 : Integrable (fun x => f r x * ρ x * generatorW C r (f r) x) := by
    refine (hmom.const_mul (B0 * Bg)).mono' (((hfc r hr').mul hρc).mul (hGc r hr')).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    have h1 := hB0' r hr' x
    have h2 := hBg r hr' x
    have h3 := hρ0 x
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg h3]
    have hBg0 : 0 ≤ Bg * (1 + ‖x‖) := (abs_nonneg _).trans h2
    calc |f r x| * ρ x * |generatorW C r (f r) x| ≤ B0 * ρ x * (Bg * (1 + ‖x‖)) := by gcongr
      _ = B0 * Bg * ((1 + ‖x‖) * ρ x) := by ring
  have I2 : Integrable (fun x => f r x * ρ x * Nnl d s ρ (fun y => gradient (f r) y) x) := by
    refine (E.K.int.const_mul (B0 * (B1 * kA d s M ρ))).mono'
      ((((hfc r hr').mul hρc).aestronglyMeasurable).mul (Nnl_meas E.K hgc.measurable).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun x => ?_)
    have h1 := hB0' r hr' x
    have h3 := hρ0 x
    have h4 := hNb x
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg h3]
    have hA0 : 0 ≤ B1 * kA d s M ρ := (abs_nonneg _).trans h4
    calc |f r x| * ρ x * |Nnl d s ρ (fun y => gradient (f r) y) x| ≤ B0 * ρ x * (B1 * kA d s M ρ) := by gcongr
      _ = B0 * (B1 * kA d s M ρ) * ρ x := by ring
  have I3 : Integrable (fun x => f r x * ρ x * (β⁻¹ * Laplacian.laplacian (f r) x +
      inner ℝ (C.drift r x) (gradient (f r) x))) := by
    refine (I1.sub I2).congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [Pi.sub_apply]
    rw [hform x]
    ring
  have hval : ∫ x, 2 * f r x * (-(generatorW C r (f r) x)) * ρ x =
      2 * β⁻¹ * (∫ x, inner ℝ (gradient (f r) x) (gradient (f r) x) * ρ x) -
        2 * ∫ x, f r x * ρ x * Nnl d s ρ (fun y => gradient (f r) y) x := by
    have e1 : ∀ x, 2 * f r x * (-(generatorW C r (f r) x)) * ρ x =
        -2 * (f r x * ρ x * (β⁻¹ * Laplacian.laplacian (f r) x +
          inner ℝ (C.drift r x) (gradient (f r) x)) + f r x * ρ x * Nnl d s ρ (fun y => gradient (f r) y) x) := by
      intro x
      rw [hform x]
      ring
    simp_rw [e1]
    rw [integral_const_mul, integral_add I3 I2, local_identity E hf hr']
    ring
  rw [hval] at hD
  exact hD.2

end HRS.MS.S111X1
