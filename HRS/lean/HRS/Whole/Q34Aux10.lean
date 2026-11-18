import HRS.Whole.Q34Aux9

/-!
# Packet Q34, helper file 10: the integral operator `u ↦ ∫ ‖x - y‖^{-s} u(y) dν(y)` on `L²(ν)`
-/

noncomputable section

open MeasureTheory Filter Topology Set Metric InnerProductSpace
open scoped ENNReal NNReal

namespace HRS.Whole.Q34

variable {d : ℕ}

/-- The potential `Tk ν u (x) = ∫ ‖x - y‖^{-s} u(y) dν(y)`. -/
def Tk (s : ℝ) (ν : Measure (Euc d)) (u : Euc d → ℝ) (x : Euc d) : ℝ :=
  ∫ y, ‖x - y‖ ^ (-s) * u y ∂ν

section Schur

variable {s : ℝ} {ρ : Euc d → ℝ} {M : ℝ}

/-- The constant `M_g` of the bounded-potential estimate. -/
def Mg (d : ℕ) (s M : ℝ) : ℝ := M * sphereArea d / ((d : ℝ) - s) + 1

theorem Mg_nonneg (hd : 1 ≤ d) (hsd : s < d) (hM0 : 0 ≤ M) : 0 ≤ Mg d s M := by
  unfold Mg
  have := sphereArea_nonneg hd
  have : 0 < (d : ℝ) - s := by linarith
  positivity

theorem kernel_sym_bound (hd : 1 ≤ d) (hs0 : 0 < s) (hsd : s < d) (hρ : IsProbDensity ρ)
    (hM : ∀ x, ρ x ≤ M) (y : Euc d) :
    ∫⁻ x, ENNReal.ofReal (‖x - y‖ ^ (-s)) ∂(withDensityReal ρ) ≤ ENNReal.ofReal (Mg d s M) := by
  have := lintegral_kernel_le hd hs0 hsd hρ hM y
  simpa only [norm_sub_rev (y) _, Mg] using this

/-- Schur's test in `lintegral` form. -/
theorem schur_lintegral (hd : 1 ≤ d) (hs0 : 0 < s) (hsd : s < d) (hρ : IsProbDensity ρ)
    (hM : ∀ x, ρ x ≤ M) (U : Euc d → ℝ≥0∞) (hU : Measurable U) :
    ∫⁻ x, (∫⁻ y, ENNReal.ofReal (‖x - y‖ ^ (-s)) * U y ∂(withDensityReal ρ)) ^ 2
        ∂(withDensityReal ρ) ≤
      ENNReal.ofReal (Mg d s M) ^ 2 * ∫⁻ y, U y ^ 2 ∂(withDensityReal ρ) := by
  have := isProbabilityMeasure_nu hρ
  set ν := withDensityReal ρ with hν
  have hG : ∀ x : Euc d, Measurable (fun y : Euc d => ENNReal.ofReal (‖x - y‖ ^ (-s))) := fun x =>
    ((measurable_norm.comp (measurable_const.sub measurable_id)).pow_const _).ennreal_ofReal
  have h1 : ∀ x : Euc d, (∫⁻ y, ENNReal.ofReal (‖x - y‖ ^ (-s)) * U y ∂ν) ^ 2 ≤
      ENNReal.ofReal (Mg d s M) * ∫⁻ y, ENNReal.ofReal (‖x - y‖ ^ (-s)) * U y ^ 2 ∂ν := by
    intro x
    refine (weighted_cs ν _ U (hG x) hU).trans ?_
    refine mul_le_mul' ?_ le_rfl
    exact lintegral_kernel_le hd hs0 hsd hρ hM x |>.trans (by simp [Mg])
  have hjoint : Measurable (fun p : Euc d × Euc d =>
      ENNReal.ofReal (‖p.1 - p.2‖ ^ (-s)) * U p.2 ^ 2) :=
    (((measurable_norm.comp (measurable_fst.sub measurable_snd)).pow_const _).ennreal_ofReal).mul
      ((hU.comp measurable_snd).pow_const 2)
  calc ∫⁻ x, (∫⁻ y, ENNReal.ofReal (‖x - y‖ ^ (-s)) * U y ∂ν) ^ 2 ∂ν
      ≤ ∫⁻ x, ENNReal.ofReal (Mg d s M) *
          ∫⁻ y, ENNReal.ofReal (‖x - y‖ ^ (-s)) * U y ^ 2 ∂ν ∂ν := lintegral_mono h1
    _ = ENNReal.ofReal (Mg d s M) *
          ∫⁻ x, ∫⁻ y, ENNReal.ofReal (‖x - y‖ ^ (-s)) * U y ^ 2 ∂ν ∂ν := by
        rw [lintegral_const_mul]
        exact Measurable.lintegral_prod_right' (f := fun p : Euc d × Euc d =>
          ENNReal.ofReal (‖p.1 - p.2‖ ^ (-s)) * U p.2 ^ 2) hjoint
    _ = ENNReal.ofReal (Mg d s M) *
          ∫⁻ y, ∫⁻ x, ENNReal.ofReal (‖x - y‖ ^ (-s)) * U y ^ 2 ∂ν ∂ν := by
        congr 1
        exact lintegral_lintegral_swap hjoint.aemeasurable
    _ ≤ ENNReal.ofReal (Mg d s M) *
          ∫⁻ y, ENNReal.ofReal (Mg d s M) * U y ^ 2 ∂ν := by
        refine mul_le_mul' le_rfl (lintegral_mono fun y => ?_)
        have hm : Measurable (fun x : Euc d => ENNReal.ofReal (‖x - y‖ ^ (-s))) := by fun_prop
        rw [lintegral_mul_const _ hm]
        exact mul_le_mul' (kernel_sym_bound hd hs0 hsd hρ hM y) le_rfl
    _ = ENNReal.ofReal (Mg d s M) ^ 2 * ∫⁻ y, U y ^ 2 ∂ν := by
        rw [lintegral_const_mul _ (hU.pow_const 2)]
        ring



/-- The `lintegral` majorant `N_u(x) = ∫ ‖x - y‖^{-s} |u(y)| dν(y)`. -/
def Nu (s : ℝ) (ν : Measure (Euc d)) (u : Euc d → ℝ) (x : Euc d) : ℝ≥0∞ :=
  ∫⁻ y, ENNReal.ofReal (‖x - y‖ ^ (-s)) * ENNReal.ofReal |u y| ∂ν

theorem tk_measurable {ν : Measure (Euc d)} [SFinite ν] {u : Euc d → ℝ} (hu : Measurable u) :
    Measurable (Tk s ν u) := by
  have hsm : StronglyMeasurable (fun p : Euc d × Euc d => ‖p.1 - p.2‖ ^ (-s) * u p.2) :=
    (((measurable_norm.comp (measurable_fst.sub measurable_snd)).pow_const _).mul
      (hu.comp measurable_snd)).stronglyMeasurable
  exact (hsm.integral_prod_right' (ν := ν)).measurable

theorem measurable_Nu {ν : Measure (Euc d)} [SFinite ν] {u : Euc d → ℝ} (hu : Measurable u) :
    Measurable (Nu s ν u) := by
  unfold Nu
  exact Measurable.lintegral_prod_right' (f := fun p : Euc d × Euc d =>
    ENNReal.ofReal (‖p.1 - p.2‖ ^ (-s)) * ENNReal.ofReal |u p.2|)
    (((measurable_norm.comp (measurable_fst.sub measurable_snd)).pow_const _).ennreal_ofReal.mul
      (hu.comp measurable_snd).abs.ennreal_ofReal)

theorem ofReal_abs_tk_le (ν : Measure (Euc d)) (u : Euc d → ℝ) (x : Euc d) :
    ENNReal.ofReal |Tk s ν u x| ≤ Nu s ν u x := by
  have := enorm_integral_le_lintegral_enorm (μ := ν) (fun y => ‖x - y‖ ^ (-s) * u y)
  rw [Real.enorm_eq_ofReal_abs] at this
  refine this.trans (le_of_eq ?_)
  refine lintegral_congr fun y => ?_
  rw [Real.enorm_eq_ofReal_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _),
    ENNReal.ofReal_mul (Real.rpow_nonneg (norm_nonneg _) _)]

variable {ρ : Euc d → ℝ} {M : ℝ}

theorem lintegral_Nu_sq_le (hd : 1 ≤ d) (hs0 : 0 < s) (hsd : s < d) (hρ : IsProbDensity ρ)
    (hM : ∀ x, ρ x ≤ M) {u : Euc d → ℝ} (hu : Measurable u) (hu2 : MemLp u 2 (withDensityReal ρ)) :
    ∫⁻ x, Nu s (withDensityReal ρ) u x ^ 2 ∂(withDensityReal ρ) ≤
      ENNReal.ofReal (Mg d s M ^ 2 * ∫ x, u x ^ 2 ∂(withDensityReal ρ)) := by
  have hM0 : 0 ≤ M := (hρ.nonneg 0).trans (hM 0)
  have hMg0 := Mg_nonneg hd hsd hM0
  have h := schur_lintegral hd hs0 hsd hρ hM (fun y => ENNReal.ofReal |u y|)
    hu.abs.ennreal_ofReal
  have hint : ∫⁻ y, ENNReal.ofReal |u y| ^ 2 ∂(withDensityReal ρ) =
      ENNReal.ofReal (∫ x, u x ^ 2 ∂(withDensityReal ρ)) := by
    rw [ofReal_integral_eq_lintegral_ofReal (hu2.integrable_sq)
      (Filter.Eventually.of_forall fun x => sq_nonneg _)]
    refine lintegral_congr fun y => ?_
    rw [← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
  rw [hint] at h
  refine h.trans (le_of_eq ?_)
  rw [← ENNReal.ofReal_pow hMg0, ← ENNReal.ofReal_mul (by positivity)]

theorem tk_memLp (hd : 1 ≤ d) (hs0 : 0 < s) (hsd : s < d) (hρ : IsProbDensity ρ)
    (hM : ∀ x, ρ x ≤ M) {u : Euc d → ℝ} (hu : Measurable u) (hu2 : MemLp u 2 (withDensityReal ρ)) :
    MemLp (Tk s (withDensityReal ρ) u) 2 (withDensityReal ρ) ∧
      ∫ x, Tk s (withDensityReal ρ) u x ^ 2 ∂(withDensityReal ρ) ≤
        Mg d s M ^ 2 * ∫ x, u x ^ 2 ∂(withDensityReal ρ) := by
  have := isProbabilityMeasure_nu hρ
  have hM0 : 0 ≤ M := (hρ.nonneg 0).trans (hM 0)
  have hMg0 := Mg_nonneg hd hsd hM0
  have hTm := tk_measurable (s := s) (ν := withDensityReal ρ) hu
  have hc : 0 ≤ Mg d s M ^ 2 * ∫ x, u x ^ 2 ∂(withDensityReal ρ) :=
    mul_nonneg (sq_nonneg _) (integral_nonneg fun x => sq_nonneg _)
  have hN := lintegral_Nu_sq_le hd hs0 hsd hρ hM hu hu2
  obtain ⟨hI, hV⟩ := integrable_of_lintegral_le (μ := withDensityReal ρ)
    (f := fun x => Tk s (withDensityReal ρ) u x ^ 2) (hTm.pow_const 2) (fun x => sq_nonneg _) hc
    ((lintegral_mono fun x => by
      calc ENNReal.ofReal (Tk s (withDensityReal ρ) u x ^ 2)
          = ENNReal.ofReal |Tk s (withDensityReal ρ) u x| ^ 2 := by
            rw [← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
        _ ≤ Nu s (withDensityReal ρ) u x ^ 2 := pow_le_pow_left' (ofReal_abs_tk_le _ _ _) 2).trans hN)
  exact ⟨(memLp_two_iff_integrable_sq hTm.aestronglyMeasurable).2 hI, hV⟩

theorem tk_ae_integrable (hd : 1 ≤ d) (hs0 : 0 < s) (hsd : s < d) (hρ : IsProbDensity ρ)
    (hM : ∀ x, ρ x ≤ M) {u : Euc d → ℝ} (hu : Measurable u) (hu2 : MemLp u 2 (withDensityReal ρ)) :
    ∀ᵐ x ∂(withDensityReal ρ), Integrable (fun y => ‖x - y‖ ^ (-s) * u y) (withDensityReal ρ) := by
  have := isProbabilityMeasure_nu hρ
  have hN := lintegral_Nu_sq_le hd hs0 hsd hρ hM hu hu2
  have hfin : ∀ᵐ x ∂(withDensityReal ρ), Nu s (withDensityReal ρ) u x ^ 2 < ∞ := by
    refine ae_lt_top ((measurable_Nu hu).pow_const 2) (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hN)
  filter_upwards [hfin] with x hx
  have hx' : Nu s (withDensityReal ρ) u x < ∞ := by
    by_contra h
    rw [not_lt, top_le_iff] at h
    rw [h] at hx
    simp at hx
  refine ⟨?_, ?_⟩
  · exact (((measurable_norm.comp (measurable_const.sub measurable_id)).pow_const _).mul
      hu).aestronglyMeasurable
  · have : ∫⁻ y, ‖‖x - y‖ ^ (-s) * u y‖ₑ ∂(withDensityReal ρ) = Nu s (withDensityReal ρ) u x := by
      refine lintegral_congr fun y => ?_
      rw [Real.enorm_eq_ofReal_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _),
        ENNReal.ofReal_mul (Real.rpow_nonneg (norm_nonneg _) _)]
    simp only [HasFiniteIntegral, this]
    exact hx'

end Schur

end HRS.Whole.Q34
