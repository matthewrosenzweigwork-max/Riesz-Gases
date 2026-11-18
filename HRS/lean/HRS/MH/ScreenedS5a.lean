import HRS.MH.ScreenedS5aAux1
import HRS.PDE.ToolboxRd.Fourier

/-!
# Packet S5a: `gag_equiv`, the Gagliardo seminorm equivalence for `0 < σ < 1`
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff FourierTransform

namespace HRS.MH.Screened

open HRS HRS.Whole

variable {d : ℕ}

open HRS.PDE.ToolboxRd HRS.PDE.ToolboxRd.FourierAux in
theorem s5a_inner_lintegral {u : Euc d → ℝ} (hu : MemLp u 2 volume) (h : Euc d) :
    ∫⁻ x : Euc d, ‖u (x + h) - u x‖ₑ ^ 2 =
      ∫⁻ ξ : Euc d, s5aG (inner ℝ h ξ) * ENNReal.ofReal (‖fourierL2 u ξ‖ ^ 2) := by
  have hw : MemLp (fun x => u x - u (x - h)) 2 volume := hu.sub (memLp_translate hu h)
  have e1 : ∫⁻ x : Euc d, ‖u (x + h) - u x‖ₑ ^ 2 = ∫⁻ x : Euc d, ‖u x - u (x - h)‖ₑ ^ 2 := by
    have := lintegral_add_right_eq_self (μ := (volume : Measure (Euc d)))
      (fun x : Euc d => ‖u x - u (x - h)‖ₑ ^ 2) h
    simpa using this
  have e2 : ∀ a : ℝ, ‖a‖ₑ ^ 2 = ENNReal.ofReal (a ^ 2) := by
    intro a
    rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_pow (norm_nonneg _), Real.norm_eq_abs, sq_abs]
  simp_rw [e1, e2]
  rw [← ofReal_integral_eq_lintegral_ofReal (hw.integrable_sq) (Filter.Eventually.of_forall fun x => sq_nonneg _),
    integral_diff_sq_eq hu h,
    ofReal_integral_eq_lintegral_ofReal (integrable_diff_sq hu h)
      (Filter.Eventually.of_forall fun x => by positivity)]
  refine lintegral_congr fun ξ => ?_
  rw [norm_one_sub_phase_sq, ENNReal.ofReal_mul (by positivity)]
  rfl

open HRS.PDE.ToolboxRd HRS.PDE.ToolboxRd.FourierAux in
theorem s5a_gagSq_eq {σ : ℝ} {u : Euc d → ℝ} (hu : MemLp u 2 volume) :
    gagSq σ u = ∫⁻ ξ : Euc d, s5aK d σ ξ * ENNReal.ofReal (‖fourierL2 u ξ‖ ^ 2) := by
  unfold gagSq
  simp_rw [s5a_inner_lintegral hu]
  have hFe : AEMeasurable (fun ξ : Euc d => ENNReal.ofReal (‖fourierL2 u ξ‖ ^ 2)) volume :=
    (aesm_sq (aestronglyMeasurable_fourierL2 hu)).aemeasurable.ennreal_ofReal
  have hmeas : AEMeasurable (Function.uncurry fun (h ξ : Euc d) =>
      s5aW d σ h * (s5aG (inner ℝ h ξ) * ENNReal.ofReal (‖fourierL2 u ξ‖ ^ 2)))
      ((volume : Measure (Euc d)).prod volume) := by
    refine ((measurable_s5aW d σ).comp measurable_fst).aemeasurable.mul
      ((measurable_s5aG.comp (continuous_fst.inner continuous_snd).measurable).aemeasurable.mul ?_)
    exact hFe.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd
  have step1 : ∀ h : Euc d, s5aW d σ h * ∫⁻ ξ : Euc d, s5aG (inner ℝ h ξ) *
      ENNReal.ofReal (‖fourierL2 u ξ‖ ^ 2) =
      ∫⁻ ξ : Euc d, s5aW d σ h * (s5aG (inner ℝ h ξ) * ENNReal.ofReal (‖fourierL2 u ξ‖ ^ 2)) := by
    intro h
    exact (lintegral_const_mul' (s5aW d σ h) _ (by unfold s5aW; exact ENNReal.ofReal_ne_top)).symm
  have hW : ∀ h : Euc d, ENNReal.ofReal (‖h‖ ^ (-((d : ℝ) + 2 * σ))) = s5aW d σ h := fun h => rfl
  simp_rw [hW, step1]
  rw [lintegral_lintegral_swap hmeas]
  refine lintegral_congr fun ξ => ?_
  unfold s5aK
  rw [← lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
  simp_rw [mul_assoc]


theorem s5aK_zero (σ : ℝ) : s5aK d σ (0 : Euc d) = 0 := by
  unfold s5aK
  simp [s5aG]

/-- the exact homogeneity of the kernel integral, at every `ξ` -/
theorem s5aK_formula (hd : 1 ≤ d) {σ : ℝ} (h0 : 0 < σ) (ξ : Euc d) :
    s5aK d σ ξ = ENNReal.ofReal (‖ξ‖ ^ (2 * σ)) * s5aK d σ (s5aE hd) := by
  by_cases hξ : ξ = 0
  · subst hξ
    rw [s5aK_zero, norm_zero, Real.zero_rpow (by positivity)]
    simp
  · exact s5aK_eq σ h0 (s5aE hd) ξ (s5aE_norm hd) hξ

theorem s5a_enorm_sq (a : ℝ) : ‖a‖ₑ ^ 2 = ENNReal.ofReal (a ^ 2) := by
  rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_pow (norm_nonneg _), Real.norm_eq_abs, sq_abs]

open HRS.PDE.ToolboxRd HRS.PDE.ToolboxRd.FourierAux in
theorem s5a_eLpNorm_sq {u : Euc d → ℝ} (hu : MemLp u 2 volume) :
    (eLpNorm u 2 volume) ^ 2 = ∫⁻ ξ : Euc d, ENNReal.ofReal (‖fourierL2 u ξ‖ ^ 2) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top hu.aestronglyMeasurable]
  simp only [ENNReal.toReal_ofNat, one_div]
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  rw [show (2 : ℝ)⁻¹ * ((2 : ℕ) : ℝ) = 1 by norm_num, ENNReal.rpow_one]
  simp_rw [ENNReal.rpow_two, s5a_enorm_sq]
  rw [← ofReal_integral_eq_lintegral_ofReal hu.integrable_sq
    (Filter.Eventually.of_forall fun x => sq_nonneg _), integral_sq_eq_norm_sq hu,
    ofReal_integral_eq_lintegral_ofReal (integrable_norm_sq_fourierL2 hu)
      (Filter.Eventually.of_forall fun x => by positivity)]

open HRS.PDE.ToolboxRd HRS.PDE.ToolboxRd.FourierAux in
theorem s5a_sobolevNormE_sq {σ : ℝ} {u : Euc d → ℝ} (hM : HRS.PDE.ToolboxRd.MemSobolev σ u) :
    (sobolevNormE σ u) ^ 2 =
      ∫⁻ ξ : Euc d, ENNReal.ofReal (wt ξ ^ σ) * ENNReal.ofReal (‖fourierL2 u ξ‖ ^ 2) := by
  unfold sobolevNormE
  have hS : 0 ≤ sobolevNormSq σ u := by
    unfold sobolevNormSq
    refine integral_nonneg fun ξ => ?_
    have := wt_pos (d := d) ξ
    positivity
  rw [if_pos hM, ← ENNReal.ofReal_pow (Real.sqrt_nonneg _), Real.sq_sqrt hS]
  rw [sobolevNormSq_eq, ofReal_integral_eq_lintegral_ofReal
    (f := fun ξ : Euc d => wt ξ ^ σ * ‖fourierL2 u ξ‖ ^ 2) hM.2
    (Filter.Eventually.of_forall fun ξ => by have := wt_pos (d := d) ξ; positivity)]
  refine lintegral_congr fun ξ => ?_
  rw [ENNReal.ofReal_mul (Real.rpow_nonneg (wt_pos ξ).le σ)]

open HRS.PDE.ToolboxRd HRS.PDE.ToolboxRd.FourierAux in
theorem s5a_memSobolev {σ : ℝ} {u : Euc d → ℝ} (hu : MemLp u 2 volume)
    (h : ∫⁻ ξ : Euc d, ENNReal.ofReal (wt ξ ^ σ) * ENNReal.ofReal (‖fourierL2 u ξ‖ ^ 2) < ⊤) :
    HRS.PDE.ToolboxRd.MemSobolev σ u := by
  refine ⟨hu, ⟨aesm_wt_mul (aestronglyMeasurable_fourierL2 hu) σ, ?_⟩⟩
  unfold HasFiniteIntegral
  refine lt_of_le_of_lt (le_of_eq ?_) h
  refine lintegral_congr fun ξ => ?_
  have h1 : 0 ≤ wt ξ ^ σ * ‖fourierL2 u ξ‖ ^ 2 := by have := wt_pos (d := d) ξ; positivity
  change ‖wt ξ ^ σ * ‖fourierL2 u ξ‖ ^ 2‖ₑ = _
  rw [Real.enorm_eq_ofReal h1, ENNReal.ofReal_mul (Real.rpow_nonneg (wt_pos ξ).le σ)]

theorem s5a_one_add_rpow_le {x σ : ℝ} (hx : 0 ≤ x) (h0 : 0 ≤ σ) (h1 : σ ≤ 1) :
    (1 + x) ^ σ ≤ 1 + x ^ σ := by
  lift x to ℝ≥0 using hx
  have := NNReal.rpow_add_le_add_rpow (1 : ℝ≥0) x h0 h1
  rw [NNReal.one_rpow] at this
  exact_mod_cast this

theorem s5a_norm_rpow (ξ : Euc d) (σ : ℝ) : ‖ξ‖ ^ (2 * σ) = (‖ξ‖ ^ 2) ^ σ := by
  rw [Real.rpow_mul (norm_nonneg _), Real.rpow_two]

theorem s5a_wt_le {σ : ℝ} (h0 : 0 ≤ σ) (h1 : σ ≤ 1) (ξ : Euc d) :
    (1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ σ ≤ 1 + (4 * Real.pi ^ 2) ^ σ * ‖ξ‖ ^ (2 * σ) := by
  refine (s5a_one_add_rpow_le (by positivity) h0 h1).trans ?_
  rw [Real.mul_rpow (by positivity) (by positivity), s5a_norm_rpow]

theorem s5a_norm_rpow_le_wt {σ : ℝ} (h0 : 0 ≤ σ) (ξ : Euc d) :
    ‖ξ‖ ^ (2 * σ) ≤ (1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ σ := by
  rw [s5a_norm_rpow]
  refine Real.rpow_le_rpow (by positivity) ?_ h0
  nlinarith [mul_nonneg (sq_nonneg ‖ξ‖) (by nlinarith [Real.pi_gt_three] : (0:ℝ) ≤ 4 * Real.pi ^ 2 - 1)]


open HRS.PDE.ToolboxRd HRS.PDE.ToolboxRd.FourierAux in
theorem gag_equiv_proof (hd : 1 ≤ d) {σ : ℝ} (h0 : 0 < σ) (h1 : σ < 1) :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ u : Euc d → ℝ, MemLp u 2 volume →
      (sobolevNormE σ u) ^ 2 ≤ ENNReal.ofReal c₁ * ((eLpNorm u 2 volume) ^ 2 + gagSq σ u) ∧
      gagSq σ u ≤ ENNReal.ofReal c₂ * (sobolevNormE σ u) ^ 2 := by
  set C0 : ℝ≥0∞ := s5aK d σ (s5aE hd) with hC0
  have hC0pos : 0 < C0 := s5aK_pos hd σ
  have hC0top : C0 < ⊤ := s5aK_lt_top hd h0 h1
  set c0 : ℝ := C0.toReal with hc0def
  have hc0 : 0 < c0 := ENNReal.toReal_pos hC0pos.ne' hC0top.ne
  have hCeq : C0 = ENNReal.ofReal c0 := (ENNReal.ofReal_toReal hC0top.ne).symm
  set k : ℝ := (4 * Real.pi ^ 2) ^ σ with hk
  have hk0 : 0 ≤ k := by positivity
  refine ⟨max 1 (k / c0), c0, lt_max_of_lt_left one_pos, hc0, fun u hu => ?_⟩
  -- notation
  set Fe : Euc d → ℝ≥0∞ := fun ξ => ENNReal.ofReal (‖fourierL2 u ξ‖ ^ 2) with hFe
  have hFem : AEMeasurable Fe volume :=
    (aesm_sq (aestronglyMeasurable_fourierL2 hu)).aemeasurable.ennreal_ofReal
  set Q : ℝ≥0∞ := ∫⁻ ξ : Euc d, ENNReal.ofReal (‖ξ‖ ^ (2 * σ)) * Fe ξ with hQ
  have hgag : gagSq σ u = C0 * Q := by
    rw [s5a_gagSq_eq hu, hQ, ← lintegral_const_mul' _ _ hC0top.ne]
    refine lintegral_congr fun ξ => ?_
    rw [s5aK_formula hd h0 ξ, mul_comm (ENNReal.ofReal _) C0, mul_assoc]
  have hE : (eLpNorm u 2 volume) ^ 2 = ∫⁻ ξ : Euc d, Fe ξ := s5a_eLpNorm_sq hu
  refine ⟨?_, ?_⟩
  · -- first inequality
    set c1 : ℝ := max 1 (k / c0) with hc1
    by_cases hfin : ENNReal.ofReal c1 * ((eLpNorm u 2 volume) ^ 2 + gagSq σ u) = ⊤
    · rw [hfin]; exact le_top
    have hlt : ENNReal.ofReal c1 * ((eLpNorm u 2 volume) ^ 2 + gagSq σ u) < ⊤ := lt_top_iff_ne_top.2 hfin
    have hLw : ∫⁻ ξ : Euc d, ENNReal.ofReal (wt ξ ^ σ) * Fe ξ ≤
        ENNReal.ofReal c1 * ((eLpNorm u 2 volume) ^ 2 + gagSq σ u) := by
      calc ∫⁻ ξ : Euc d, ENNReal.ofReal (wt ξ ^ σ) * Fe ξ
          ≤ ∫⁻ ξ : Euc d, (Fe ξ + ENNReal.ofReal k * (ENNReal.ofReal (‖ξ‖ ^ (2 * σ)) * Fe ξ)) := by
            refine lintegral_mono fun ξ => ?_
            have hw := s5a_wt_le h0.le h1.le ξ
            calc ENNReal.ofReal (wt ξ ^ σ) * Fe ξ
                ≤ ENNReal.ofReal (1 + k * ‖ξ‖ ^ (2 * σ)) * Fe ξ := by
                  gcongr
                  exact hw
                _ = _ := by
                  rw [ENNReal.ofReal_add zero_le_one (by positivity), ENNReal.ofReal_one,
                    ENNReal.ofReal_mul hk0, add_mul, one_mul, mul_assoc]
        _ = (∫⁻ ξ : Euc d, Fe ξ) + ENNReal.ofReal k * Q := by
            rw [lintegral_add_left' hFem, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        _ ≤ ENNReal.ofReal c1 * (∫⁻ ξ : Euc d, Fe ξ) + ENNReal.ofReal c1 * (C0 * Q) := by
            refine add_le_add ?_ ?_
            · exact le_mul_of_one_le_left' (ENNReal.one_le_ofReal.2 (le_max_left _ _))
            · rw [hCeq, ← mul_assoc, ← ENNReal.ofReal_mul (le_trans zero_le_one (le_max_left _ _))]
              refine mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) Q
              have : k / c0 ≤ c1 := le_max_right _ _
              rwa [div_le_iff₀ hc0] at this
        _ = _ := by rw [hE, hgag, mul_add]
    have hM : HRS.PDE.ToolboxRd.MemSobolev σ u := s5a_memSobolev hu (lt_of_le_of_lt hLw hlt)
    rw [s5a_sobolevNormE_sq hM]
    exact hLw
  · -- second inequality
    by_cases hM : HRS.PDE.ToolboxRd.MemSobolev σ u
    · rw [s5a_sobolevNormE_sq hM, hgag, hCeq]
      gcongr
      refine lintegral_mono fun ξ => ?_
      gcongr
      exact s5a_norm_rpow_le_wt h0.le ξ
    · have : sobolevNormE σ u = ⊤ := by unfold sobolevNormE; rw [if_neg hM]
      rw [this, ENNReal.top_pow (by norm_num), ENNReal.mul_top (ENNReal.ofReal_pos.2 hc0).ne']
      exact le_top

end HRS.MH.Screened
