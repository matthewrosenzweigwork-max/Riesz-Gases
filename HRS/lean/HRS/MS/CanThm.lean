import HRS.MS.CanThmAux2

/-!
# CAN2: `euc_thermal_canonical` and `logThermal_canonical`

* `logThermal_canonical_proof : type_of% @HRS.Whole.logThermal_canonical` is clause 1 only
  (`HRS.MS.Can2.can2_clause1_log`).
* `euc_thermal_canonical_proof : type_of% @HRS.Whole.euc_thermal_canonical`: clause 1 is
  `HRS.MS.Can2.can2_clause1_pos`; clause 2 is the Jensen argument of the supplement (S lines 1378-1384),
  proved without `euc_static`: for `g ≥ 0`, one integrates out the first (resp. first two) particles with
  the weight `e^{-βV}`; Jensen's inequality `∫ w e^{-u} ≥ Λ e^{-βB}` (with `∫ g(x-y) w(x) dx ≤ B Λ`,
  from the K1 bound `riesz_conv_gaussian_bound`) gives `W_{n+1} ≥ Λ e^{-βB} W_n` for the total masses of the
  `n`-particle weights with the coupling `1/N`, hence `P^{(1)} ≤ e^{βB} γ` and `P^{(2)} ≤ e^{2βB} γ ⊗ γ`;
  `γ ≤ ρ/c` (`cb_thermal_two_sided`) converts this into `μ_β`.  No statement was adjusted.
-/

open MeasureTheory
open scoped ENNReal NNReal

noncomputable section

namespace HRS.MS.Can2

open HRS.Whole HRS.MS.Thm

variable {d : ℕ}

/-- `exp(-β V) = k⁻¹ γ` for the confinement `V = a|x|²/2` and the Gaussian comparison density `γ`. -/
lemma can2_w_eq {a β : ℝ} (ha : 0 < a) (hβ : 0 < β) (x : Euc d) :
    Real.exp (-β * confinement a x) =
      ((β * a / (2 * Real.pi)) ^ ((d : ℝ) / 2))⁻¹ * gaussianComparison d a β x := by
  have hk : 0 < (β * a / (2 * Real.pi)) ^ ((d : ℝ) / 2) := by positivity
  rw [gaussianComparison_eq, ← mul_assoc, inv_mul_cancel₀ hk.ne', one_mul]
  unfold confinement
  congr 1
  ring

lemma can2_L_eq {a β : ℝ} (ha : 0 < a) (hβ : 0 < β) :
    can2_L (confinement a : Euc d → ℝ) β = ((β * a / (2 * Real.pi)) ^ ((d : ℝ) / 2))⁻¹ := by
  unfold can2_L
  simp only [can2_w_eq ha hβ]
  rw [integral_const_mul, (gaussianComparison_isProbDensity (d := d) ha hβ).integral_one, mul_one]

lemma can2_rieszKernel_measurable {s : ℝ} (hs : s ≠ 0) : Measurable (rieszKernel d s : Euc d → ℝ) := by
  have h : (rieszKernel d s : Euc d → ℝ) = fun z => ‖z‖ ^ (-s) := funext fun z => by
    simp [rieszKernel, hs]
  rw [h]; exact measurable_norm.pow_const _

/-- The abstract setting holds for the Riesz kernel with `0 < s < d` and the confinement. -/
lemma can2_setting_pos (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 < s) (hsd : s < d) {a β : ℝ} (ha : 0 < a)
    (hβ : 0 < β) :
    ∃ B : ℝ, Can2Setting (rieszKernel d s) (confinement a) β B := by
  obtain ⟨B₀, hB₀⟩ := riesz_conv_gaussian_bound (d := d) hd hs0 hsd ha hβ
  have hk : 0 < (β * a / (2 * Real.pi)) ^ ((d : ℝ) / 2) := by positivity
  refine ⟨max B₀ 0, ?_⟩
  have hVm : Measurable (confinement a : Euc d → ℝ) := by
    unfold confinement; fun_prop
  refine ⟨hβ, can2_rieszKernel_measurable hs0.ne', fun x => ?_, hVm, ?_, le_max_right _ _, fun y => ?_⟩
  · simp only [rieszKernel, hs0.ne', ite_false]
    exact Real.rpow_nonneg (norm_nonneg _) _
  · have h := (gaussianComparison_integrable (d := d) ha hβ).const_mul
      ((β * a / (2 * Real.pi)) ^ ((d : ℝ) / 2))⁻¹
    refine h.congr (ae_of_all _ fun x => ?_)
    simp only [can2_w_eq ha hβ]
  · have e : ∀ x : Euc d, rieszKernel d s (x - y) * Real.exp (-β * confinement a x) =
        ((β * a / (2 * Real.pi)) ^ ((d : ℝ) / 2))⁻¹ *
          (rieszKernel d s (y - x) * gaussianComparison d a β x) := fun x => by
      rw [can2_w_eq ha hβ, ← neg_sub y x, can2_rieszKernel_neg]
      ring
    simp only [e]
    refine ⟨((hB₀ y).1.const_mul _), ?_⟩
    have hL := can2_L_eq (d := d) ha hβ
    unfold can2_L at hL
    rw [integral_const_mul, hL]
    have h1 := (hB₀ y).2
    have h2 : ∫ x, rieszKernel d s (y - x) * gaussianComparison d a β x ≤ max B₀ 0 := h1.trans (le_max_left _ _)
    calc ((β * a / (2 * Real.pi)) ^ ((d : ℝ) / 2))⁻¹ *
          ∫ x, rieszKernel d s (y - x) * gaussianComparison d a β x
        ≤ ((β * a / (2 * Real.pi)) ^ ((d : ℝ) / 2))⁻¹ * max B₀ 0 :=
          mul_le_mul_of_nonneg_left h2 (inv_nonneg.2 hk.le)
      _ = _ := mul_comm _ _

lemma can2_smul_mono {α : Type*} [MeasurableSpace α] {a b : ℝ≥0∞} (h : a ≤ b) (m : Measure α) :
    a • m ≤ b • m :=
  Measure.le_iff.2 fun s _ => by
    simp only [Measure.smul_apply, smul_eq_mul]
    exact mul_le_mul_left h _

/-- Clause 2 of `euc_thermal_canonical`. -/
theorem can2_clause2_pos (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 < s) (hsd : s < d) {a β : ℝ}
    (ha : 0 < a) (hβ : 0 < β) :
    ∃ C : ℝ≥0, ∀ N, 2 ≤ N →
      HRS.Whole.firstMarginal (HRS.Whole.canonicalGibbs (rieszKernel d s) (confinement a) N β) ≤
        C • thermalMeasure d s a β ∧
      HRS.Whole.secondMarginal (HRS.Whole.canonicalGibbs (rieszKernel d s) (confinement a) N β) ≤
        C • (thermalMeasure d s a β).prod (thermalMeasure d s a β) := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨B, hS⟩ := can2_setting_pos hd1 hs0 hsd ha hβ
  obtain ⟨hprob, c, C', hc, hC', hbd⟩ := cb_thermal_two_sided hd1 hs0 hsd ha hβ
  set K : ℝ := Real.exp (β * B) / c with hK
  have hK0 : 0 ≤ K := (div_pos (Real.exp_pos _) hc).le
  have hdom : ∀ x : Euc d, (can2_L (confinement a : Euc d → ℝ) β * Real.exp (-(β * B)))⁻¹ *
      Real.exp (-β * confinement a x) ≤ K * thermalDensity d s a β x := by
    intro x
    have hk : 0 < (β * a / (2 * Real.pi)) ^ ((d : ℝ) / 2) := by positivity
    rw [can2_w_eq ha hβ, can2_L_eq ha hβ]
    have hρ := (hbd x).1
    have e : (((β * a / (2 * Real.pi)) ^ ((d : ℝ) / 2))⁻¹ * Real.exp (-(β * B)))⁻¹ *
        (((β * a / (2 * Real.pi)) ^ ((d : ℝ) / 2))⁻¹ * gaussianComparison d a β x) =
        Real.exp (β * B) * gaussianComparison d a β x := by
      rw [mul_inv, inv_inv, ← Real.exp_neg, neg_neg]
      field_simp
    rw [e, hK, div_mul_eq_mul_div, le_div_iff₀ hc]
    calc Real.exp (β * B) * gaussianComparison d a β x * c
        = Real.exp (β * B) * (c * gaussianComparison d a β x) := by ring
      _ ≤ Real.exp (β * B) * thermalDensity d s a β x :=
          mul_le_mul_of_nonneg_left hρ (Real.exp_pos _).le
      _ = _ := by ring
  refine ⟨(K + K * K).toNNReal, fun N hN => ?_⟩
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 2 := ⟨N - 2, by omega⟩
  have hρm := hprob.measurable
  refine ⟨?_, ?_⟩
  · have h1 := can2_first_final hS (n + 1) hK0 hdom
    have e : HRS.Whole.firstMarginal (HRS.Whole.canonicalGibbs (rieszKernel d s) (confinement a) (n + 2) β) =
        (HRS.Whole.canonicalGibbs (rieszKernel d s) (confinement a) (n + 1 + 1) β).map
          (fun X : Fin (n + 1 + 1) → Euc d => X 0) := by
      unfold HRS.Whole.firstMarginal
      rw [dif_pos (by omega)]
      rfl
    rw [e]
    refine h1.trans ?_
    exact can2_smul_mono (by
      change ENNReal.ofReal K ≤ ENNReal.ofReal (K + K * K)
      exact ENNReal.ofReal_le_ofReal (by nlinarith)) _
  · have h2 := can2_second_final hS n hρm hK0 hdom
    have e : HRS.Whole.secondMarginal (HRS.Whole.canonicalGibbs (rieszKernel d s) (confinement a) (n + 2) β) =
        (HRS.Whole.canonicalGibbs (rieszKernel d s) (confinement a) (n + 2) β).map
          (fun X : Fin (n + 2) → Euc d => (X 0, X 1)) := by
      unfold HRS.Whole.secondMarginal
      rw [dif_pos (by omega)]
      rfl
    rw [e]
    refine h2.trans ?_
    refine can2_smul_mono ?_ _
    rw [← ENNReal.ofReal_mul hK0]
    change ENNReal.ofReal (K * K) ≤ ENNReal.ofReal (K + K * K)
    exact ENNReal.ofReal_le_ofReal (by nlinarith)

/-- `P_N = Q_N(μ_β)` for the logarithmic thermal measure. -/
theorem logThermal_canonical_proof : type_of% @HRS.Whole.logThermal_canonical := by
  intro d hd a β ha hβ N
  exact can2_clause1_log hd ha hβ N

/-- Proposition S3.4, last clauses. -/
theorem euc_thermal_canonical_proof : type_of% @HRS.Whole.euc_thermal_canonical := by
  intro d s hd hs0 hsd a β ha hβ
  exact ⟨fun N => can2_clause1_pos hd hs0 hsd ha hβ N, can2_clause2_pos hd hs0 hsd ha hβ⟩

end HRS.MS.Can2

end
