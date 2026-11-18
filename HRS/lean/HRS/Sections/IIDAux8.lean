import HRS.Sections.IIDAux7

/-!
# IID helper chain, part 8: coupling data `CB` (first and fourth moment of a coupling), its
mixture and translation stability, and the resulting `W₁`, `W₂` bounds.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace HRS.IID

section CB

open HRS.InitialDataAux

variable {d : ℕ} {m : ℝ}

/-- Coupling data: a coupling `π` of `ν` and `γ` with `E‖x-y‖ ≤ J` and `E‖x-y‖⁴ ≤ M`. -/
def CB (ν γ : Measure (NegSobolev d m)) (J M : ℝ) : Prop :=
  ∃ π : Measure (NegSobolev d m × NegSobolev d m), IsCoupling π ν γ ∧ IsProbabilityMeasure π ∧
    ∫⁻ z, ‖z.1 - z.2‖ₑ ∂π ≤ ENNReal.ofReal J ∧ ∫⁻ z, ‖z.1 - z.2‖ₑ ^ 4 ∂π ≤ ENNReal.ofReal M

lemma CB.w1 {ν γ : Measure (NegSobolev d m)} {J M : ℝ} (h : CB ν γ J M) :
    wassersteinE 1 ν γ ≤ ENNReal.ofReal J := by
  obtain ⟨π, hπ, hp, h1, -⟩ := h
  refine (wassersteinE_le_cost (p := 1) hπ).trans ?_
  simp only [Real.rpow_one, div_one, ENNReal.rpow_one]
  refine le_trans (le_of_eq ?_) h1
  refine lintegral_congr fun z => ?_
  rw [ofReal_norm]

lemma CB.w2 {ν γ : Measure (NegSobolev d m)} {J M : ℝ} (h : CB ν γ J M) (hJ : 0 < J) (hM : 0 < M) :
    wassersteinE 2 ν γ ≤
      ENNReal.ofReal (Real.sqrt (2 * M ^ ((1 : ℝ) / 3) * (J ^ ((1 : ℝ) / 3)) ^ 2)) := by
  obtain ⟨π, hπ, hp, h1, h4⟩ := h
  have := w2_of_l1 π Prod.fst Prod.snd measurable_fst measurable_snd hJ hM h1 h4
  have e1 : law π Prod.fst = ν := hπ.1
  have e2 : law π Prod.snd = γ := hπ.2
  rwa [e1, e2] at this

lemma CB.mix {ν₁ ν₂ γ₁ γ₂ : Measure (NegSobolev d m)} {J₁ J₂ M₁ M₂ : ℝ} (hJ₁ : 0 ≤ J₁) (hJ₂ : 0 ≤ J₂)
    (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂) (h₁ : CB ν₁ γ₁ J₁ M₁) (h₂ : CB ν₂ γ₂ J₂ M₂) :
    CB ((2 : ℝ≥0∞)⁻¹ • ν₁ + (2 : ℝ≥0∞)⁻¹ • ν₂) ((2 : ℝ≥0∞)⁻¹ • γ₁ + (2 : ℝ≥0∞)⁻¹ • γ₂)
      ((J₁ + J₂) / 2) ((M₁ + M₂) / 2) := by
  obtain ⟨π₁, hπ₁, hp₁, a₁, b₁⟩ := h₁
  obtain ⟨π₂, hπ₂, hp₂, a₂, b₂⟩ := h₂
  refine ⟨(2 : ℝ≥0∞)⁻¹ • π₁ + (2 : ℝ≥0∞)⁻¹ • π₂, ⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · rw [Measure.map_add _ _ measurable_fst, Measure.map_smul, Measure.map_smul, hπ₁.1, hπ₂.1]
    <;> exact measurable_fst.aemeasurable
  · rw [Measure.map_add _ _ measurable_snd, Measure.map_smul, Measure.map_smul, hπ₁.2, hπ₂.2]
    <;> exact measurable_snd.aemeasurable
  · constructor
    simp only [Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
    rw [← two_mul, ENNReal.mul_inv_cancel (by norm_num) (by norm_num)]
  · rw [lintegral_add_measure, lintegral_smul_measure, lintegral_smul_measure]
    calc (2 : ℝ≥0∞)⁻¹ * ∫⁻ z, ‖z.1 - z.2‖ₑ ∂π₁ + (2 : ℝ≥0∞)⁻¹ * ∫⁻ z, ‖z.1 - z.2‖ₑ ∂π₂
        ≤ (2 : ℝ≥0∞)⁻¹ * ENNReal.ofReal J₁ + (2 : ℝ≥0∞)⁻¹ * ENNReal.ofReal J₂ := by gcongr
      _ = ENNReal.ofReal ((J₁ + J₂) / 2) := by
          rw [ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_add hJ₁ hJ₂]
          simp only [ENNReal.ofReal_ofNat, div_eq_mul_inv, mul_comm _ (2 : ℝ≥0∞)⁻¹, mul_add]
  · rw [lintegral_add_measure, lintegral_smul_measure, lintegral_smul_measure]
    calc (2 : ℝ≥0∞)⁻¹ * ∫⁻ z, ‖z.1 - z.2‖ₑ ^ 4 ∂π₁ + (2 : ℝ≥0∞)⁻¹ * ∫⁻ z, ‖z.1 - z.2‖ₑ ^ 4 ∂π₂
        ≤ (2 : ℝ≥0∞)⁻¹ * ENNReal.ofReal M₁ + (2 : ℝ≥0∞)⁻¹ * ENNReal.ofReal M₂ := by gcongr
      _ = ENNReal.ofReal ((M₁ + M₂) / 2) := by
          rw [ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_add hM₁ hM₂]
          simp only [ENNReal.ofReal_ofNat, div_eq_mul_inv, mul_comm _ (2 : ℝ≥0∞)⁻¹, mul_add]

lemma CB.shift {ν γ : Measure (NegSobolev d m)} {J M : ℝ} (h : CB ν γ J M) (s : NegSobolev d m) :
    CB (ν.map fun x => x + s) (γ.map fun x => x + s) J M := by
  obtain ⟨π, hπ, hp, a, b⟩ := h
  have hm : Measurable fun z : NegSobolev d m × NegSobolev d m => (z.1 + s, z.2 + s) :=
    (measurable_fst.add_const s).prodMk (measurable_snd.add_const s)
  refine ⟨π.map fun z => (z.1 + s, z.2 + s), ⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · rw [Measure.map_map measurable_fst hm, ← hπ.1, Measure.map_map (measurable_add_const s) measurable_fst]
    rfl
  · rw [Measure.map_map measurable_snd hm, ← hπ.2, Measure.map_map (measurable_add_const s) measurable_snd]
    rfl
  · exact ⟨by rw [Measure.map_apply hm MeasurableSet.univ]; simp⟩
  · rw [lintegral_map (by fun_prop) hm]
    simpa using a
  · rw [lintegral_map (by fun_prop) hm]
    simpa using b


lemma enorm_sub_pow4_le (a b : NegSobolev d m) :
    ‖a - b‖ₑ ^ 4 ≤ ENNReal.ofReal 8 * ‖a‖ₑ ^ 4 + ENNReal.ofReal 8 * ‖b‖ₑ ^ 4 := by
  have h1 : ‖a - b‖ ≤ ‖a‖ + ‖b‖ := norm_sub_le _ _
  have h2 : ‖a - b‖ ^ 4 ≤ 8 * ‖a‖ ^ 4 + 8 * ‖b‖ ^ 4 := by
    have h0 : 0 ≤ ‖a - b‖ := norm_nonneg _
    have : ‖a - b‖ ^ 4 ≤ (‖a‖ + ‖b‖) ^ 4 := pow_le_pow_left₀ h0 h1 4
    nlinarith [sq_nonneg (‖a‖ ^ 2 - ‖b‖ ^ 2), sq_nonneg (‖a‖ - ‖b‖), norm_nonneg a, norm_nonneg b,
      mul_nonneg (norm_nonneg a) (norm_nonneg b), sq_nonneg (‖a‖ + ‖b‖)]
  have e : ∀ x : NegSobolev d m, ‖x‖ₑ ^ 4 = ENNReal.ofReal (‖x‖ ^ 4) := fun x => by
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
  rw [e, e, e, ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by norm_num),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  exact ENNReal.ofReal_le_ofReal h2

lemma lintegral_enorm_pow4_le {α : Type*} [MeasurableSpace α] (μ : Measure α) (f : α → NegSobolev d m)
    (hint : Integrable (fun x => ‖f x‖ ^ 4) μ) {M : ℝ} (hM : ∫ x, ‖f x‖ ^ 4 ∂μ ≤ M) :
    ∫⁻ x, ‖f x‖ₑ ^ 4 ∂μ ≤ ENNReal.ofReal M := by
  have e : ∀ x, ‖f x‖ₑ ^ 4 = ENNReal.ofReal (‖f x‖ ^ 4) := fun x => by
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
  simp_rw [e]
  rw [← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun x => by positivity)]
  exact ENNReal.ofReal_le_ofReal hM

lemma integrable_fld4 (hm : (d : ℝ) < 2 * m) {N : ℕ} (hN : 1 ≤ N) (μ : Measure (Torus d))
    [IsProbabilityMeasure μ] :
    Integrable (fun X => ‖fld m N μ X‖ ^ 4) (Measure.pi fun _ : Fin N => μ) := by
  set B := Real.sqrt (8 * ∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (-(2 * m)))
  refine Integrable.of_bound (((continuous_fld hm hN μ).norm.pow 4).aestronglyMeasurable)
    (((Real.sqrt N)⁻¹ * (N * B)) ^ 4) (Filter.Eventually.of_forall fun X => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  refine pow_le_pow_left₀ (norm_nonneg _) ?_ 4
  rw [fld_eq_sum hm hN μ X, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  calc ‖∑ i : Fin N, yv m μ (X i)‖ ≤ ∑ i : Fin N, ‖yv m μ (X i)‖ := norm_sum_le _ _
    _ ≤ ∑ i : Fin N, B := Finset.sum_le_sum fun i _ => norm_yv_le hm μ _
    _ = N * B := by simp

/-- Coupling data for the i.i.d. field on the modes `T` (centre = sampling density). -/
theorem CB_T (hm : (d : ℝ) < 2 * m) {c : ℝ} (hc : 0 < c) {ρ : Torus d → ℝ}
    (hρ : IsProbDensity ρ) (hρc : ∀ x, c ≤ ρ x) {γ : Measure (NegSobolev d m)}
    [IsProbabilityMeasure γ] (hγ : IsCenteredGaussianWithCov m γ (iidCov (withDensityReal ρ)))
    (T : Finset (NonzeroLattice d)) {N : ℕ} (hN : 1 ≤ N) {η : ℝ} (hη : 0 < η) :
    CB ((Measure.pi fun _ : Fin N => withDensityReal ρ).map (fld m N (withDensityReal ρ))) γ
      (Real.sqrt (8 * (∑ k ∈ T, Lattice.jp k.1 ^ (-(2 * m))) / N) *
          (T.card * Real.log (Real.exp 1 * N) + 2) + η + 2 * Real.sqrt (tailR d m T))
      (1632 * (∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (-(2 * m))) ^ 2) := by
  haveI := negSobolev_secondCountable d m
  haveI : IsProbabilityMeasure (withDensityReal ρ) := isProb_withDensityReal hρ
  obtain ⟨P, hP, hP1, hP2, hPc⟩ := iid_T_coupling hm hc hρ hρc hγ T hN hη
  set μ := withDensityReal ρ with hμ
  set Z : ℝ := ∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (-(2 * m)) with hZ
  have hF : Measurable (fld m N μ) := (continuous_fld hm hN μ).measurable
  have hm' : Measurable fun ω : Config d N × NegSobolev d m => (fld m N μ ω.1, ω.2) :=
    (hF.comp measurable_fst).prodMk measurable_snd
  have hf4 := lintegral_enorm_pow4_le (Measure.pi fun _ : Fin N => μ) (fld m N μ)
    (integrable_fld4 hm hN μ) (fourth_fld hm hN μ)
  have hg4 := lintegral_enorm_pow4_le γ id
    (by simpa using HRS.EdgeAux.gaussian_integrable_pow hγ.1 4) (M := 12 * Z ^ 2)
    (by simpa using fourth_gauss hm hγ)
  simp only [id] at hg4
  refine ⟨P.map fun ω => (fld m N μ ω.1, ω.2), ⟨?_, ?_⟩, ⟨?_⟩, ?_, ?_⟩
  · rw [Measure.map_map measurable_fst hm', ← hP1, Measure.map_map hF measurable_fst]; rfl
  · rw [Measure.map_map measurable_snd hm', ← hP2]; rfl
  · rw [Measure.map_apply hm' MeasurableSet.univ]; simp
  · rw [lintegral_map (by fun_prop) hm']; exact hPc
  · rw [lintegral_map (by fun_prop) hm']
    have e1 : ∫⁻ ω, ‖fld m N μ ω.1‖ₑ ^ 4 ∂P = ∫⁻ X, ‖fld m N μ X‖ₑ ^ 4 ∂(Measure.pi fun _ : Fin N => μ) := by
      rw [← hP1, lintegral_map (by fun_prop) measurable_fst]
    have e2 : ∫⁻ ω, ‖ω.2‖ₑ ^ 4 ∂P = ∫⁻ F, ‖F‖ₑ ^ 4 ∂γ := by
      rw [← hP2, lintegral_map (by fun_prop) measurable_snd]
    have hme : Measurable fun ω : Config d N × NegSobolev d m => ‖fld m N μ ω.1‖ₑ ^ 4 :=
      ((hF.comp measurable_fst).enorm).pow_const 4
    calc ∫⁻ ω, ‖(fld m N μ ω.1, ω.2).1 - (fld m N μ ω.1, ω.2).2‖ₑ ^ 4 ∂P
        ≤ ∫⁻ ω, (ENNReal.ofReal 8 * ‖fld m N μ ω.1‖ₑ ^ 4 + ENNReal.ofReal 8 * ‖ω.2‖ₑ ^ 4) ∂P :=
          lintegral_mono fun ω => enorm_sub_pow4_le _ _
      _ = ENNReal.ofReal 8 * ∫⁻ ω, ‖fld m N μ ω.1‖ₑ ^ 4 ∂P + ENNReal.ofReal 8 * ∫⁻ ω, ‖ω.2‖ₑ ^ 4 ∂P := by
          rw [lintegral_add_left (hme.const_mul _), lintegral_const_mul _ hme,
            lintegral_const_mul _ (measurable_snd.enorm.pow_const 4)]
      _ ≤ ENNReal.ofReal 8 * ENNReal.ofReal (192 * Z ^ 2) + ENNReal.ofReal 8 * ENNReal.ofReal (12 * Z ^ 2) := by
          rw [e1, e2]; gcongr
      _ = ENNReal.ofReal (1632 * Z ^ 2) := by
          rw [← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by norm_num),
            ← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 1; ring

end CB

end HRS.IID
