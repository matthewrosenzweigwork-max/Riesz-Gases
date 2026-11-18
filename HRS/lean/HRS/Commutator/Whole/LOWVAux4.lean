import HRS.Commutator.Whole.LOWVAux3

/-!
# CMX-LOWV auxiliary 4: pairing a finite measure against a band-limited function
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform ContDiff

namespace HRS.Commutator.Whole

open HRS HRS.Whole

variable {d : ℕ}

theorem lowv_H_integrable {Λ : ℝ} (hΛ : 0 < Λ) (μ : Measure (Euc d)) [IsFiniteMeasure μ]
    (hmom : Integrable (fun y : Euc d => ‖y‖) μ) {k : Euc d → ℝ} (hk : Continuous k) (C : ℝ)
    (hC : ∀ x, |k x| ≤ C * (1 + ‖x‖)) :
    Integrable (fun p : Euc d × Euc d => psiL Λ (p.1 - p.2) * k p.2) (μ.prod volume) := by
  have hmeas : AEStronglyMeasurable (fun p : Euc d × Euc d => psiL Λ (p.1 - p.2) * k p.2)
      (μ.prod volume) :=
    (((lowv_psiL_continuous hΛ).comp (continuous_fst.sub continuous_snd)).mul
      (hk.comp continuous_snd)).aestronglyMeasurable
  have hG := lowv_psiL_integrable_mul (d := d) hΛ 1
  set M := ∫ w : Euc d, (1 + ‖w‖) ^ 1 * |psiL Λ w| with hM
  have hpt : ∀ z x : Euc d, ‖psiL Λ (z - x) * k x‖ ≤
      (|C| * (1 + ‖z‖)) * ((1 + ‖z - x‖) ^ 1 * |psiL Λ (z - x)|) := by
    intro z x
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    have h1 : 1 + ‖x‖ ≤ (1 + ‖z‖) * (1 + ‖z - x‖) := by
      have : ‖x‖ ≤ ‖z‖ + ‖z - x‖ := by
        calc ‖x‖ = ‖z - (z - x)‖ := by rw [sub_sub_cancel]
          _ ≤ ‖z‖ + ‖z - x‖ := norm_sub_le _ _
      nlinarith [norm_nonneg z, norm_nonneg (z - x)]
    have h2 : |k x| ≤ |C| * ((1 + ‖z‖) * (1 + ‖z - x‖)) := by
      calc |k x| ≤ C * (1 + ‖x‖) := hC x
        _ ≤ |C| * (1 + ‖x‖) := by gcongr; exact le_abs_self _
        _ ≤ |C| * ((1 + ‖z‖) * (1 + ‖z - x‖)) := by gcongr
    calc |psiL Λ (z - x)| * |k x| ≤ |psiL Λ (z - x)| * (|C| * ((1 + ‖z‖) * (1 + ‖z - x‖))) := by
          gcongr
      _ = _ := by ring
  have hint : ∀ z : Euc d, Integrable (fun x => psiL Λ (z - x) * k x) := by
    intro z
    refine ((hG.comp_sub_left z).const_mul (|C| * (1 + ‖z‖))).mono' ?_
      (Eventually.of_forall fun x => hpt z x)
    exact (((lowv_psiL_continuous hΛ).comp (continuous_const.sub continuous_id)).mul
      hk).aestronglyMeasurable
  have hnorm : ∀ z : Euc d, ∫ x, ‖psiL Λ (z - x) * k x‖ ≤ (|C| * M) * (1 + ‖z‖) := by
    intro z
    calc ∫ x, ‖psiL Λ (z - x) * k x‖
        ≤ ∫ x, (|C| * (1 + ‖z‖)) * ((1 + ‖z - x‖) ^ 1 * |psiL Λ (z - x)|) :=
          integral_mono (hint z).norm ((hG.comp_sub_left z).const_mul _) (fun x => hpt z x)
      _ = (|C| * (1 + ‖z‖)) * M := by
          rw [integral_const_mul]
          congr 1
          exact integral_sub_left_eq_self (fun w : Euc d => (1 + ‖w‖) ^ 1 * |psiL Λ w|) volume z
      _ = (|C| * M) * (1 + ‖z‖) := by ring
  rw [integrable_prod_iff hmeas]
  refine ⟨Eventually.of_forall fun z => hint z, ?_⟩
  refine ((hmom.add (integrable_const 1)).const_mul (|C| * M)).mono' ?_
    (Eventually.of_forall fun z => ?_)
  · exact hmeas.norm.integral_prod_right'
  · rw [Real.norm_of_nonneg (integral_nonneg fun x => norm_nonneg _)]
    refine (hnorm z).trans ?_
    simp only [Pi.add_apply]
    rw [add_comm]

theorem lowv_pair_meas {Λ : ℝ} (hΛ : 0 < Λ) (μ : Measure (Euc d)) [IsFiniteMeasure μ]
    (hmom : Integrable (fun y : Euc d => ‖y‖) μ) {k : Euc d → ℝ} (hk : Continuous k) (C : ℝ)
    (hC : ∀ x, |k x| ≤ C * (1 + ‖x‖)) (hP : ∀ z, Pleq Λ k z = k z) :
    Integrable (fun x => k x * ∫ z, psiL Λ (x - z) ∂μ) ∧
    ∫ z, k z ∂μ = ∫ x, k x * ∫ z, psiL Λ (x - z) ∂μ := by
  have hH := lowv_H_integrable hΛ μ hmom hk C hC
  have hkz : ∀ z, k z = ∫ x, psiL Λ (z - x) * k x := by
    intro z
    rw [← hP z]
    unfold Pleq
    have := integral_sub_left_eq_self (fun y => psiL Λ y • k (z - y)) volume z
    simp only [sub_sub_cancel, smul_eq_mul] at this
    simp only [smul_eq_mul]
    exact this.symm
  have h1 : ∫ z, k z ∂μ = ∫ z, ∫ x, psiL Λ (z - x) * k x ∂volume ∂μ :=
    integral_congr_ae (Eventually.of_forall hkz)
  have h2 := integral_integral_swap (f := fun z x => psiL Λ (z - x) * k x) hH
  have hev : ∀ x z : Euc d, psiL Λ (z - x) = psiL Λ (x - z) := fun x z => by
    rw [← cmxFB_psiL_neg, neg_sub]
  have h3 : ∀ x, ∫ z, psiL Λ (z - x) * k x ∂μ = k x * ∫ z, psiL Λ (x - z) ∂μ := by
    intro x
    rw [integral_mul_const, mul_comm]
    simp_rw [hev x]
  refine ⟨?_, ?_⟩
  · have := hH.integral_prod_right
    refine this.congr (Eventually.of_forall fun x => ?_)
    simp only
    exact h3 x
  · rw [h1, h2]
    exact integral_congr_ae (Eventually.of_forall h3)

/-- Pairing of a signed measure with a band-limited function: `∫ k dσ = ∫ k a dx`,
`a = ψ_Λ * σ`. -/
theorem lowv_pair_sint {Λ : ℝ} (hΛ : 0 < Λ) (σ : SMeas d) (hf : σ.IsFinite)
    (hmp : Integrable (fun y : Euc d => ‖y‖) σ.pos) (hmn : Integrable (fun y : Euc d => ‖y‖) σ.neg)
    {k : Euc d → ℝ} (hk : Continuous k) (C : ℝ)
    (hC : ∀ x, |k x| ≤ C * (1 + ‖x‖)) (hP : ∀ z, Pleq Λ k z = k z) :
    Integrable (fun x => k x * σ.int (fun z => psiL Λ (x - z))) ∧
    σ.int k = ∫ x, k x * σ.int (fun z => psiL Λ (x - z)) := by
  obtain ⟨hp, hn⟩ := hf
  haveI := hp
  haveI := hn
  obtain ⟨hi1, he1⟩ := lowv_pair_meas hΛ σ.pos hmp hk C hC hP
  obtain ⟨hi2, he2⟩ := lowv_pair_meas hΛ σ.neg hmn hk C hC hP
  have e : ∀ x, k x * σ.int (fun z => psiL Λ (x - z)) =
      k x * ∫ z, psiL Λ (x - z) ∂σ.pos - k x * ∫ z, psiL Λ (x - z) ∂σ.neg := by
    intro x
    unfold SMeas.int
    ring
  refine ⟨?_, ?_⟩
  · simp_rw [e]
    exact hi1.sub hi2
  · simp_rw [e]
    rw [integral_sub hi1 hi2, ← he1, ← he2]
    rfl

end HRS.Commutator.Whole
