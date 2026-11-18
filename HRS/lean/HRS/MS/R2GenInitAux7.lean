import HRS.MS.R2GenInitAux6

/-!
# S10.5 input `hmom` (part 1): the entropy against the product reference

`s105_kl_product`: if `H(f | Q_{N,β}(ρ dx)) ≤ H_b` then `H(f | (ρ dx)^{⊗N}) ≤ C₁ (H_b + Nδ_N)` (change of reference measure
`log φ = -log K - βN F_N`, the pressure bound on `log K` and `euclidean_pair_entropy_self`; the proof of `euclidean_preparations_stationary` (S3.2) with
the entropy hypothesis in place of the stationary dynamics).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Function Set
open scoped ENNReal NNReal

namespace HRS.MS.R2GenInit

open HRS.Whole HRS.MS.Wr HRS.MS.PrepStat

variable {d : ℕ}

theorem s105_kl_product (hd : 2 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (M L β : ℝ) (hβ : 0 < β) :
    ∃ C₁ : ℝ, 0 ≤ C₁ ∧ ∀ ρ : Euc d → ℝ, HRS.Whole.IsProbDensity ρ → (∀ x, ρ x ≤ M) →
      (s = 0 → HasLogMoment (HRS.Whole.withDensityReal ρ) L) → ∀ N : ℕ, 2 ≤ N →
      ∀ f : Measure (EucConfig d N), IsProbabilityMeasure f → ∀ Hb : ℝ, 0 ≤ Hb →
      InformationTheory.klDiv f (HRS.Whole.modulatedGibbs (HRS.Whole.rieszKernel d s) N β
        (HRS.Whole.withDensityReal ρ)) ≤ ENNReal.ofReal Hb →
      InformationTheory.klDiv f (Measure.pi fun _ : Fin N => HRS.Whole.withDensityReal ρ) ≠ ⊤ ∧
      (InformationTheory.klDiv f (Measure.pi fun _ : Fin N => HRS.Whole.withDensityReal ρ)).toReal ≤
        C₁ * (Hb + (N : ℝ) * deltaN d s N) := by
  have hbm0 : 0 < β := hβ
  have hbmp : β < β + 1 := by linarith
  obtain ⟨θ0, hθ0, C0, hP⟩ := euclidean_pressure_proof hd hs0 hsd M L β (β + 1) 0 hbm0 hbmp
  obtain ⟨cE, hcE, CE, hS⟩ := euclidean_pair_entropy_self_proof hd hs0 hsd M L β (β + 1) hbm0 hbmp
  have hhz : IsBoundedPairKernel s 0 (fun _ _ : Euc d => (0 : ℝ)) :=
    ⟨measurable_const, fun _ _ => rfl, fun x y _ => by simp⟩
  set C0' : ℝ := max C0 0 with hC0'
  set CE' : ℝ := max CE 0 with hCE'
  have hC0'0 : 0 ≤ C0' := le_max_right _ _
  have hCE'0 : 0 ≤ CE' := le_max_right _ _
  refine ⟨1 + C0' + β * CE', by positivity, ?_⟩
  intro ρ hρ hρM hlog N hN f hf Hb hHb0 hH
  have hμprob : IsProbabilityMeasure (HRS.Whole.withDensityReal ρ) := Q34.isProbabilityMeasure_nu hρ
  set μ := HRS.Whole.withDensityReal ρ with hμ
  set T' : ℝ := (N : ℝ) * deltaN d s N with hT'
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hδ : 0 ≤ deltaN d s N := HRS.MS.S53.s53_deltaN_nonneg s (by omega)
  have hT0 : 0 ≤ T' := mul_nonneg hN0.le hδ
  set G : Euc d → Euc d → ℝ := fun x y => rieszKernel d s (x - y) with hG
  have hGm : Measurable (Function.uncurry G) := wr9_rieszKernel_pair_meas s
  have hFm : Measurable (fun X : EucConfig d N => pairEnergy G X μ) := wr9_measurable_pairEnergy hGm
  obtain ⟨hWb, hlogKb⟩ : GibbsWellDefined G N β μ ∧ |Real.log (pairNormalizer G N β μ)| ≤ C0 * T' := by
    obtain ⟨hW', hbd⟩ := hP ρ hρ hρM hlog (fun _ _ => 0) hhz N hN β ⟨le_rfl, by linarith⟩ 0
      (by rw [abs_zero]; exact hθ0.le)
    simp only [zero_mul, sub_zero] at hW' hbd
    exact ⟨hW', by simpa only [hT', mul_assoc] using hbd⟩
  have hQprob : IsProbabilityMeasure (pairGibbs G N β μ) := wr9_gibbs_prob hWb
  set Q : Measure (EucConfig d N) := HRS.Whole.modulatedGibbs (rieszKernel d s) N β μ with hQ
  have hQeq : Q = pairGibbs G N β μ := rfl
  have : IsProbabilityMeasure Q := hQprob
  set π : Measure (EucConfig d N) := Measure.pi fun _ : Fin N => μ with hπ
  have hHfin : InformationTheory.klDiv f Q ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hH
  have hHreal : (InformationTheory.klDiv f Q).toReal ≤ Hb := ENNReal.toReal_le_of_le_ofReal hHb0 hH
  have hHnn : 0 ≤ (InformationTheory.klDiv f Q).toReal := ENNReal.toReal_nonneg
  obtain ⟨hFint, hFbd⟩ := (hS ρ hρ hρM hlog N hN β ⟨le_rfl, by linarith⟩).2 f hf
    (lt_top_iff_ne_top.2 hHfin)
  have hFint' : Integrable (fun X : EucConfig d N => (N : ℝ) * |pairEnergy G X μ|) f := hFint
  have hFbd' : ∫ X : EucConfig d N, (N : ℝ) * |pairEnergy G X μ| ∂f ≤ CE' * (Hb + T') := by
    refine le_trans hFbd ?_
    exact mul_le_mul (le_max_left _ _)
      (show (InformationTheory.klDiv f Q).toReal + (N : ℝ) * deltaN d s N ≤ Hb + T' by rw [hT']; linarith)
      (add_nonneg hHnn hT0) hCE'0
  obtain ⟨φ, hφm, hφpos, hQπ, hlogφ⟩ := s32_ref_tilt hGm hWb
  have hNF : Integrable (fun X : EucConfig d N => (N : ℝ) * pairEnergy G X μ) f := by
    have h1 : Integrable (fun X : EucConfig d N => ‖(N : ℝ) * pairEnergy G X μ‖) f :=
      hFint'.congr (Filter.Eventually.of_forall fun X => by
        simp only [norm_mul, Real.norm_eq_abs, abs_of_pos hN0])
    exact (integrable_norm_iff (hFm.const_mul _).aestronglyMeasurable).1 h1
  have hint_log : Integrable (fun X : EucConfig d N => Real.log (φ X)) f :=
    ((integrable_const (-Real.log (pairNormalizer G N β μ))).sub (hNF.const_mul β)).congr
      (Filter.Eventually.of_forall fun X => (hlogφ X).symm)
  obtain ⟨hπne, hπeq⟩ := s32_kl_refchange f Q π hφm hφpos hQπ hHfin hint_log
  have hlogint : ∫ X, Real.log (φ X) ∂f ≤ C0' * T' + β * (CE' * (Hb + T')) := by
    have h1 : ∫ X, Real.log (φ X) ∂f ≤
        ∫ X, (|Real.log (pairNormalizer G N β μ)| + β * ((N : ℝ) * |pairEnergy G X μ|)) ∂f := by
      refine integral_mono hint_log ((integrable_const _).add (hFint'.const_mul β)) fun X => ?_
      rw [hlogφ X]
      have hF1 : -(pairEnergy G X μ) ≤ |pairEnergy G X μ| := neg_le_abs _
      have hF2 : -((N : ℝ) * pairEnergy G X μ) ≤ (N : ℝ) * |pairEnergy G X μ| := by nlinarith
      have h3 := mul_le_mul_of_nonneg_left hF2 hβ.le
      linarith [neg_le_abs (Real.log (pairNormalizer G N β μ))]
    refine h1.trans ?_
    rw [integral_add (integrable_const _) (hFint'.const_mul β), integral_const, integral_const_mul]
    simp only [measureReal_def, measure_univ, ENNReal.toReal_one, one_smul]
    have h4 : |Real.log (pairNormalizer G N β μ)| ≤ C0' * T' :=
      hlogKb.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hT0)
    have h5 := mul_le_mul_of_nonneg_left hFbd' hβ.le
    linarith
  refine ⟨hπne, ?_⟩
  rw [hπeq]
  have hCE2 : β * (CE' * (Hb + T')) ≤ β * CE' * (Hb + T') := by rw [mul_assoc]
  nlinarith [mul_nonneg hC0'0 hT0, mul_nonneg hCE'0 hT0, mul_nonneg hCE'0 hHb0, mul_nonneg hβ.le hCE'0,
    mul_nonneg (mul_nonneg hβ.le hCE'0) (add_nonneg hHb0 hT0)]

end HRS.MS.R2GenInit
