import HRS.MS.R2WinErrAux16

/-!
# S10.5 packet G0: the commutator input at a moving reference with a general entropy bound

`s105_comm_expect`: if `H(f | Q_{N,β}(ρ dx)) ≤ H_b` then every `Λ`-Lipschitz field `v` satisfies
`E_f |Comm_N(v; Z, ρ)| ≤ C Λ (H_b/N + δ_N)` (`W:r2:pressure-input` with `δ_N` replaced by `B_N/N`, S L8460-8470); this is
`s104_comm_expect` with the entropy bound `H_b` in place of `H₀ N δ_N`.  `s105_forcing_expect` is the pushforward form along a random
configuration, and `s105_energy_moment` bounds `E(F_N + o_N)` by `C(H_b/N + δ_N) + o_N` (`euclidean_pair_entropy_self`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Function Set
open scoped ENNReal NNReal

namespace HRS.MS.R2GenInit

open HRS.Whole HRS.MS.Wr HRS.MS.PrepStat HRS.MS.R2WinErr

variable {d : ℕ}

theorem s105_comm_expect (hd : 2 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (M L β : ℝ) (hβ : 0 < β) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ρ : Euc d → ℝ, HRS.Whole.IsProbDensity ρ → (∀ x, ρ x ≤ M) →
      (s = 0 → HasLogMoment (HRS.Whole.withDensityReal ρ) L) → ∀ N : ℕ, 2 ≤ N →
      ∀ f : Measure (EucConfig d N), IsProbabilityMeasure f → ∀ Hb : ℝ, 0 ≤ Hb →
      HRS.relEntropy f (HRS.Whole.modulatedGibbs (HRS.Whole.rieszKernel d s) N β (HRS.Whole.withDensityReal ρ)) ≤
        ENNReal.ofReal Hb →
      ∀ (v : Euc d → Euc d) (Λ : ℝ≥0), LipschitzWith Λ v →
        Integrable (fun Z : EucConfig d N => |commN d s v Z (HRS.Whole.withDensityReal ρ)|) f ∧
        ∫ Z, |commN d s v Z (HRS.Whole.withDensityReal ρ)| ∂f ≤ C * Λ * (Hb / N + deltaN d s N) := by
  obtain ⟨cH, hcH, CH, hHh⟩ :=
    euclidean_pair_entropy_proof hd hs0 hsd M L β (β + 1) (s + 1) hβ (by linarith)
  set CH' : ℝ := max CH 0 with hCH'
  have hCH'0 : 0 ≤ CH' := le_max_right _ _
  refine ⟨2 * CH', by positivity, ?_⟩
  intro ρ hρ hρM hlog N hN f hf Hb hHb0 hH v Λ hv
  have hμprob : IsProbabilityMeasure (HRS.Whole.withDensityReal ρ) :=
    Q34.isProbabilityMeasure_nu hρ
  set μ := HRS.Whole.withDensityReal ρ with hμ
  set T' : ℝ := (N : ℝ) * deltaN d s N with hT'
  have hT1 : 1 ≤ T' := wr8_one_le_mul_deltaN hs0 N (by omega)
  have hN1 : 0 < N := by omega
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hδ : 0 < deltaN d s N := by
    by_contra h
    push Not at h
    have : (N : ℝ) * deltaN d s N ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hN0.le h
    linarith
  set Q : Measure (EucConfig d N) := HRS.Whole.modulatedGibbs (rieszKernel d s) N β μ with hQ
  have hHfin : InformationTheory.klDiv f Q ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hH
  have hHnn : 0 ≤ (InformationTheory.klDiv f Q).toReal := ENNReal.toReal_nonneg
  have hHreal : (InformationTheory.klDiv f Q).toReal ≤ Hb :=
    ENNReal.toReal_le_of_le_ofReal hHb0 hH
  have hcm := HRS.MS.Comm.comm_meas (d := d) (s := s) v hv.continuous.measurable
  by_cases hΛ : Λ = 0
  · subst hΛ
    have h0 : ∀ Z : EucConfig d N, |commN d s v Z μ| = 0 := fun Z => by
      rw [s32_commN_zero s hv]; simp
    simp only [h0]
    refine ⟨integrable_zero _ _ _, ?_⟩
    simp
  · have hv1 := s32_lipschitz_scale hΛ hv
    have hB := s32_comm_isBounded (d := d) hs0 hv1
    obtain ⟨-, hbd⟩ := hHh ρ hρ hρM hlog _ hB N hN β ⟨le_rfl, by linarith⟩
    obtain ⟨hi1, hb1⟩ := hbd f hf (lt_top_iff_ne_top.2 hHfin)
    have hΛ0 : (0 : ℝ) ≤ Λ := Λ.coe_nonneg
    have hpt : ∀ X : EucConfig d N, |commN d s v X μ| = (2 * (Λ : ℝ) / N) *
        ((N : ℝ) * |pairEnergy (commutatorKernel d s ((Λ : ℝ)⁻¹ • v)) X μ|) := by
      intro X
      rw [s32_commN_eq]
      have e : commutatorKernel d s v = fun x y =>
          (Λ : ℝ) * commutatorKernel d s ((Λ : ℝ)⁻¹ • v) x y :=
        funext fun x => funext fun y => s32_commKernel_scale s hΛ v x y
      rw [e, s32_pairEnergy_const_mul, abs_mul, abs_mul, abs_of_nonneg hΛ0]
      rw [abs_two]
      field_simp
    have hi : Integrable (fun X : EucConfig d N => |commN d s v X μ|) f :=
      (hi1.const_mul (2 * (Λ : ℝ) / N)).congr (Filter.Eventually.of_forall fun X => (hpt X).symm)
    refine ⟨hi, ?_⟩
    have e3 : ∫ X, |commN d s v X μ| ∂f = (2 * (Λ : ℝ) / N) *
        ∫ X, (N : ℝ) * |pairEnergy (commutatorKernel d s ((Λ : ℝ)⁻¹ • v)) X μ| ∂f := by
      rw [← integral_const_mul]
      exact integral_congr_ae (Filter.Eventually.of_forall hpt)
    rw [e3]
    have hb2 : ∫ X, (N : ℝ) * |pairEnergy (commutatorKernel d s ((Λ : ℝ)⁻¹ • v)) X μ| ∂f ≤
        CH' * (Hb + T') := by
      refine hb1.trans ?_
      have h1 : CH * ((InformationTheory.klDiv f Q).toReal + (N : ℝ) * deltaN d s N) ≤
          CH' * ((InformationTheory.klDiv f Q).toReal + T') :=
        mul_le_mul (le_max_left _ _) le_rfl (add_nonneg hHnn (by linarith)) hCH'0
      refine h1.trans (mul_le_mul_of_nonneg_left ?_ hCH'0)
      nlinarith
    have hcoef : 0 ≤ 2 * (Λ : ℝ) / N := by positivity
    refine (mul_le_mul_of_nonneg_left hb2 hcoef).trans (le_of_eq ?_)
    rw [hT']; field_simp

end HRS.MS.R2GenInit
