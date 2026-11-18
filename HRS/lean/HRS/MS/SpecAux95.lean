import HRS.MS.SpecAux94

/-!
# S8M: the normalization `⟨e, w⟩_μ = 1` bounds `‖w‖²_μ ≤ β` (S8.7, R4)

Namespace `HRS.MS.Spec`, helper prefix `s8p_`.  With `e = ν w + U - c`, `∫ w dμ = 0`: `⟨e, w⟩_μ = ν ∫ w² dμ + ∫ h (g*h)`
(`h = ρ w = √ρ φ`), and the energy `∫ h (g*h)` is nonnegative (`s8p_Good_energy_nonneg`); hence `W₂ = ∫ ρ w² ≤ β`.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal RealInnerProductSpace ContDiff

namespace HRS.MS.Spec

open HRS HRS.Whole HRS.MS.MovDec

variable {d : ℕ} {s : ℝ} {ρ : Euc d → ℝ}

local notation "𝓢R" => SchwartzMap (Euc d) ℝ

theorem s8p_h_good (hρ : Mov2eRho d ρ) (φ : 𝓢R) : s8p_Good (mov2eH ρ φ) := by
  obtain ⟨C, c, hC, hc, h0, -⟩ := s8p_h_bounds hρ φ
  exact s8p_good_of_gauss (s8p_h_smooth hρ φ).continuous hc h0

theorem s8p_W2_le (hd : 1 ≤ d) (hs0 : 0 < s) (hsd : s < d) (hρ : Mov2eRho d ρ) (hE : Mov2eEll d ρ)
    {β : ℝ} (hβ : 0 < β) (φ : 𝓢R) (hmean : ∫ x, Real.sqrt (ρ x) * φ x = 0)
    (hnorm : ∫ x, s8p_E d s β ρ φ x * (φ x / Real.sqrt (ρ x)) ∂(HRS.Whole.withDensityReal ρ) = 1) :
    s8p_W2 ρ φ ≤ β := by
  haveI := mov2e_isProb hρ
  set μ := HRS.Whole.withDensityReal ρ with hμ
  have hf2 := (s8p_f_memLp hρ φ)
  have hU2 := s8p_U_memLp hd hs0.le hsd hρ hE β φ
  have hfi : Integrable (fun x => φ x / Real.sqrt (ρ x)) μ := hf2.integrable one_le_two
  have hff : Integrable (fun x => (φ x / Real.sqrt (ρ x)) * (φ x / Real.sqrt (ρ x))) μ :=
    hf2.integrable_mul hf2
  have hUf : Integrable (fun x => s8p_U d s ρ φ x * (φ x / Real.sqrt (ρ x))) μ := hU2.integrable_mul hf2
  have e1 : ∀ x, s8p_E d s β ρ φ x * (φ x / Real.sqrt (ρ x)) =
      β⁻¹ * ((φ x / Real.sqrt (ρ x)) * (φ x / Real.sqrt (ρ x))) +
        s8p_U d s ρ φ x * (φ x / Real.sqrt (ρ x)) - s8p_Cc d s ρ φ * (φ x / Real.sqrt (ρ x)) := fun x => by
    unfold s8p_E; ring
  simp_rw [e1] at hnorm
  have hA : Integrable (fun x => β⁻¹ * ((φ x / Real.sqrt (ρ x)) * (φ x / Real.sqrt (ρ x))) +
      s8p_U d s ρ φ x * (φ x / Real.sqrt (ρ x))) μ := (hff.const_mul β⁻¹).add hUf
  have hB : Integrable (fun x => s8p_Cc d s ρ φ * (φ x / Real.sqrt (ρ x))) μ := hfi.const_mul _
  rw [integral_sub hA hB, integral_add (hff.const_mul β⁻¹) hUf,
    integral_const_mul, integral_const_mul, s8p_f_mean hρ φ hmean, mul_zero, sub_zero] at hnorm
  have hQ : 0 ≤ ∫ x, s8p_U d s ρ φ x * (φ x / Real.sqrt (ρ x)) ∂μ := by
    rw [mov2e_integral_mu hρ]
    have := s8p_Good_energy_nonneg hd hs0 hsd (s8p_h_good hρ φ)
    refine this.trans (le_of_eq ?_)
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only
    have := mov2e_rho_div hρ φ x
    have e : mov2eH ρ φ x = ρ x * (φ x / Real.sqrt (ρ x)) := by rw [this]
    unfold s8p_U
    rw [e]; ring
  have hW : ∫ x, (φ x / Real.sqrt (ρ x)) * (φ x / Real.sqrt (ρ x)) ∂μ = s8p_W2 ρ φ := by
    rw [mov2e_integral_mu hρ]
    unfold s8p_W2 s8p_ws
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only; ring
  rw [hW] at hnorm
  have : β⁻¹ * s8p_W2 ρ φ ≤ 1 := by linarith
  rw [inv_mul_le_iff₀ hβ] at this
  linarith

end HRS.MS.Spec
