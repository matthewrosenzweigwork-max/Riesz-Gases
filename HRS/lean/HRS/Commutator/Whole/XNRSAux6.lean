import HRS.Commutator.Whole.XNRSAux5

/-!
# Packet X-NRS, part 6: Fourier representation of the Gagliardo form for a general even kernel

The statements of part 5 for an arbitrary continuous even integrable nonnegative kernel `K`
(`XKer K`): `m_K(ξ) = ∫ K(z)(1 - cos 2π⟨z,ξ⟩) dz`.
-/

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal FourierTransform ContDiff SchwartzMap LineDeriv

noncomputable section

namespace HRS.Commutator.Whole.XNRS

variable {d : ℕ}

/-- A continuous even integrable nonnegative kernel. -/
structure XKer (K : Euc d → ℝ) : Prop where
  nonneg : ∀ z, 0 ≤ K z
  cont : Continuous K
  integrable : Integrable K
  even : ∀ z, K (-z) = K z

/-- `m_K(ξ) = ∫ K(z)(1 - cos 2π⟨z,ξ⟩) dz`. -/
def xmK (K : Euc d → ℝ) (ξ : Euc d) : ℝ := ∫ z, K z * xph ξ z

lemma integrable_xmK_integrand {K : Euc d → ℝ} (hK : XKer K) (ξ : Euc d) :
    Integrable (fun z : Euc d => K z * xph ξ z) := by
  refine (hK.integrable.mul_const 2).mono' ?_ (Eventually.of_forall fun z => ?_)
  · exact (hK.cont.mul (continuous_xph ξ)).aestronglyMeasurable
  · rw [Real.norm_of_nonneg (mul_nonneg (hK.nonneg z) (xph_nonneg ξ z))]
    exact mul_le_mul_of_nonneg_left (xph_le_two ξ z) (hK.nonneg z) |>.trans (le_of_eq (by ring))

lemma xint_phaseK {K : Euc d → ℝ} (hK : XKer K) (ξ : Euc d) :
    ∫ z, ((K z : ℝ) : ℂ) * (1 - HRS.PDE.ToolboxRd.FourierAux.phase z ξ) =
      ((xmK K ξ : ℝ) : ℂ) := by
  have hsplit : ∀ z : Euc d, ((K z : ℝ) : ℂ) * (1 - HRS.PDE.ToolboxRd.FourierAux.phase z ξ) =
      ((K z * xph ξ z : ℝ) : ℂ) +
        Complex.I * ((K z * Real.sin (2 * Real.pi * inner ℝ z ξ) : ℝ) : ℂ) := by
    intro z
    unfold HRS.PDE.ToolboxRd.FourierAux.phase xph
    rw [Complex.exp_mul_I]
    have hc : Real.cos (-2 * Real.pi * inner ℝ z ξ) = Real.cos (2 * Real.pi * inner ℝ z ξ) := by
      rw [show -2 * Real.pi * inner ℝ z ξ = -(2 * Real.pi * inner ℝ z ξ) by ring, Real.cos_neg]
    have hs : Real.sin (-2 * Real.pi * inner ℝ z ξ) = -Real.sin (2 * Real.pi * inner ℝ z ξ) := by
      rw [show -2 * Real.pi * inner ℝ z ξ = -(2 * Real.pi * inner ℝ z ξ) by ring, Real.sin_neg]
    rw [← Complex.ofReal_cos, ← Complex.ofReal_sin, hc, hs]
    push_cast
    ring
  simp_rw [hsplit]
  have hi1 : Integrable (fun z : Euc d => ((K z * xph ξ z : ℝ) : ℂ)) :=
    (integrable_xmK_integrand hK ξ).ofReal
  have hi2 : Integrable (fun z : Euc d => Complex.I *
      ((K z * Real.sin (2 * Real.pi * inner ℝ z ξ) : ℝ) : ℂ)) := by
    refine Integrable.const_mul ?_ _
    refine Integrable.ofReal ?_
    refine hK.integrable.mono' ?_ (Eventually.of_forall fun z => ?_)
    · exact (hK.cont.mul (by fun_prop)).aestronglyMeasurable
    · show ‖K z * Real.sin (2 * Real.pi * inner ℝ z ξ)‖ ≤ K z
      rw [norm_mul, Real.norm_of_nonneg (hK.nonneg z), Real.norm_eq_abs]
      exact mul_le_of_le_one_right (hK.nonneg z) (Real.abs_sin_le_one _)
  rw [integral_add hi1 hi2, integral_const_mul, integral_complex_ofReal, integral_complex_ofReal]
  have hz : ∫ z : Euc d, K z * Real.sin (2 * Real.pi * inner ℝ z ξ) = 0 := by
    have h := integral_neg_eq_self (fun z : Euc d => K z * Real.sin (2 * Real.pi * inner ℝ z ξ))
      volume
    simp only [hK.even, inner_neg_left, mul_neg, Real.sin_neg, integral_neg] at h
    linarith
  rw [hz]
  simp [xmK]


theorem xJ_fourierK {K : Euc d → ℝ} (hK : XKer K) (h ψ : 𝓢(Euc d, ℂ)) :
    ∫ z, ((K z : ℝ) : ℂ) * (∫ x, (h x - h (x - z)) * ψ x) =
      ∫ ξ, ((xmK K ξ : ℝ) : ℂ) * 𝓕 h ξ * 𝓕 ψ (-ξ) := by
  have step1 : ∀ z : Euc d, ∫ x, (h x - h (x - z)) * ψ x =
      ∫ ξ, (1 - HRS.PDE.ToolboxRd.FourierAux.phase z ξ) * 𝓕 h ξ * 𝓕 ψ (-ξ) := by
    intro z
    have := xparseval (xdiff z h) ψ
    simp only [xdiff_apply] at this
    rw [this]
    refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
    simp only [fourier_xdiff, mul_assoc]
  simp_rw [step1]
  simp_rw [← integral_const_mul]
  have hint : Integrable (Function.uncurry fun (z ξ : Euc d) =>
      ((K z : ℝ) : ℂ) * ((1 - HRS.PDE.ToolboxRd.FourierAux.phase z ξ) * 𝓕 h ξ * 𝓕 ψ (-ξ)))
      (volume.prod volume) := by
    have hg : Integrable (fun p : Euc d × Euc d => K p.1 * (2 * ‖𝓕 h p.2 * 𝓕 ψ (-p.2)‖))
        (volume.prod volume) :=
      Integrable.mul_prod (f := K) (g := fun ξ : Euc d => 2 * ‖𝓕 h ξ * 𝓕 ψ (-ξ)‖)
        hK.integrable ((xFpair_int h ψ).norm.const_mul 2)
    refine hg.mono' ?_ (Eventually.of_forall fun p => ?_)
    · have hc : Continuous (fun p : Euc d × Euc d =>
          ((K p.1 : ℝ) : ℂ) * ((1 - HRS.PDE.ToolboxRd.FourierAux.phase p.1 p.2) *
            𝓕 h p.2 * 𝓕 ψ (-p.2))) := by
        refine (Complex.continuous_ofReal.comp (hK.cont.comp continuous_fst)).mul ?_
        refine ((continuous_const.sub continuous_phase_prod).mul
          ((𝓕 h : 𝓢(Euc d, ℂ)).continuous.comp continuous_snd)).mul
          ((𝓕 ψ : 𝓢(Euc d, ℂ)).continuous.comp (continuous_neg.comp continuous_snd))
      exact hc.aestronglyMeasurable
    · show ‖((K p.1 : ℝ) : ℂ) * ((1 - HRS.PDE.ToolboxRd.FourierAux.phase p.1 p.2) *
          𝓕 h p.2 * 𝓕 ψ (-p.2))‖ ≤ K p.1 * (2 * ‖𝓕 h p.2 * 𝓕 ψ (-p.2)‖)
      have hn1 : ‖((K p.1 : ℝ) : ℂ) * ((1 - HRS.PDE.ToolboxRd.FourierAux.phase p.1 p.2) *
          𝓕 h p.2 * 𝓕 ψ (-p.2))‖ = K p.1 * (‖1 - HRS.PDE.ToolboxRd.FourierAux.phase p.1 p.2‖ *
          ‖𝓕 h p.2‖ * ‖𝓕 ψ (-p.2)‖) := by
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hK.nonneg p.1), norm_mul, norm_mul]
      rw [hn1, norm_mul (𝓕 h p.2)]
      have h1 : ‖1 - HRS.PDE.ToolboxRd.FourierAux.phase p.1 p.2‖ ≤ 2 := by
        refine (norm_sub_le _ _).trans ?_
        rw [norm_one, HRS.PDE.ToolboxRd.FourierAux.norm_phase]; norm_num
      apply mul_le_mul_of_nonneg_left _ (hK.nonneg p.1)
      have := mul_nonneg (norm_nonneg (𝓕 h p.2)) (norm_nonneg (𝓕 ψ (-p.2)))
      nlinarith [norm_nonneg (𝓕 h p.2), norm_nonneg (𝓕 ψ (-p.2))]
  rw [integral_integral_swap hint]
  refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
  simp only
  have : ∀ z : Euc d, ((K z : ℝ) : ℂ) *
      ((1 - HRS.PDE.ToolboxRd.FourierAux.phase z ξ) * 𝓕 h ξ * 𝓕 ψ (-ξ)) =
      (((K z : ℝ) : ℂ) * (1 - HRS.PDE.ToolboxRd.FourierAux.phase z ξ)) * (𝓕 h ξ * 𝓕 ψ (-ξ)) := by
    intro z; ring
  simp_rw [this]
  rw [integral_mul_const, xint_phaseK hK ξ]
  ring


theorem xenergyK {K : Euc d → ℝ} (hK : XKer K) (h : 𝓢(Euc d, ℂ)) :
    ∫ z, K z * (∫ x, ‖h x - h (x - z)‖ ^ 2) = ∫ ξ, 2 * xmK K ξ * ‖𝓕 h ξ‖ ^ 2 := by
  simp_rw [xdiff_plancherel, ← integral_const_mul]
  have hint : Integrable (Function.uncurry fun (z ξ : Euc d) =>
      K z * (2 * xph ξ z * ‖𝓕 h ξ‖ ^ 2)) (volume.prod volume) := by
    have hg : Integrable (fun p : Euc d × Euc d => K p.1 * (4 * ‖𝓕 h p.2‖ ^ 2))
        (volume.prod volume) :=
      Integrable.mul_prod (f := K) (g := fun ξ : Euc d => 4 * ‖𝓕 h ξ‖ ^ 2)
        hK.integrable ((integrable_fourier_norm_sq h).const_mul 4)
    refine hg.mono' ?_ (Eventually.of_forall fun p => ?_)
    · have hc : Continuous (fun p : Euc d × Euc d =>
          K p.1 * (2 * xph p.2 p.1 * ‖𝓕 h p.2‖ ^ 2)) := by
        refine (hK.cont.comp continuous_fst).mul ?_
        have : Continuous (fun p : Euc d × Euc d => xph p.2 p.1) := by
          unfold xph; fun_prop
        exact (continuous_const.mul this).mul
          (((𝓕 h : 𝓢(Euc d, ℂ)).continuous.comp continuous_snd).norm.pow 2)
      exact hc.aestronglyMeasurable
    · show ‖K p.1 * (2 * xph p.2 p.1 * ‖𝓕 h p.2‖ ^ 2)‖ ≤ K p.1 * (4 * ‖𝓕 h p.2‖ ^ 2)
      have h0 : 0 ≤ K p.1 := hK.nonneg p.1
      have h1 := xph_nonneg p.2 p.1
      have h2 := xph_le_two p.2 p.1
      rw [Real.norm_of_nonneg (by positivity)]
      apply mul_le_mul_of_nonneg_left _ h0
      nlinarith [sq_nonneg ‖𝓕 h p.2‖]
  rw [integral_integral_swap hint]
  refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
  simp only
  have : ∀ z : Euc d, K z * (2 * xph ξ z * ‖𝓕 h ξ‖ ^ 2) =
      (K z * xph ξ z) * (2 * ‖𝓕 h ξ‖ ^ 2) := by intro z; ring
  simp_rw [this]
  rw [integral_mul_const]
  unfold xmK
  ring

end HRS.Commutator.Whole.XNRS
