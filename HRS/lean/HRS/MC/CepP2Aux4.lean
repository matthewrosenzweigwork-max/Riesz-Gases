import HRS.MC.CepP2Aux3

/-!
# Packet CEPP2 (aux 4): Fourier inversion on `ℝ × ℝⁿ` for smooth compactly supported functions
-/

open MeasureTheory
open scoped FourierTransform
noncomputable section
namespace HRS.MC.CepP2
variable {n : ℕ}

instance instXSAddHaar : (volume : Measure (XS n)).IsAddHaarMeasure := by
  change (volume.prod volume : Measure (ℝ × EuclideanSpace ℝ (Fin n))).IsAddHaarMeasure
  infer_instance

abbrev VX (n : ℕ) := WithLp 2 (XS n)

lemma inner_VX (v w : VX n) : inner ℝ v w = ell w.ofLp v.ofLp := by
  simp [WithLp.prod_inner_apply, ell_apply]
  exact real_inner_comm _ _

lemma ell_smul (c : ℝ) (ζ q : XS n) : ell (c • ζ) q = c * ell ζ q := by
  simp [ell_apply, inner_smul_left]; ring

/-- Fourier transform of a function on `X`: `∫ φ(q) e^{-i ℓ_ζ(q)} dq`. -/
def phat (φ : XS n → ℝ) (ζ : XS n) : ℂ :=
  ∫ q, (φ q : ℂ) * Complex.exp (-(ell ζ q : ℂ) * Complex.I)

lemma contDiff_ofLp_VX : ContDiff ℝ smTop (fun v : VX n => v.ofLp) := by
  exact (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ (EuclideanSpace ℝ (Fin n))).contDiff

lemma hasCompactSupport_ofLp_VX {φ : XS n → ℝ} (hc : HasCompactSupport φ) :
    HasCompactSupport (fun v : VX n => ((φ v.ofLp : ℝ) : ℂ)) := by
  have h1 : HasCompactSupport (fun x : XS n => ((φ x : ℝ) : ℂ)) :=
    hc.comp_left (g := fun x : ℝ => (x : ℂ)) (by simp)
  exact h1.comp_homeomorph (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ (EuclideanSpace ℝ (Fin n))).toHomeomorph

lemma ell_comm (ζ p : XS n) : ell ζ p = ell p ζ := by
  simp only [ell_apply]; rw [mul_comm, real_inner_comm]

lemma finrank_XS (n : ℕ) : Module.finrank ℝ (XS n) = n + 1 := by
  simp [Module.finrank_prod]; ring

lemma toLp_meas : MeasurePreserving (WithLp.toLp 2 : XS n → VX n) volume volume :=
  WithLp.volume_preserving_toLp ℝ (EuclideanSpace ℝ (Fin n))

lemma toLp_emb : MeasurableEmbedding (WithLp.toLp 2 : XS n → VX n) :=
  (MeasurableEquiv.toLp 2 (XS n)).measurableEmbedding

theorem inv_X {φ : XS n → ℝ} (hφ : ContDiff ℝ smTop φ) (hc : HasCompactSupport φ) :
    Integrable (phat φ) ∧ ∀ p : XS n, (φ p : ℂ) =
      (((2 * Real.pi) ^ (n + 1))⁻¹ : ℝ) • ∫ ζ, Complex.exp ((ell ζ p : ℂ) * Complex.I) * phat φ ζ := by
  set f : VX n → ℂ := fun v => ((φ v.ofLp : ℝ) : ℂ) with hf
  have hfs : ContDiff ℝ smTop f := Complex.ofRealCLM.contDiff.comp (hφ.comp contDiff_ofLp_VX)
  have hfc : HasCompactSupport f := hasCompactSupport_ofLp_VX hc
  set s := hfc.toSchwartzMap hfs with hs
  have hpi : (2 * Real.pi) ≠ 0 := by positivity
  have hF : ∀ ζ : XS n, 𝓕 (⇑s) (WithLp.toLp 2 ((2 * Real.pi)⁻¹ • ζ)) = phat φ ζ := by
    intro ζ
    rw [Real.fourier_eq']
    rw [← toLp_meas.integral_comp toLp_emb]
    unfold phat
    refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
    have hsf : ∀ v, s v = f v := fun v => rfl
    simp only [hsf, hf, inner_VX, ell_smul]
    simp
    have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
    have e : 2 * (Real.pi : ℂ) * ((Real.pi : ℂ)⁻¹ * 2⁻¹ * ((ell ζ q : ℝ) : ℂ)) = ((ell ζ q : ℝ) : ℂ) := by
      field_simp
    rw [e, mul_comm]
  have hInt : Integrable (𝓕 ⇑s) volume := (SchwartzMap.fourierTransformCLM ℂ s).integrable
  have hinv : 𝓕⁻ (𝓕 ⇑s) = ⇑s := Continuous.fourierInv_fourier_eq s.continuous s.integrable hInt
  have hFs : ∀ ζ' : XS n, 𝓕 ⇑s (WithLp.toLp 2 ζ') = phat φ ((2 * Real.pi) • ζ') := by
    intro ζ'
    rw [← hF]
    rw [smul_smul, inv_mul_cancel₀ hpi, one_smul]
  constructor
  · have h1 : Integrable (fun ζ' : XS n => 𝓕 ⇑s (WithLp.toLp 2 ζ')) volume :=
      (toLp_meas.integrable_comp_emb toLp_emb).2 hInt
    have e : (fun x : XS n => 𝓕 ⇑s (WithLp.toLp 2 ((2 * Real.pi)⁻¹ • x))) = phat φ := by
      funext x; exact hF x
    have h3 : Integrable (fun x : XS n => 𝓕 ⇑s (WithLp.toLp 2 ((2 * Real.pi)⁻¹ • x))) volume :=
      h1.comp_smul (R := (2 * Real.pi)⁻¹) (inv_ne_zero hpi)
    rw [e] at h3
    exact h3
  · intro p
    have h := congrFun hinv (WithLp.toLp 2 p)
    have hsp : s (WithLp.toLp 2 p) = (φ p : ℂ) := rfl
    rw [← hsp, ← h, Real.fourierInv_eq']
    simp only [smul_eq_mul]
    rw [← toLp_meas.integral_comp toLp_emb]
    have hc2 := Measure.integral_comp_smul (volume : Measure (XS n))
      (fun ζ : XS n => Complex.exp ((ell ζ p : ℂ) * Complex.I) * phat φ ζ) (2 * Real.pi)
    rw [finrank_XS] at hc2
    have hpos : 0 ≤ ((2 * Real.pi) ^ (n + 1))⁻¹ := by positivity
    rw [abs_of_nonneg hpos] at hc2
    rw [← hc2]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [inner_VX, hFs, ell_smul]
    rw [ell_comm p x]

end HRS.MC.CepP2
