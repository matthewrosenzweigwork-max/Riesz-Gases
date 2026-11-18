import HRS.Commutator.Whole.ApproxAux

/-!
# Scaling lemmas for the sub-Coulomb commutator (packet CMX-SCALE, helpers)

Helpers carry the prefix `cmxSA_`.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform ContDiff

namespace HRS.Commutator.Whole

open HRS HRS.Whole

variable {d : ℕ} {s : ℝ}

/-- the scaling homeomorphism -/
def cmxSA_smulHomeo (η : ℝ) (hη : 0 < η) : Euc d ≃ₜ Euc d :=
  Homeomorph.smulOfNeZero η hη.ne'

lemma cmxSA_integral_comp_smul (η : ℝ) (hη : 0 < η) (f : Euc d → ℝ) :
    ∫ x, f (η • x) = (η ^ d)⁻¹ * ∫ x, f x := by
  rw [Measure.integral_comp_smul volume f η, cmxSA_finrank, abs_of_pos (by positivity)]
  rfl

lemma cmxSA_integral_comp_smul' {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (η : ℝ) (hη : 0 < η) (f : Euc d → E) :
    ∫ x, f (η • x) = (η ^ d)⁻¹ • ∫ x, f x := by
  rw [Measure.integral_comp_smul volume f η, cmxSA_finrank, abs_of_pos (by positivity)]

theorem cmxSA_scaleDens_bdd (η : ℝ) (hη : 0 < η) (ρ : Euc d → ℝ) (hρ : BddCptDensity ρ) :
    BddCptDensity (scaleDens η ρ) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (hρ.measurable.comp (measurable_const_smul η)).const_mul _
  · obtain ⟨B, hB⟩ := hρ.bdd
    refine ⟨η ^ d * B, fun x => ?_⟩
    unfold scaleDens
    rw [abs_mul, abs_of_pos (by positivity)]
    exact mul_le_mul_of_nonneg_left (hB _) (by positivity)
  · have := hρ.cpt.comp_homeomorph (cmxSA_smulHomeo (d := d) η hη)
    exact this.mul_left (f := fun _ => η ^ d)
  · unfold scaleDens
    rw [integral_const_mul, cmxSA_integral_comp_smul η hη ρ, hρ.mass]
    field_simp


lemma cmxSA_eLpNorm_comp_smul (η : ℝ) (hη : 0 < η) (p : ℝ≥0∞) (ρ : Euc d → ℝ) :
    eLpNorm (fun x => ρ (η • x)) p volume =
      ENNReal.ofReal (η ^ d)⁻¹ ^ ((1 / p).toReal) * eLpNorm ρ p volume := by
  have hme : MeasurableEmbedding (fun x : Euc d => η • x) :=
    (cmxSA_smulHomeo (d := d) η hη).measurableEmbedding
  have h1 := hme.eLpNorm_map_measure (g := ρ) (p := p) (μ := volume)
  have h2 : Measure.map (fun x : Euc d => η • x) volume =
      ENNReal.ofReal (η ^ d)⁻¹ • volume := by
    rw [Measure.map_addHaar_smul volume hη.ne', cmxSA_finrank, abs_of_pos (by positivity)]
  have hc : ENNReal.ofReal (η ^ d)⁻¹ ≠ 0 := by
    have : 0 < (η ^ d)⁻¹ := by positivity
    simpa using this
  rw [h2, eLpNorm_smul_measure_of_ne_zero hc] at h1
  exact h1.symm

theorem cmxSA_normE_scaleDens (η : ℝ) (hη : 0 < η) (p : ℝ≥0∞) (ρ : Euc d → ℝ) :
    normE p (scaleDens η ρ) = η ^ ((d : ℝ) * (1 - (p⁻¹).toReal)) * normE p ρ := by
  have hsc : (scaleDens η ρ) = (η ^ d) • (fun x => ρ (η • x)) := by
    funext x; simp [scaleDens]
  unfold normE
  rw [hsc, eLpNorm_const_smul, cmxSA_eLpNorm_comp_smul η hη p ρ]
  set E := eLpNorm ρ p volume
  have e1 : (1 / p).toReal = (p⁻¹).toReal := by rw [one_div]
  rw [e1]
  have hpos : 0 < η ^ d := by positivity
  have hnn : 0 ≤ ((η ^ d)⁻¹) := by positivity
  have : ‖η ^ d‖ₑ = ENNReal.ofReal (η ^ d) := by
    rw [Real.enorm_eq_ofReal hpos.le]
  rw [this, ENNReal.ofReal_rpow_of_nonneg hnn ENNReal.toReal_nonneg, ← mul_assoc,
    ← ENNReal.ofReal_mul hpos.le, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]
  congr 1
  rw [Real.inv_rpow hpos.le, ← Real.rpow_natCast, ← Real.rpow_neg_one, ← Real.rpow_mul hη.le]
  rw [Real.rpow_neg_one, ← div_eq_mul_inv, ← Real.rpow_sub hη]
  congr 1; ring


/-! ### Scaling of the distributional fractional derivative -/

lemma cmxSA_fourier_comp (η : ℝ) (hη : 0 < η) (f : Euc d → ℂ) (ξ : Euc d) :
    𝓕 (fun x => f (η⁻¹ • x)) ξ = ((η ^ d : ℝ) : ℂ) * 𝓕 f (η • ξ) := by
  rw [Real.fourier_eq', Real.fourier_eq']
  set F : Euc d → ℂ := fun x => Complex.exp ((↑(-2 * Real.pi * inner ℝ x ξ) * Complex.I)) •
    f (η⁻¹ • x) with hF
  have h1 := cmxSA_integral_comp_smul' η hη F
  have h2 : ∫ x, F (η • x) = ∫ y, Complex.exp ((↑(-2 * Real.pi * inner ℝ y (η • ξ)) * Complex.I)) • f y := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [hF, smul_smul, inv_smul_smul₀ hη.ne', real_inner_smul_left, real_inner_smul_right]
  have h3 : ∫ x, F x = ((η ^ d : ℝ) : ℂ) * ∫ x, F (η • x) := by
    rw [h1, Complex.real_smul, ← mul_assoc]
    have : ((η ^ d : ℝ) : ℂ) * (((η ^ d)⁻¹ : ℝ) : ℂ) = 1 := by
      rw [← Complex.ofReal_mul]; rw [mul_inv_cancel₀ (by positivity)]; simp
    rw [this, one_mul]
  rw [h3, h2]


/-- `𝓕⁻[(2π|ξ|)^α 𝓕 f]`. -/
def cmxSA_Psi (α : ℝ) (f : Euc d → ℂ) (x : Euc d) : ℂ :=
  𝓕⁻ (fun ξ : Euc d => (((2 * Real.pi * ‖ξ‖) ^ α : ℝ) : ℂ) * 𝓕 f ξ) x

lemma cmxSA_Psi_comp (α : ℝ) (η : ℝ) (hη : 0 < η) (f : Euc d → ℂ) (x : Euc d) :
    cmxSA_Psi α (fun y => f (η⁻¹ • y)) x = ((η ^ (-α) : ℝ) : ℂ) * cmxSA_Psi α f (η⁻¹ • x) := by
  unfold cmxSA_Psi
  rw [Real.fourierInv_eq', Real.fourierInv_eq']
  set H : Euc d → ℂ := fun ξ => Complex.exp ((↑(2 * Real.pi * inner ℝ ξ x) * Complex.I)) •
    (((((2 * Real.pi * ‖ξ‖) ^ α : ℝ)) : ℂ) * 𝓕 (fun y => f (η⁻¹ • y)) ξ) with hH
  have h1 := cmxSA_integral_comp_smul' (E := ℂ) η⁻¹ (inv_pos.2 hη) H
  have h2 : ∫ ζ, H (η⁻¹ • ζ) = ((η ^ d : ℝ) : ℂ) * ((η ^ (-α) : ℝ) : ℂ) *
      ∫ ζ, Complex.exp ((↑(2 * Real.pi * inner ℝ ζ (η⁻¹ • x)) * Complex.I)) •
        (((((2 * Real.pi * ‖ζ‖) ^ α : ℝ)) : ℂ) * 𝓕 f ζ) := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ζ => ?_)
    simp only [hH, cmxSA_fourier_comp η hη, smul_eq_mul, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.2 hη), smul_smul, mul_inv_cancel₀ hη.ne', one_smul]
    have e1 : (2 * Real.pi * (η⁻¹ * ‖ζ‖)) ^ α = η ^ (-α) * (2 * Real.pi * ‖ζ‖) ^ α := by
      rw [show 2 * Real.pi * (η⁻¹ * ‖ζ‖) = η⁻¹ * (2 * Real.pi * ‖ζ‖) by ring,
        Real.mul_rpow (inv_nonneg.2 hη.le) (by positivity), Real.inv_rpow hη.le,
        ← Real.rpow_neg hη.le]
    have e2 : inner ℝ (η⁻¹ • ζ) x = inner ℝ ζ (η⁻¹ • x) := by
      rw [real_inner_smul_left, real_inner_smul_right]
    rw [e1, e2]; push_cast; ring
  have h3 : ∫ ξ, H ξ = ((η⁻¹ ^ d : ℝ) : ℂ) * ∫ ζ, H (η⁻¹ • ζ) := by
    rw [h1, Complex.real_smul, ← mul_assoc]
    have : (((η⁻¹) ^ d : ℝ) : ℂ) * ((((η⁻¹) ^ d)⁻¹ : ℝ) : ℂ) = 1 := by
      rw [← Complex.ofReal_mul]; rw [mul_inv_cancel₀ (by positivity)]; simp
    rw [this, one_mul]
  rw [h3, h2, ← mul_assoc, ← mul_assoc]
  have : (((η⁻¹) ^ d : ℝ) : ℂ) * ((η ^ d : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, ← mul_pow, inv_mul_cancel₀ hη.ne']; simp
  rw [this, one_mul]


/-- `φ(·/η)` as a Schwartz function. -/
def cmxSA_schw (η : ℝ) (hη : 0 < η) (φ : SchwartzMap (Euc d) ℂ) : SchwartzMap (Euc d) ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (LinearEquiv.toContinuousLinearEquiv
      (LinearEquiv.smulOfNeZero ℝ (Euc d) η⁻¹ (inv_ne_zero hη.ne'))) φ

lemma cmxSA_schw_apply (η : ℝ) (hη : 0 < η) (φ : SchwartzMap (Euc d) ℂ) (x : Euc d) :
    cmxSA_schw η hη φ x = φ (η⁻¹ • x) := rfl

lemma cmxSA_fracRep_scale (α : ℝ) (η : ℝ) (hη : 0 < η) {v w : Euc d → ℝ}
    (h : IsFracDerivRep α v w) :
    IsFracDerivRep α (fun x => η⁻¹ * v (η • x)) (fun x => η ^ (α - 1) * w (η • x)) := by
  intro φ
  obtain ⟨h1, h2, h3⟩ := h (cmxSA_schw η hη φ)
  -- the key identity for the test function
  have hP : ∀ x, 𝓕⁻ (fun ξ : Euc d => (((2 * Real.pi * ‖ξ‖) ^ α : ℝ) : ℂ) * 𝓕 (⇑φ) ξ) x =
      ((η ^ α : ℝ) : ℂ) * 𝓕⁻ (fun ξ : Euc d => (((2 * Real.pi * ‖ξ‖) ^ α : ℝ) : ℂ) *
        𝓕 (⇑(cmxSA_schw η hη φ)) ξ) (η • x) := by
    intro x
    have := cmxSA_Psi_comp α η hη (⇑φ) (η • x)
    unfold cmxSA_Psi at this
    rw [inv_smul_smul₀ hη.ne'] at this
    have e : (⇑(cmxSA_schw η hη φ)) = fun y => φ (η⁻¹ • y) := rfl
    rw [e, this, ← mul_assoc, ← Complex.ofReal_mul, ← Real.rpow_add hη]
    simp
  set c : ℂ := ((η ^ (α - 1) : ℝ) : ℂ) with hc
  have hcα : c = ((η⁻¹ : ℝ) : ℂ) * ((η ^ α : ℝ) : ℂ) := by
    rw [hc, Real.rpow_sub_one hη.ne', div_eq_inv_mul]; push_cast; ring
  have eL : (fun x => (((η⁻¹ * v (η • x) : ℝ)) : ℂ) *
      𝓕⁻ (fun ξ : Euc d => (((2 * Real.pi * ‖ξ‖) ^ α : ℝ) : ℂ) * 𝓕 (⇑φ) ξ) x) =
      fun x => c * (((v (η • x) : ℝ) : ℂ) * 𝓕⁻ (fun ξ : Euc d =>
        (((2 * Real.pi * ‖ξ‖) ^ α : ℝ) : ℂ) * 𝓕 (⇑(cmxSA_schw η hη φ)) ξ) (η • x)) := by
    funext x
    rw [hP x, hcα]; push_cast; ring
  have eR : (fun x => (((η ^ (α - 1) * w (η • x) : ℝ)) : ℂ) * φ x) =
      fun x => c * (((w (η • x) : ℝ) : ℂ) * cmxSA_schw η hη φ (η • x)) := by
    funext x
    rw [cmxSA_schw_apply, inv_smul_smul₀ hη.ne', hc]; push_cast; ring
  refine ⟨?_, ?_, ?_⟩
  · rw [eL]; exact (h1.comp_smul hη.ne').const_mul c
  · rw [eR]; exact (h2.comp_smul hη.ne').const_mul c
  · rw [eL, eR, integral_const_mul, integral_const_mul,
      cmxSA_integral_comp_smul' η hη (fun y => ((v y : ℝ) : ℂ) * 𝓕⁻ (fun ξ : Euc d =>
        (((2 * Real.pi * ‖ξ‖) ^ α : ℝ) : ℂ) * 𝓕 (⇑(cmxSA_schw η hη φ)) ξ) y),
      cmxSA_integral_comp_smul' η hη (fun y => ((w y : ℝ) : ℂ) * cmxSA_schw η hη φ y), h3]

theorem cmxSA_subTransport_scale (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) (η : ℝ)
    (hη : 0 < η) (v : Euc d → Euc d) (K : ℝ) (hv : SubTransport d s v K) :
    SubTransport d s (scaleVec η v) K := by
  obtain ⟨L, F, hF, hL, ⟨w, hw, hn⟩, hK⟩ := hv
  have hd3 : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (0 : ℝ) < (d : ℝ) - s - 2 := by linarith
  set α : ℝ := ((d : ℝ) - s) / 2 with hα
  set P : ℝ := 2 * d / ((d : ℝ) - s - 2) with hP
  have hPpos : 0 < P := by rw [hP]; positivity
  refine ⟨L, F, hF, ?_, ⟨fun x => η ^ (α - 1) • w (η • x), ?_, ?_⟩, hK⟩
  · refine LipschitzWith.of_dist_le_mul fun x y => ?_
    simp only [scaleVec, dist_smul₀, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hη)]
    have := hL.dist_le_mul (η • x) (η • y)
    rw [dist_smul₀, Real.norm_eq_abs, abs_of_pos hη] at this
    calc η⁻¹ * dist (v (η • x)) (v (η • y)) ≤ η⁻¹ * (L * (η * dist x y)) :=
          mul_le_mul_of_nonneg_left this (inv_nonneg.2 hη.le)
      _ = L * dist x y := by field_simp
  · intro i
    have := cmxSA_fracRep_scale α η hη (hw i)
    simpa [scaleVec] using this
  · change eLpNorm (fun x => ‖η ^ (α - 1) • w (η • x)‖) (ENNReal.ofReal P) volume ≤
      ENNReal.ofReal F
    have e : (fun x => ‖η ^ (α - 1) • w (η • x)‖) =
        (η ^ (α - 1)) • (fun x => ‖w (η • x)‖) := by
      funext x
      simp only [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hη _),
        Pi.smul_apply, smul_eq_mul]
    rw [e, eLpNorm_const_smul, cmxSA_eLpNorm_comp_smul η hη (ENNReal.ofReal P) (fun x => ‖w x‖)]
    have hone : ‖η ^ (α - 1)‖ₑ * ENNReal.ofReal (η ^ d)⁻¹ ^ ((1 / ENNReal.ofReal P).toReal) = 1 := by
      have hpos : 0 < η ^ (α - 1) := Real.rpow_pos_of_pos hη _
      rw [Real.enorm_eq_ofReal hpos.le, ENNReal.ofReal_rpow_of_nonneg (by positivity)
        ENNReal.toReal_nonneg, ← ENNReal.ofReal_mul hpos.le]
      have : η ^ (α - 1) * ((η ^ d)⁻¹) ^ ((1 / ENNReal.ofReal P).toReal) = 1 := by
        rw [one_div, ← ENNReal.ofReal_inv_of_pos hPpos, ENNReal.toReal_ofReal (by positivity)]
        rw [Real.inv_rpow (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul hη.le,
          ← Real.rpow_neg_one, Real.rpow_neg_one]
        have h1 : (d : ℝ) * P⁻¹ = α - 1 := by
          rw [hP, hα, inv_div]; field_simp
        rw [h1, mul_inv_cancel₀ hpos.ne']
      rw [this]; simp
    rw [← mul_assoc, hone, one_mul]; exact hn

/-! ### Change of variables in the pair functional -/

lemma cmxSA_single (η : ℝ) (hη : 0 < η) (ρ : Euc d → ℝ) (F : Euc d → ℝ) :
    ∫ y, F y * scaleDens η ρ y = ∫ u, F (η⁻¹ • u) * ρ u := by
  have h := cmxSA_integral_comp_smul η hη (fun u => F (η⁻¹ • u) * ρ u)
  have e : (fun y => F y * scaleDens η ρ y) =
      fun y => η ^ d * ((fun u => F (η⁻¹ • u) * ρ u) (η • y)) := by
    funext y
    simp only [scaleDens, inv_smul_smul₀ hη.ne']; ring
  rw [e, integral_const_mul, h]
  have : η ^ d * (η ^ d)⁻¹ = 1 := mul_inv_cancel₀ (by positivity)
  rw [← mul_assoc, this, one_mul]

theorem cmxSA_pairGen_scale {N : ℕ} (k : Euc d → Euc d → ℝ) (η : ℝ) (hη : 0 < η)
    (X : Fin N → Euc d) (ρ : Euc d → ℝ) :
    pairGen k (scaleConf η X) (scaleDens η ρ) =
      pairGen (fun a b => k (η⁻¹ • a) (η⁻¹ • b)) X ρ := by
  have t2 : ∑ i, ∫ y, k (scaleConf η X i) y * scaleDens η ρ y =
      ∑ i, ∫ y, k (η⁻¹ • X i) (η⁻¹ • y) * ρ y :=
    Finset.sum_congr rfl fun i _ => cmxSA_single η hη ρ (fun y => k (scaleConf η X i) y)
  have h1 : ∀ x, ∫ y, k x y * scaleDens η ρ x * scaleDens η ρ y =
      scaleDens η ρ x * ∫ u, k x (η⁻¹ • u) * ρ u := by
    intro x
    have := cmxSA_single η hη ρ (fun y => k x y * scaleDens η ρ x)
    rw [this, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    simp only; ring
  have t3 : ∫ x, ∫ y, k x y * scaleDens η ρ x * scaleDens η ρ y =
      ∫ x, ∫ y, k (η⁻¹ • x) (η⁻¹ • y) * ρ x * ρ y := by
    simp_rw [h1]
    have h2 := cmxSA_single η hη ρ (fun x => ∫ u, k x (η⁻¹ • u) * ρ u)
    have e : (fun x => scaleDens η ρ x * ∫ u, k x (η⁻¹ • u) * ρ u) =
        fun x => (∫ u, k x (η⁻¹ • u) * ρ u) * scaleDens η ρ x := by
      funext x; ring
    rw [e, h2]
    refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
    simp only
    rw [← integral_mul_const]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    simp only; ring
  unfold pairGen
  rw [t2, t3]
  simp only [scaleConf]

lemma cmxSA_pairGen_const_mul {N : ℕ} (c : ℝ) (k : Euc d → Euc d → ℝ) (X : Fin N → Euc d)
    (ρ : Euc d → ℝ) : pairGen (fun a b => c * k a b) X ρ = c * pairGen k X ρ := by
  unfold pairGen
  have e1 : ∀ i, ∫ y, c * k (X i) y * ρ y = c * ∫ y, k (X i) y * ρ y := by
    intro i; rw [← integral_const_mul]; exact integral_congr_ae (Filter.Eventually.of_forall fun y => by simp only; ring)
  have e2 : ∫ x, ∫ y, c * k x y * ρ x * ρ y = c * ∫ x, ∫ y, k x y * ρ x * ρ y := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only
    rw [← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall fun y => by simp only; ring)
  simp_rw [e1, e2, ← Finset.mul_sum]
  ring

lemma cmxSA_kernGrad_scale (s η : ℝ) (hη : 0 < η) (z : Euc d) :
    kernGrad s (η⁻¹ • z) = (η ^ (s + 1)) • kernGrad s z := by
  unfold kernGrad
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hη),
    Real.mul_rpow (inv_nonneg.2 hη.le) (norm_nonneg _), Real.inv_rpow hη.le, ← Real.rpow_neg hη.le,
    neg_neg]
  rw [smul_smul, smul_smul]
  congr 1
  have : η ^ (s + 2) * η⁻¹ = η ^ (s + 1) := by
    rw [Real.rpow_add hη, Real.rpow_add hη, Real.rpow_two, Real.rpow_one]; field_simp
  rw [← this]; ring

lemma cmxSA_commKer_scale (s η : ℝ) (hη : 0 < η) (v : Euc d → Euc d) (a b : Euc d) :
    commKer (kernGrad s) (scaleVec η v) (η⁻¹ • a) (η⁻¹ • b) =
      η ^ s * commKer (kernGrad s) v a b := by
  unfold commKer
  by_cases h : a = b
  · subst h; simp
  · have h' : η⁻¹ • a ≠ η⁻¹ • b := fun h2 => h (smul_right_injective _ (inv_ne_zero hη.ne') h2)
    rw [if_neg h, if_neg h', ← smul_sub, cmxSA_kernGrad_scale s η hη]
    simp only [scaleVec, smul_smul, mul_inv_cancel₀ hη.ne', one_smul]
    rw [← smul_sub, real_inner_smul_left, real_inner_smul_right]
    have : η⁻¹ * η ^ (s + 1) = η ^ s := by
      rw [Real.rpow_add hη, Real.rpow_one]; field_simp
    rw [← mul_assoc, this]

theorem cmxSA_commA_scale (s η : ℝ) (hη : 0 < η) (ρ : Euc d → ℝ) {N : ℕ} (X : Fin N → Euc d)
    (v : Euc d → Euc d) :
    commA s (scaleConf η X) (scaleDens η ρ) (scaleVec η v) = η ^ s * commA s X ρ v := by
  unfold commA
  rw [cmxSA_pairGen_scale _ η hη]
  simp_rw [cmxSA_commKer_scale s η hη v]
  rw [cmxSA_pairGen_const_mul]

end HRS.Commutator.Whole
