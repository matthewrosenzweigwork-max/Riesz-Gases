import HRS.Commutator.Whole.XNRSAux11

/-!
# Packet X-NRS, part 12: the super-Coulombic bound for the damped kernel

`‖∫ m_K(ξ) 𝓕h(ξ) 𝓕ψ(-ξ) dξ‖ ≤ (d + (d+2σ+2)/2) L ∫ m_K |𝓕h|²`, `ψ = v·∇h`, `K = K_δ`.
-/

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal FourierTransform ContDiff SchwartzMap LineDeriv

noncomputable section

namespace HRS.Commutator.Whole.XNRS

variable {d : ℕ}

/-- `Φ₃ = Θ Q ⟨z, v(y)⟩`. -/
def xPhi3 (h : 𝓢(Euc d, ℂ)) (v : Euc d → Euc d) (σ δ : ℝ) (p : Euc d × Euc d) : ℂ :=
  (h p.1 - h p.2) ^ 2 * ((xQ d σ δ (p.1 - p.2) * inner ℝ (p.1 - p.2) (v p.2) : ℝ) : ℂ)

lemma xPhi2_swap (h : 𝓢(Euc d, ℂ)) (v : Euc d → Euc d) (σ δ : ℝ) (p : Euc d × Euc d) :
    xPhi2 h v σ δ p.swap = -xPhi3 h v σ δ p := by
  unfold xPhi2 xPhi3 xD2
  simp only [Prod.fst_swap, Prod.snd_swap]
  have h1 : (h p.2 - h p.1) ^ 2 = (h p.1 - h p.2) ^ 2 := by ring
  have h2 : xQ d σ δ (p.2 - p.1) = xQ d σ δ (p.1 - p.2) := by
    simp only [xQ, xPhi, xP, xN]
    rw [← norm_neg (p.2 - p.1), neg_sub]
  have h3 : inner ℝ (p.2 - p.1) (v p.2) = -inner ℝ (p.1 - p.2) (v p.2) := by
    rw [← neg_sub, inner_neg_left]
  rw [h1, h2, h3]
  push_cast
  ring

lemma xPhi3_int {v : Euc d → Euc d} (hv : XTVF v) {L : ℝ} (hL0 : 0 ≤ L) (hL : XLip v L) {σ δ : ℝ}
    (hσ : 0 < σ) (hδ : 0 < δ) (h : 𝓢(Euc d, ℂ)) :
    Integrable (xPhi3 h v σ δ) (volume.prod volume) := by
  have h1 := (xPhi2_int hv hL0 hL hσ hδ h).swap
  have h2 : (xPhi2 h v σ δ ∘ Prod.swap) = fun p => -xPhi3 h v σ δ p := by
    funext p; exact xPhi2_swap h v σ δ p
  rw [h2] at h1
  simpa using h1.neg

lemma xPhi23_norm {v : Euc d → Euc d} {L : ℝ} (hL0 : 0 ≤ L) (hL : XLip v L) {σ δ : ℝ}
    (hσ : 0 < σ) (hδ : 0 < δ) (h : 𝓢(Euc d, ℂ)) (p : Euc d × Euc d) :
    ‖xPhi2 h v σ δ p - xPhi3 h v σ δ p‖ ≤
      L * ((d : ℝ) + 2 * σ + 2) * (‖h p.1 - h p.2‖ ^ 2 * xK d σ δ (p.1 - p.2)) := by
  unfold xPhi2 xPhi3 xD2
  rw [← mul_sub, norm_mul, norm_pow, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  set z := p.1 - p.2 with hz
  have hQ := xQ_nonneg hσ hδ z
  have e1 : xQ d σ δ z * inner ℝ z (v p.1) - xQ d σ δ z * inner ℝ z (v p.2) =
      xQ d σ δ z * inner ℝ z (v p.1 - v p.2) := by rw [inner_sub_right]; ring
  rw [e1, abs_mul, abs_of_nonneg hQ]
  have hi : |inner ℝ z (v p.1 - v p.2)| ≤ ‖z‖ * (L * ‖z‖) := by
    refine (abs_real_inner_le_norm _ _).trans ?_
    exact mul_le_mul_of_nonneg_left (hL p.1 p.2) (norm_nonneg _)
  have h6 := xQ_mul_sq_le hσ hδ z
  have e2 : xQ d σ δ z * (‖z‖ * (L * ‖z‖)) = L * (‖z‖ ^ 2 * xQ d σ δ z) := by ring
  calc ‖h p.1 - h p.2‖ ^ 2 * (xQ d σ δ z * |inner ℝ z (v p.1 - v p.2)|)
      ≤ ‖h p.1 - h p.2‖ ^ 2 * (xQ d σ δ z * (‖z‖ * (L * ‖z‖))) := by
        gcongr
    _ = ‖h p.1 - h p.2‖ ^ 2 * (L * (‖z‖ ^ 2 * xQ d σ δ z)) := by rw [e2]
    _ ≤ ‖h p.1 - h p.2‖ ^ 2 * (L * (((d : ℝ) + 2 * σ + 2) * xK d σ δ z)) := by gcongr
    _ = _ := by ring


/-- `E_prod = ∬ |h(x)-h(y)|² K(x-y)` over the product. -/
def xEprod (h : 𝓢(Euc d, ℂ)) (σ δ : ℝ) : ℝ :=
  ∫ p : Euc d × Euc d, ‖h p.1 - h p.2‖ ^ 2 * xK d σ δ (p.1 - p.2)

lemma xEprod_nonneg {σ δ : ℝ} (hδ : 0 < δ) (h : 𝓢(Euc d, ℂ)) : 0 ≤ xEprod h σ δ :=
  integral_nonneg fun p => mul_nonneg (sq_nonneg _) (xK_pos hδ _).le

lemma xT1 {v : Euc d → Euc d} (hv : XTVF v) {L : ℝ} (hL0 : 0 ≤ L) (hL : XLip v L) {σ δ : ℝ}
    (hσ : 0 < σ) (hδ : 0 < δ) (h : 𝓢(Euc d, ℂ)) :
    ‖∫ p, xPhi1 h v σ δ p‖ ≤ (d : ℝ) * L * xEprod h σ δ := by
  refine (norm_integral_le_integral_norm _).trans ?_
  have hb := (xe_int (xKer_xK (d := d) (σ := σ) hσ hδ) h).const_mul ((d : ℝ) * L)
  unfold xEprod
  rw [← integral_const_mul]
  refine integral_mono_of_nonneg (Eventually.of_forall fun p => norm_nonneg _) hb
    (Eventually.of_forall fun p => ?_)
  show ‖xPhi1 h v σ δ p‖ ≤ (d : ℝ) * L * (‖h p.1 - h p.2‖ ^ 2 * xK d σ δ (p.1 - p.2))
  unfold xPhi1
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
  have := xD1_bound hv hL0 hL (σ := σ) hδ p.1 p.2
  nlinarith [mul_le_mul_of_nonneg_left this (sq_nonneg ‖h p.1 - h p.2‖)]

lemma xT2 {v : Euc d → Euc d} (hv : XTVF v) {L : ℝ} (hL0 : 0 ≤ L) (hL : XLip v L) {σ δ : ℝ}
    (hσ : 0 < σ) (hδ : 0 < δ) (h : 𝓢(Euc d, ℂ)) :
    ‖∫ p, xPhi2 h v σ δ p‖ ≤ (1 / 2) * (L * ((d : ℝ) + 2 * σ + 2)) * xEprod h σ δ := by
  have h2 := xPhi2_int hv hL0 hL hσ hδ h
  have h3 := xPhi3_int hv hL0 hL hσ hδ h
  have hsw : ∫ p : Euc d × Euc d, xPhi2 h v σ δ p.swap = ∫ p : Euc d × Euc d, xPhi2 h v σ δ p :=
    integral_prod_swap (μ := (volume : Measure (Euc d))) (ν := (volume : Measure (Euc d)))
      (xPhi2 h v σ δ)
  have e1 : ∫ p : Euc d × Euc d, xPhi2 h v σ δ p.swap = -∫ p : Euc d × Euc d, xPhi3 h v σ δ p := by
    simp_rw [xPhi2_swap]; rw [integral_neg]
  have h4 : ∫ p : Euc d × Euc d, (xPhi2 h v σ δ p - xPhi3 h v σ δ p) =
      (∫ p : Euc d × Euc d, xPhi2 h v σ δ p) - ∫ p : Euc d × Euc d, xPhi3 h v σ δ p :=
    integral_sub h2 h3
  have e2 : (2 : ℂ) * ∫ p : Euc d × Euc d, xPhi2 h v σ δ p =
      ∫ p : Euc d × Euc d, (xPhi2 h v σ δ p - xPhi3 h v σ δ p) := by
    rw [h4]
    have : ∫ p : Euc d × Euc d, xPhi3 h v σ δ p = -∫ p : Euc d × Euc d, xPhi2 h v σ δ p := by
      rw [hsw] at e1; linear_combination e1
    rw [this]; ring
  have hn : ‖∫ p : Euc d × Euc d, (xPhi2 h v σ δ p - xPhi3 h v σ δ p)‖ ≤
      L * ((d : ℝ) + 2 * σ + 2) * xEprod h σ δ := by
    refine (norm_integral_le_integral_norm _).trans ?_
    have hb := (xe_int (xKer_xK (d := d) (σ := σ) hσ hδ) h).const_mul (L * ((d : ℝ) + 2 * σ + 2))
    unfold xEprod
    rw [← integral_const_mul]
    exact integral_mono_of_nonneg (Eventually.of_forall fun p => norm_nonneg _) hb
      (Eventually.of_forall fun p => xPhi23_norm hL0 hL hσ hδ h p)
  rw [← e2, norm_mul] at hn
  have h2n : ‖(2 : ℂ)‖ = 2 := by simp
  rw [h2n] at hn
  linarith


theorem xsc_core {v : Euc d → Euc d} (hv : XTVF v) {L : ℝ} (hL0 : 0 ≤ L) (hL : XLip v L) {σ δ : ℝ}
    (hσ : 0 < σ) (hδ : 0 < δ) (h : 𝓢(Euc d, ℂ)) :
    ‖∫ ξ, ((xmK (xK d σ δ) ξ : ℝ) : ℂ) * 𝓕 h ξ * 𝓕 (xadv v h) (-ξ)‖ ≤
      ((d : ℝ) + ((d : ℝ) + 2 * σ + 2) / 2) * L * ∫ ξ, xmK (xK d σ δ) ξ * ‖𝓕 h ξ‖ ^ 2 := by
  have hK := xKer_xK (d := d) hσ hδ
  set ψ := xadv v h with hψ
  have e1 := xJ_fourierK hK h ψ
  have e2 := xsc_AB hK h ψ
  have e3 : ∀ y : Euc d, ∫ x, ψ x * ((h x - h y) * ((xK d σ δ (x - y) : ℝ) : ℂ)) =
      -(1 / 2 : ℂ) * ∫ x, (h x - h y) ^ 2 * ((xGy v σ δ y x : ℝ) : ℂ) := fun y =>
    xibp_y hv hL0 hL hσ hδ h y
  have hF : Integrable (fun p => xPhi1 h v σ δ p - xPhi2 h v σ δ p) (volume.prod volume) :=
    (xPhi1_int hv hL0 hL hσ hδ h).sub (xPhi2_int hv hL0 hL hσ hδ h)
  have e4 : ∫ y, ∫ x, (h x - h y) ^ 2 * ((xGy v σ δ y x : ℝ) : ℂ) =
      ∫ p : Euc d × Euc d, (xPhi1 h v σ δ p - xPhi2 h v σ δ p) := by
    have := (integral_prod_symm (μ := (volume : Measure (Euc d))) (ν := (volume : Measure (Euc d)))
      (fun p => xPhi1 h v σ δ p - xPhi2 h v σ δ p) hF).symm
    refine Eq.trans ?_ this
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [xPhi1, xPhi2, xGy_eq]
    push_cast
    ring
  have e5 : ∫ ξ, ((xmK (xK d σ δ) ξ : ℝ) : ℂ) * 𝓕 h ξ * 𝓕 ψ (-ξ) =
      -(1 / 2 : ℂ) * ∫ p : Euc d × Euc d, (xPhi1 h v σ δ p - xPhi2 h v σ δ p) := by
    rw [← e1, e2]
    simp_rw [e3]
    rw [integral_const_mul, e4]
  rw [e5, norm_mul]
  have h1 : ‖-(1 / 2 : ℂ)‖ = 1 / 2 := by simp
  rw [h1]
  have h2 : ∫ p : Euc d × Euc d, (xPhi1 h v σ δ p - xPhi2 h v σ δ p) =
      (∫ p : Euc d × Euc d, xPhi1 h v σ δ p) - ∫ p : Euc d × Euc d, xPhi2 h v σ δ p :=
    integral_sub (xPhi1_int hv hL0 hL hσ hδ h) (xPhi2_int hv hL0 hL hσ hδ h)
  rw [h2]
  have hT1 := xT1 hv hL0 hL hσ hδ h
  have hT2 := xT2 hv hL0 hL hσ hδ h
  have hE : xEprod h σ δ = 2 * ∫ ξ, xmK (xK d σ δ) ξ * ‖𝓕 h ξ‖ ^ 2 := by
    unfold xEprod
    have := (integral_prod_symm (μ := (volume : Measure (Euc d))) (ν := (volume : Measure (Euc d)))
      (fun p : Euc d × Euc d => ‖h p.1 - h p.2‖ ^ 2 * xK d σ δ (p.1 - p.2)) (xe_int hK h))
    refine this.trans ?_
    rw [xE_eq hK h, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
    simp only; ring
  have hn := (norm_sub_le (∫ p : Euc d × Euc d, xPhi1 h v σ δ p) (∫ p : Euc d × Euc d, xPhi2 h v σ δ p))
  have hIn : 0 ≤ ∫ ξ, xmK (xK d σ δ) ξ * ‖𝓕 h ξ‖ ^ 2 :=
    integral_nonneg fun ξ => mul_nonneg (integral_nonneg fun z => mul_nonneg (hK.nonneg z) (xph_nonneg ξ z)) (sq_nonneg _)
  rw [hE] at hT1 hT2
  nlinarith [hT1, hT2, hn]

end HRS.Commutator.Whole.XNRS
