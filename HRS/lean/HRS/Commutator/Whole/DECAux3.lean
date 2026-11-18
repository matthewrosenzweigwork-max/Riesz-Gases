import HRS.Commutator.Whole.DECAux2
import HRS.Commutator.Whole.Local
import HRS.Commutator.Whole.ApproxAux
import HRS.Commutator.Whole.LocalAuxFC2

/-!
# Packet CMX-DEC, helper file 3: the kernels of the decomposition are good

* `ghiForce` (Fourier remainder) with the Lemma 3.1 `L¹` bound, via `cmxSA_core_integrable`;
* `kernGrad` (full kernel), via the `cmxSA_core_m` route of `cmxSA_comm_integrable_meas`;
* `gloForce` against `v_{>1}` (bounded) and against `v` (via the difference of the two above);
* the `pairGen` identity `pairGen K X ρ = N⁻¹ ∑ Φ_K(X_i) - ∫ ρ Φ_K`.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform ContDiff

namespace HRS.Commutator.Whole.DEC

variable {d : ℕ} {s : ℝ}

theorem ghi_measurable (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) :
    Measurable (ghiForce s : Euc d → Euc d) :=
  (cmxSA_kernGrad_measurable s).sub (gloForce_props hd hs0 hsd).1.continuous.measurable

theorem glo_measurable (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) :
    Measurable (gloForce s : Euc d → Euc d) :=
  (gloForce_props hd hs0 hsd).1.continuous.measurable

theorem ghi_odd (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) (z : Euc d) :
    ghiForce s (-z) = -ghiForce s z := by
  unfold ghiForce
  rw [cmxFB_kernGrad_neg, (gloForce_props hd hs0 hsd).2.2.1 z]
  abel

theorem glo_odd (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) (z : Euc d) :
    gloForce s (-z) = -gloForce s z :=
  (gloForce_props hd hs0 hsd).2.2.1 z

theorem kernGrad_odd (s : ℝ) (z : Euc d) : kernGrad s (-z) = -kernGrad s z :=
  cmxFB_kernGrad_neg z

/-- The Fourier remainder kernel is good against `ρ` (Lemma 3.1 `L¹` bound). -/
theorem ghi_good (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) {ρ : Euc d → ℝ}
    (hρ : BddCptDensity ρ) {v : Euc d → Euc d} {L : ℝ≥0} (hv : LipschitzWith L v) :
    DecGood ρ (commKer (ghiForce s) v) := by
  have hρm : Measurable ρ := hρ.measurable
  have hρ1 : Integrable ρ := (energyAux_bddCpt_integrable ρ hρ).1
  obtain ⟨Bρ, hBρ⟩ := hρ.bdd
  have hgm := ghi_measurable hd hs0 hsd
  set h : Euc d → ℝ := fun z => ‖z‖ * ‖ghiForce s z‖ with hh
  have hhm : Measurable h := measurable_norm.mul hgm.norm
  have hh1 : Integrable h := memLp_one_iff_integrable.1 (kernel_remainder_Lp hd hs0 hsd).1
  set m : Euc d → ℝ := fun z => (L : ℝ) * h z with hm
  have hmm : Measurable m := measurable_const.mul hhm
  have hm0 : ∀ z, 0 ≤ m z := fun z => mul_nonneg L.coe_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  have hmint : Integrable m := hh1.const_mul _
  have hmfin : ∫⁻ z, ‖m z‖ₑ < ⊤ := hmint.2
  have hbdρ : ∀ y, ‖ρ y‖ₑ ≤ ENNReal.ofReal Bρ := fun y => by
    rw [← ofReal_norm_eq_enorm]
    exact ENNReal.ofReal_le_ofReal (by rw [Real.norm_eq_abs]; exact hBρ y)
  have hconv : ∀ a, ∫⁻ y, ‖m (a - y)‖ₑ * ‖ρ y‖ₑ ≤
      (∫⁻ z, ‖m z‖ₑ) * ENNReal.ofReal Bρ := by
    intro a
    have hT : ∫⁻ y, ‖m (a - y)‖ₑ = ∫⁻ z, ‖m z‖ₑ :=
      (Measure.measurePreserving_sub_left volume a).lintegral_comp hmm.enorm
    calc ∫⁻ y, ‖m (a - y)‖ₑ * ‖ρ y‖ₑ ≤ ∫⁻ y, ‖m (a - y)‖ₑ * ENNReal.ofReal Bρ :=
          lintegral_mono fun y => by gcongr; exact hbdρ y
      _ = (∫⁻ y, ‖m (a - y)‖ₑ) * ENNReal.ofReal Bρ :=
          lintegral_mul_const' _ _ ENNReal.ofReal_ne_top
      _ = (∫⁻ z, ‖m z‖ₑ) * ENNReal.ofReal Bρ := by rw [hT]
  have hk : Measurable (fun q : Euc d × Euc d => commKer (ghiForce s) v q.1 q.2) :=
    dec_commKer_meas hgm hv.continuous.measurable
  have hbound : ∀ x y, ‖commKer (ghiForce s) v x y‖ ≤
      m (x - y) + 0 + (fun _ : Euc d => (0 : ℝ)) x + (fun _ : Euc d => (0 : ℝ)) y := by
    intro x y
    simp only [add_zero]
    unfold commKer
    by_cases hxy : x = y
    · subst hxy
      simp [m, h]
    · rw [if_neg hxy]
      have h1 : ‖inner ℝ (v x - v y) (ghiForce s (x - y))‖ ≤
          ‖v x - v y‖ * ‖ghiForce s (x - y)‖ := norm_inner_le_norm _ _
      have h2 : ‖v x - v y‖ ≤ (L : ℝ) * ‖x - y‖ := by
        have := hv.dist_le_mul x y
        rwa [dist_eq_norm, dist_eq_norm] at this
      calc ‖inner ℝ (v x - v y) (ghiForce s (x - y))‖
          ≤ ‖v x - v y‖ * ‖ghiForce s (x - y)‖ := h1
        _ ≤ ((L : ℝ) * ‖x - y‖) * ‖ghiForce s (x - y)‖ :=
            mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
        _ = m (x - y) := by simp only [hm, hh]; ring
  have hcore := cmxSA_core_integrable (k := commKer (ghiForce s) v) hk ρ hρm hρ1 m
    (fun _ => 0) hmm hm0 measurable_const (fun _ => le_rfl)
    (by simp) 0 le_rfl ((∫⁻ z, ‖m z‖ₑ) * ENNReal.ofReal Bρ)
    (ENNReal.mul_lt_top hmfin ENNReal.ofReal_lt_top) hconv hbound
  exact ⟨hk, fun x y => dec_commKer_symm (ghi_odd hd hs0 hsd) v x y, hcore.1, hcore.2⟩


/-- The full kernel is good against `ρ` (the `cmxSA_core_m` route, for all `a`). -/
theorem full_good (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) {ρ : Euc d → ℝ}
    (hρ : BddCptDensity ρ) {v : Euc d → Euc d} {L : ℝ≥0} (hv : LipschitzWith L v) :
    DecGood ρ (commKer (kernGrad s) v) := by
  have hpρ : MemLp ρ ⊤ volume := energyAux_memLp_bdd ρ hρ ⊤
  have hp : ENNReal.ofReal ((d : ℝ) / (d - s)) < ⊤ := ENNReal.ofReal_lt_top
  obtain ⟨-, qr, σ, hq, hsσ, hσ0, hσq, hpq⟩ := cmxSA_exponents hd hs0 hsd ⊤ hp
  obtain ⟨B, hB, hconv⟩ := cmxSA_conv_bound (by omega) hσ0.le hq hσq ⊤ hpq ρ hpρ
  have hcore := cmxSA_core_m (k := commKer (kernGrad s) v)
    (cmxSA_commKer_measurable s hv.continuous.measurable) ρ hρ.measurable
    (energyAux_bddCpt_integrable ρ hρ).1
    (fun _ => 0) measurable_const (fun _ => le_rfl) (by simpa using integrable_zero _ _ _)
    L L σ L.coe_nonneg L.coe_nonneg B hB hconv
    (fun x y => by simpa using cmxSA_comm_bound hs0 hσ0 hsσ hv x y)
  exact ⟨cmxSA_commKer_measurable s hv.continuous.measurable,
    fun x y => dec_commKer_symm (kernGrad_odd s) v x y, hcore.1, hcore.2⟩

/-- The bounded kernel `commKer (gloForce s) (v_{>1})` is good against `ρ`. -/
theorem gloPgt_good (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) {ρ : Euc d → ℝ}
    (hρ : BddCptDensity ρ) {v : Euc d → Euc d} {L : ℝ≥0} (hv : LipschitzWith L v) :
    DecGood ρ (commKer (gloForce s) (Pgt 1 v)) := by
  obtain ⟨C, hC, hvh⟩ := vhi_bounded (d := d) hd
  obtain ⟨hcont, -, hbdd⟩ := hvh v L hv
  obtain ⟨Bg, hBg⟩ := (gloForce_props hd hs0 hsd).2.2.2 0
  have hG : ∀ z, ‖gloForce s z‖ ≤ Bg := fun z => by
    have h := hBg z
    rwa [norm_iteratedFDeriv_zero] at h
  have hCL : 0 ≤ C * (L : ℝ) := mul_nonneg hC.le L.coe_nonneg
  have hB0 : 0 ≤ Bg := (norm_nonneg _).trans (hG 0)
  have hbound : ∀ x y, ‖commKer (gloForce s) (Pgt 1 v) x y‖ ≤ 2 * (C * (L : ℝ)) * Bg := by
    intro x y
    unfold commKer
    by_cases hxy : x = y
    · rw [if_pos hxy, norm_zero]
      exact mul_nonneg (mul_nonneg two_pos.le hCL) hB0
    · rw [if_neg hxy]
      have h1 : ‖inner ℝ (Pgt 1 v x - Pgt 1 v y) (gloForce s (x - y))‖ ≤
          ‖Pgt 1 v x - Pgt 1 v y‖ * ‖gloForce s (x - y)‖ := norm_inner_le_norm _ _
      have h2 : ‖Pgt 1 v x - Pgt 1 v y‖ ≤ 2 * (C * (L : ℝ)) :=
        (norm_sub_le _ _).trans (by linarith [hbdd x, hbdd y])
      exact h1.trans (mul_le_mul h2 (hG _) (norm_nonneg _) (mul_nonneg two_pos.le hCL))
  exact dec_good_bdd hρ (dec_commKer_meas (glo_measurable hd hs0 hsd) hcont.measurable)
    (dec_commKer_symm (glo_odd hd hs0 hsd) (Pgt 1 v)) hbound

/-- Splitting of the full commutator kernel into the Fourier remainder and the low-frequency part. -/
theorem kernGrad_split (v : Euc d → Euc d) (x y : Euc d) :
    commKer (kernGrad s) v x y = commKer (ghiForce s) v x y + commKer (gloForce s) v x y := by
  have hk : ∀ z : Euc d, kernGrad s z = ghiForce s z + gloForce s z := fun z => by
    unfold ghiForce; abel
  unfold commKer
  by_cases hxy : x = y
  · simp [hxy]
  · rw [if_neg hxy, if_neg hxy, if_neg hxy, hk (x - y), inner_add_right]

/-- Sup bound on the convolution `(F*σ)(x) = σ.intV (y ↦ F(x-y))`. -/
theorem convForce_bound (σ : SMeas d) [IsFiniteMeasure σ.pos] [IsFiniteMeasure σ.neg]
    {F : Euc d → Euc d} {B : ℝ} (hB : ∀ z, ‖F z‖ ≤ B) (x : Euc d) :
    ‖σ.convForce F x‖ ≤ B * (σ.pos.real Set.univ + σ.neg.real Set.univ) := by
  unfold SMeas.convForce SMeas.intV
  calc ‖(∫ y, F (x - y) ∂σ.pos) - ∫ y, F (x - y) ∂σ.neg‖
      ≤ ‖∫ y, F (x - y) ∂σ.pos‖ + ‖∫ y, F (x - y) ∂σ.neg‖ := norm_sub_le _ _
    _ ≤ B * σ.pos.real Set.univ + B * σ.neg.real Set.univ :=
        add_le_add (norm_integral_le_of_norm_le_const (ae_of_all _ fun y => hB _))
          (norm_integral_le_of_norm_le_const (ae_of_all _ fun y => hB _))
    _ = B * (σ.pos.real Set.univ + σ.neg.real Set.univ) := by ring

/-- The kernel `commKer (gloForce s) v` is good against `ρ` (difference of the full and the Fourier
remainder kernels). -/
theorem glo_good (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) {ρ : Euc d → ℝ}
    (hρ : BddCptDensity ρ) {v : Euc d → Euc d} {L : ℝ≥0} (hv : LipschitzWith L v) :
    DecGood ρ (commKer (gloForce s) v) := by
  have hsplit : ∀ x y, commKer (kernGrad s) v x y =
      commKer (ghiForce s) v x y + commKer (gloForce s) v x y := by
    intro x y
    have hk : ∀ z : Euc d, kernGrad s z = ghiForce s z + gloForce s z := fun z => by
      unfold ghiForce; abel
    unfold commKer
    by_cases hxy : x = y
    · simp [hxy]
    · rw [if_neg hxy, if_neg hxy, if_neg hxy, hk (x - y), inner_add_right]
  exact ((full_good hd hs0 hsd hρ hv).sub (ghi_good hd hs0 hsd hρ hv)).congr'
    (fun x y => by simp only [hsplit x y]; ring)

/-- The kernel `commKer (gloForce s) (v_{≤1})` is good against `ρ`. -/
theorem glo_Pleq_good (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) {ρ : Euc d → ℝ}
    (hρ : BddCptDensity ρ) {v : Euc d → Euc d} {L : ℝ≥0} (hv : LipschitzWith L v) :
    DecGood ρ (commKer (gloForce s) (Pleq 1 v)) :=
  ((glo_good hd hs0 hsd hρ hv).sub (gloPgt_good hd hs0 hsd hρ hv)).congr'
    (fun x y => by simp only [dec_commKer_split (gloForce s) v x y]; ring)

/-- The `pairGen` identity: `pairGen K X ρ = N⁻¹ ∑_i Φ_K(X_i) - ∫ ρ Φ_K` for a good kernel with zero
diagonal. -/
theorem pairGen_formula {ρ : Euc d → ℝ} (hρ : BddCptDensity ρ) {N : ℕ} (hN : 1 ≤ N)
    (X : Fin N → Euc d) {K : Euc d → Euc d → ℝ} (hG : DecGood ρ K)
    (hdiag : ∀ x, K x x = 0) :
    pairGen K X ρ = (1 / (N : ℝ)) * ∑ i, decPhi ρ X K (X i) - ∫ x, ρ x * decPhi ρ X K x := by
  have hi1 : Integrable (fun x => (1 / (N : ℝ)) * ∑ j, K (X j) x * ρ x) := by
    refine Integrable.const_mul ?_ _
    exact integrable_finsetSum _ fun j _ => hG.F1 (X j)
  have hi2 : Integrable (fun x => ∫ y, K x y * ρ x * ρ y) := hG.F2.integral_prod_left
  have hI : ∫ x, ρ x * decPhi ρ X K x =
      (1 / (N : ℝ)) * ∑ j, (∫ y, K (X j) y * ρ y) - ∫ x, ∫ y, K x y * ρ x * ρ y := by
    have e1 : (fun x => ρ x * decPhi ρ X K x) =
        fun x => (1 / (N : ℝ)) * ∑ j, K (X j) x * ρ x - ∫ y, K x y * ρ x * ρ y :=
      funext (decPhi_pt X K hG)
    rw [e1, integral_sub hi1 hi2, integral_const_mul,
      integral_finsetSum _ (fun j _ => hG.F1 (X j))]
  have hE : ∀ i, ∑ j ∈ Finset.univ.erase i, K (X i) (X j) = ∑ j, K (X i) (X j) :=
    fun i => Finset.sum_erase _ (hdiag (X i))
  unfold pairGen
  simp only [hE]
  rw [hI]
  simp only [decPhi, Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring


end HRS.Commutator.Whole.DEC
