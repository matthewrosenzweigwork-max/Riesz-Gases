import HRS.Equilibrium.Parametrix.PX3aAuxX

/-!
# Packet PX3a auxiliaries Y: `newton_doublyCentered` and `newton_linear`
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.Parx

variable {d : ℕ}

theorem px3a_newton_doublyCentered (hd : 2 ≤ d) {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ) {β : ℝ}
    (hβ : 0 < β) {σ : ℝ} (hσ : σ < d) {b m : ℕ} {B : ℝ} {F : Torus d → Torus d → ℝ}
    (hF : Conormal σ b m B F) : PDE.DoublyCentered (withDensityReal ρ) (newtonOp d β ρ F) := by
  have hB := conormalL_B_nonneg hd hF
  have hF0 := conormalL_mono_m (m' := 0) (Nat.zero_le _) hF
  obtain ⟨Cn, hCn0, hCn⟩ := newton_ofChart_general hd (ν := β⁻¹) (inv_pos.mpr hβ) hσ b 0
  have hN := hCn B F hB hF0
  have hN' : Conormal (σ - 2) (b + 1) 0 (Cn * B) (ofChart (newtonChart d β⁻¹ (toChart F))) :=
    conormalL_mono_b (mul_nonneg hCn0 hB) (fun c => by split_ifs <;> omega) hN
  have hdiag : ∀ x, ofChart (newtonChart d β⁻¹ (toChart F)) x x = 0 := fun x => by simp [ofChart]
  exact doublyCentered_cc hd hρ (σ := σ - 2) (by linarith) (b + 1) (mul_nonneg hCn0 hB) hN' hdiag

lemma newtonPot_integrand_int (hd : 2 ≤ d) {σ : ℝ} (hσ : σ < d) {b m : ℕ} {A : ℝ} (hA : 0 ≤ A)
    {g : Euc d × Euc d → ℝ} (h : SrcCls d σ b m A g) {p : Euc d × Euc d} (hp1 : 0 < ‖p.2‖)
    (hp2 : ‖p.2‖ < 1 / 8) : Integrable (fun w => Efund d (p.2 - w) * g (p.1, w)) := by
  set r : ℝ := ‖p.2‖ with hr
  have hρ : 0 < r / 8 := by positivity
  obtain ⟨hLn, hLf, -⟩ := newtonPot_split hd hσ hA h hp1 hp2 (z0 := p.2) rfl (p := p)
    (by rw [sub_self, norm_zero]; positivity) 0
  have hLnw : Integrable (fun w => Ln d 0 (r / 8) (p.2 - w) * g (p.1, w)) := by
    have := hLn.comp_sub_left p.2
    refine this.congr (Eventually.of_forall fun w => ?_)
    simp
  have hgi := h.slice_integrable (by omega) hσ p.1
  have hpt : ∀ w : Euc d, Efund d (p.2 - w) * g (p.1, w) =
      0 * g (p.1, w) + Ln d 0 (r / 8) (p.2 - w) * g (p.1, w) + Lf d 0 (r / 8) (p.2 - w) * g (p.1, w) := by
    intro w
    by_cases hw : 1 / 16 < ‖w‖
    · simp [h.supp p.1 w hw]
    · have hw' : ‖w‖ ≤ 1 / 16 := not_lt.mp hw
      have h1 : px3a_zeta d 1 (p.2 - w) = 1 :=
        px3a_zeta_eq_one one_pos (by have := norm_sub_le p.2 w; linarith)
      simp only [Ln, Lf, h1]
      ring
  exact (((hgi.const_mul 0).add hLnw).add hLf).congr (Eventually.of_forall fun w => (hpt w).symm)

lemma newtonChart_linear (hd : 2 ≤ d) {ν : ℝ} {σ : ℝ} (hσ : σ < d) {b : ℕ} {B B' : ℝ} (hB : 0 ≤ B)
    (hB' : 0 ≤ B') {F G : Torus d → Torus d → ℝ} (hF : Conormal σ b 0 B F) (hG : Conormal σ b 0 B' G)
    (a c : ℝ) (p : Euc d × Euc d) (hp0 : p.2 ≠ 0) :
    newtonChart d ν (toChart (fun x y => a * F x y + c * G x y)) p =
      a * newtonChart d ν (toChart F) p + c * newtonChart d ν (toChart G) p := by
  by_cases h8 : 1 / 16 ≤ ‖p.2‖
  · simp [newtonChart, chi_eq_zero h8]
  · have hp2 : ‖p.2‖ < 1 / 8 := by linarith [not_le.mp h8]
    have hp1 : 0 < ‖p.2‖ := norm_pos_iff.mpr hp0
    obtain ⟨K1, hK1, hsrc⟩ := srcCls_chart (d := d) σ b 0
    have hgF := hsrc B F hB hF
    have hgG := hsrc B' G hB' hG
    have hiF : Integrable (fun w => newtonKernel d ν (p.2 - w) * (chi d w * toChart F (p.1, w))) := by
      refine ((newtonPot_integrand_int hd hσ (mul_nonneg hK1 hB) hgF hp1 hp2).const_mul (1 / (2 * ν))).congr
        (Eventually.of_forall fun w => ?_)
      simp only [newtonKernel_eq]; ring
    have hiG : Integrable (fun w => newtonKernel d ν (p.2 - w) * (chi d w * toChart G (p.1, w))) := by
      refine ((newtonPot_integrand_int hd hσ (mul_nonneg hK1 hB') hgG hp1 hp2).const_mul (1 / (2 * ν))).congr
        (Eventually.of_forall fun w => ?_)
      simp only [newtonKernel_eq]; ring
    unfold newtonChart
    have e : (fun w => newtonKernel d ν (p.2 - w) * (chi d w * toChart (fun x y => a * F x y + c * G x y) (p.1, w))) =
        fun w => a * (newtonKernel d ν (p.2 - w) * (chi d w * toChart F (p.1, w))) +
          c * (newtonKernel d ν (p.2 - w) * (chi d w * toChart G (p.1, w))) := by
      funext w
      simp only [toChart]
      ring
    rw [e, integral_add (hiF.const_mul a) (hiG.const_mul c), integral_const_mul, integral_const_mul]
    ring

lemma ofChart_newtonChart_linear (hd : 2 ≤ d) {ν : ℝ} {σ : ℝ} (hσ : σ < d) {b : ℕ} {B B' : ℝ}
    (hB : 0 ≤ B) (hB' : 0 ≤ B') {F G : Torus d → Torus d → ℝ} (hF : Conormal σ b 0 B F)
    (hG : Conormal σ b 0 B' G) (a c : ℝ) (x y : Torus d) :
    ofChart (newtonChart d ν (toChart (fun x y => a * F x y + c * G x y))) x y =
      a * ofChart (newtonChart d ν (toChart F)) x y + c * ofChart (newtonChart d ν (toChart G)) x y := by
  unfold ofChart
  by_cases hxy : x = y
  · simp [hxy]
  · rw [if_neg hxy, if_neg hxy, if_neg hxy]
    refine newtonChart_linear hd hσ hB hB' hF hG a c _ ?_
    show Torus.centeredRep (x - y) ≠ 0
    intro h0
    apply hxy
    have := px3a_mk_cR (x - y)
    rw [h0, show Torus.mk (0 : Euc d) = 0 from mk_isLat isLat_zero] at this
    exact sub_eq_zero.mp this.symm

lemma canonicalCenter_lin (hd : 2 ≤ d) {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ) {σ : ℝ}
    (hσ : σ < d) (b : ℕ) {B₁ B₂ : ℝ} (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂) {H₁ H₂ : Torus d → Torus d → ℝ}
    (h₁ : Conormal σ b 0 B₁ H₁) (h₂ : Conormal σ b 0 B₂ H₂) (hd₁ : ∀ x, H₁ x x = 0)
    (hd₂ : ∀ x, H₂ x x = 0) (a c : ℝ) (x y : Torus d) :
    canonicalCenter (withDensityReal ρ) (fun x y => a * H₁ x y + c * H₂ x y) x y =
      a * canonicalCenter (withDensityReal ρ) H₁ x y + c * canonicalCenter (withDensityReal ρ) H₂ x y := by
  haveI : IsProbabilityMeasure (withDensityReal ρ) := isProb_withDensityReal hρ.density
  set μ : Measure (Torus d) := withDensityReal ρ with hμ
  obtain ⟨K, hK0, hK⟩ := conormal_row_int hd hρ hσ b
  have hrow₁ : ∀ x', Integrable (fun y' => H₁ x' y') μ := fun x' => (hK B₁ H₁ hB₁ h₁ hd₁ x').1
  have hrow₂ : ∀ x', Integrable (fun y' => H₂ x' y') μ := fun x' => (hK B₂ H₂ hB₂ h₂ hd₂ x').1
  have hcol₁ : ∀ y', Integrable (fun x' => H₁ x' y') μ :=
    fun y' => (hK B₁ (swapK H₁) hB₁ (conormalL_swap h₁) hd₁ y').1
  have hcol₂ : ∀ y', Integrable (fun x' => H₂ x' y') μ :=
    fun y' => (hK B₂ (swapK H₂) hB₂ (conormalL_swap h₂) hd₂ y').1
  have hr₁ : Integrable (fun x' => ∫ y', H₁ x' y' ∂μ) μ :=
    (conormal_prod_int hd hρ hσ b hB₁ h₁ hd₁).integral_prod_left
  have hr₂ : Integrable (fun x' => ∫ y', H₂ x' y' ∂μ) μ :=
    (conormal_prod_int hd hρ hσ b hB₂ h₂ hd₂).integral_prod_left
  have row_lin : ∀ x', ∫ y', (a * H₁ x' y' + c * H₂ x' y') ∂μ =
      a * ∫ y', H₁ x' y' ∂μ + c * ∫ y', H₂ x' y' ∂μ := fun x' => by
    rw [integral_add ((hrow₁ x').const_mul a) ((hrow₂ x').const_mul c), integral_const_mul,
      integral_const_mul]
  have col_lin : ∀ y', ∫ x', (a * H₁ x' y' + c * H₂ x' y') ∂μ =
      a * ∫ x', H₁ x' y' ∂μ + c * ∫ x', H₂ x' y' ∂μ := fun y' => by
    rw [integral_add ((hcol₁ y').const_mul a) ((hcol₂ y').const_mul c), integral_const_mul,
      integral_const_mul]
  have dbl : ∫ x', (∫ y', (a * H₁ x' y' + c * H₂ x' y') ∂μ) ∂μ =
      a * ∫ x', (∫ y', H₁ x' y' ∂μ) ∂μ + c * ∫ x', (∫ y', H₂ x' y' ∂μ) ∂μ := by
    simp_rw [row_lin]
    rw [integral_add (hr₁.const_mul a) (hr₂.const_mul c), integral_const_mul, integral_const_mul]
  simp only [canonicalCenter]
  rw [row_lin x, col_lin y, dbl]
  ring

theorem px3a_newton_linear (hd : 2 ≤ d) {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ) {β : ℝ}
    (hβ : 0 < β) {σ : ℝ} (hσ : σ < d) {b m : ℕ} {B B' : ℝ} {F G : Torus d → Torus d → ℝ}
    (hF : Conormal σ b m B F) (hG : Conormal σ b m B' G) (a c : ℝ) :
    newtonOp d β ρ (fun x y => a * F x y + c * G x y) =
      fun x y => a * newtonOp d β ρ F x y + c * newtonOp d β ρ G x y := by
  have hB := conormalL_B_nonneg hd hF
  have hB' := conormalL_B_nonneg hd hG
  have hF0 := conormalL_mono_m (m' := 0) (Nat.zero_le _) hF
  have hG0 := conormalL_mono_m (m' := 0) (Nat.zero_le _) hG
  obtain ⟨Cn, hCn0, hCn⟩ := newton_ofChart_general hd (ν := β⁻¹) (inv_pos.mpr hβ) hσ b 0
  have hN₁ : Conormal (σ - 2) (b + 1) 0 (Cn * B) (ofChart (newtonChart d β⁻¹ (toChart F))) :=
    conormalL_mono_b (mul_nonneg hCn0 hB) (fun c => by split_ifs <;> omega) (hCn B F hB hF0)
  have hN₂ : Conormal (σ - 2) (b + 1) 0 (Cn * B') (ofChart (newtonChart d β⁻¹ (toChart G))) :=
    conormalL_mono_b (mul_nonneg hCn0 hB') (fun c => by split_ifs <;> omega) (hCn B' G hB' hG0)
  have hdiag : ∀ (K : Torus d → Torus d → ℝ) x, ofChart (newtonChart d β⁻¹ (toChart K)) x x = 0 :=
    fun K x => by simp [ofChart]
  funext x y
  unfold newtonOp
  by_cases hxy : x = y
  · simp [hxy]
  · rw [if_neg hxy, if_neg hxy, if_neg hxy]
    have hlin : ofChart (newtonChart d β⁻¹ (toChart (fun x y => a * F x y + c * G x y))) =
        fun x y => a * ofChart (newtonChart d β⁻¹ (toChart F)) x y +
          c * ofChart (newtonChart d β⁻¹ (toChart G)) x y := by
      funext x' y'
      exact ofChart_newtonChart_linear hd hσ hB hB' hF0 hG0 a c x' y'
    rw [hlin]
    exact canonicalCenter_lin hd hρ (σ := σ - 2) (by linarith) (b + 1) (mul_nonneg hCn0 hB)
      (mul_nonneg hCn0 hB') hN₁ hN₂ (hdiag F) (hdiag G) a c x y

end HRS.Parx

end
