import HRS.Uniform.Q12P3

/-!
# Q12, Peyre part 4: Taylor remainder and the abstract consistency lemma of one Euler step
-/

noncomputable section

open HRS MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

namespace HRS.Uniform.Q12

variable {d : ℕ}

lemma q12_taylor {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {Φ : X → ℝ}
    (hΦ : ContDiff ℝ 2 Φ) {B : ℝ} (hB : ∀ y, ‖fderiv ℝ (fderiv ℝ Φ) y‖ ≤ B) (y h : X) :
    |Φ (y + h) - Φ y - fderiv ℝ Φ y h| ≤ B * ‖h‖ ^ 2 := by
  have hΦ1 : ContDiff ℝ 1 (fderiv ℝ Φ) := hΦ.fderiv_right (by norm_num)
  have hdd : Differentiable ℝ (fderiv ℝ Φ) := hΦ1.differentiable one_ne_zero
  have hd : Differentiable ℝ Φ := hΦ.differentiable (by norm_num)
  have hlip : ∀ x : X, ‖fderiv ℝ Φ x - fderiv ℝ Φ y‖ ≤ B * ‖x - y‖ := fun x => by
    have := (convex_univ (𝕜 := ℝ) (E := X)).norm_image_sub_le_of_norm_fderiv_le
      (f := fderiv ℝ Φ) (C := B) (fun z _ => hdd z) (fun z _ => hB z) (mem_univ y) (mem_univ x)
    exact this
  have hcl : ∀ x ∈ Metric.closedBall y ‖h‖, ‖fderiv ℝ Φ x - fderiv ℝ Φ y‖ ≤ B * ‖h‖ := by
    intro x hx
    have hB0 : 0 ≤ B := le_trans (norm_nonneg (fderiv ℝ (fderiv ℝ Φ) y)) (hB y)
    refine (hlip x).trans (mul_le_mul_of_nonneg_left ?_ hB0)
    simpa [dist_eq_norm] using hx
  have := (convex_closedBall y ‖h‖).norm_image_sub_le_of_norm_hasFDerivWithin_le'
    (f := Φ) (f' := fderiv ℝ Φ) (φ := fderiv ℝ Φ y) (C := B * ‖h‖)
    (fun x _ => (hd x).hasFDerivAt.hasFDerivWithinAt) hcl
    (Metric.mem_closedBall_self (norm_nonneg h))
    (show y + h ∈ Metric.closedBall y ‖h‖ by simp [Metric.mem_closedBall, dist_eq_norm])
  simp only [add_sub_cancel_left] at this
  rw [Real.norm_eq_abs] at this
  calc _ ≤ B * ‖h‖ * ‖h‖ := this
    _ = _ := by ring

lemma q12_per_fderiv {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {Φ : Euc d → X}
    (hΦ : Torus.Per Φ) (y : Euc d) (n : Lattice d) :
    fderiv ℝ Φ (y + Lattice.toEuc n) = fderiv ℝ Φ y := by
  have e : (fun z => Φ (z + Lattice.toEuc n)) = Φ := funext fun z => hΦ z n
  have := fderiv_comp_add_right (𝕜 := ℝ) (f := Φ) (x := y) (Lattice.toEuc n)
  rw [e] at this
  exact this.symm

lemma q12_per_fderiv_apply {Φ : Euc d → ℝ} {w : Euc d → Euc d} (hΦ : Torus.Per Φ) (hw : Torus.Per w) :
    Torus.Per (fun y => fderiv ℝ Φ y (w y)) := by
  intro y n
  show fderiv ℝ Φ (y + Lattice.toEuc n) (w (y + Lattice.toEuc n)) = fderiv ℝ Φ y (w y)
  rw [q12_per_fderiv hΦ, hw]

/-- Consistency of one Euler step in the weak norm. -/
lemma q12_consistency {μa μb : Measure (Torus d)} [IsProbabilityMeasure μa] {τ δ V : ℝ}
    (hτ : 0 ≤ τ) {w : Euc d → Euc d} (hwp : Torus.Per w) (hwc : Continuous w)
    (hV : ∀ y, ‖w y‖ ≤ V)
    (hCE : ∀ (Φ : Euc d → ℝ) (B : ℝ), Torus.Per Φ → C2b B Φ →
      |τ * ∫ x, fderiv ℝ Φ (Torus.rep x) (w (Torus.rep x)) ∂μa + (Iw μa Φ - Iw μb Φ)| ≤ δ * B) :
    WeakClose (μa.map (torusMap (fun y => y + τ • w y))) μb (δ + τ ^ 2 * V ^ 2) := by
  intro Φ B hΦp hC
  have hT := q12_perEquiv_shift hwp τ
  have hcT : Continuous (fun y : Euc d => y + τ • w y) := continuous_id.add (hwc.const_smul τ)
  have hΦc : Continuous Φ := hC.1.continuous
  rw [q12_Iw_map hT hcT μa hΦp hΦc]
  have hB0 : 0 ≤ B := le_trans (abs_nonneg _) (hC.2 0).1
  have hV0 : 0 ≤ V := le_trans (norm_nonneg _) (hV 0)
  have hDc : Continuous fun y => fderiv ℝ Φ y (w y) :=
    ((hC.1.continuous_fderiv (by norm_num)).clm_apply hwc)
  have hper2 : Torus.Per (fun y => Φ (y + τ • w y) - Φ y - τ * fderiv ℝ Φ y (w y)) := by
    intro y n
    show Φ (y + Lattice.toEuc n + τ • w (y + Lattice.toEuc n)) - Φ (y + Lattice.toEuc n) -
      τ * fderiv ℝ Φ (y + Lattice.toEuc n) (w (y + Lattice.toEuc n)) =
      Φ (y + τ • w y) - Φ y - τ * fderiv ℝ Φ y (w y)
    rw [hwp, q12_per_fderiv hΦp, hΦp y n]
    have := q12_perEquiv_per_comp hT hΦp y n
    simp only at this
    rw [hwp] at this
    rw [show y + Lattice.toEuc n + τ • w y = (y + τ • w y) + Lattice.toEuc n by abel, hΦp]
  have hc2 : Continuous fun y => Φ (y + τ • w y) - Φ y - τ * fderiv ℝ Φ y (w y) :=
    (hΦc.comp hcT).sub hΦc |>.sub (continuous_const.mul hDc)
  have hint1 : Integrable (fun x : Torus d => Φ (Torus.rep x + τ • w (Torus.rep x)) - Φ (Torus.rep x)
      - τ * fderiv ℝ Φ (Torus.rep x) (w (Torus.rep x))) μa :=
    (Torus.continuous_descend hper2 hc2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hint2 : Integrable (fun x : Torus d => fderiv ℝ Φ (Torus.rep x) (w (Torus.rep x))) μa :=
    (Torus.continuous_descend (q12_per_fderiv_apply hΦp hwp) hDc).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hint3 : Integrable (fun x : Torus d => Φ (Torus.rep x)) μa :=
    (Torus.continuous_descend hΦp hΦc).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hrem : ∀ y, |Φ (y + τ • w y) - Φ y - τ * fderiv ℝ Φ y (w y)| ≤ B * (τ ^ 2 * V ^ 2) := by
    intro y
    have h := q12_taylor hC.1 (fun z => (hC.2 z).2.2) y (τ • w y)
    simp only [map_smul, smul_eq_mul] at h
    refine h.trans (mul_le_mul_of_nonneg_left ?_ hB0)
    rw [norm_smul, Real.norm_of_nonneg hτ, mul_pow]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hV y) 2) (sq_nonneg τ)
  have hdec : Iw μa (fun y => Φ (y + τ • w y)) - Iw μb Φ =
      (∫ x, (Φ (Torus.rep x + τ • w (Torus.rep x)) - Φ (Torus.rep x) -
        τ * fderiv ℝ Φ (Torus.rep x) (w (Torus.rep x))) ∂μa) +
      (τ * ∫ x, fderiv ℝ Φ (Torus.rep x) (w (Torus.rep x)) ∂μa + (Iw μa Φ - Iw μb Φ)) := by
    have e1 : ∫ x, (Φ (Torus.rep x + τ • w (Torus.rep x)) - Φ (Torus.rep x) -
        τ * fderiv ℝ Φ (Torus.rep x) (w (Torus.rep x))) ∂μa =
        Iw μa (fun y => Φ (y + τ • w y)) - Iw μa Φ - τ * ∫ x, fderiv ℝ Φ (Torus.rep x) (w (Torus.rep x)) ∂μa := by
      have hi0 : Integrable (fun x : Torus d => Φ (Torus.rep x + τ • w (Torus.rep x))) μa := by
        have := hint1.add (hint3.add (hint2.const_mul τ))
        refine this.congr (Filter.Eventually.of_forall fun x => ?_)
        simp only [Pi.add_apply]; ring
      have hia : Integrable (fun x : Torus d => Φ (Torus.rep x + τ • w (Torus.rep x)) - Φ (Torus.rep x)) μa :=
        hi0.sub hint3
      have hib : Integrable (fun x : Torus d => τ * fderiv ℝ Φ (Torus.rep x) (w (Torus.rep x))) μa :=
        hint2.const_mul τ
      rw [integral_sub hia hib, integral_sub hi0 hint3, integral_const_mul]
      rfl
    rw [e1]; ring
  rw [hdec]
  have hb1 : |∫ x, (Φ (Torus.rep x + τ • w (Torus.rep x)) - Φ (Torus.rep x) -
      τ * fderiv ℝ Φ (Torus.rep x) (w (Torus.rep x))) ∂μa| ≤ B * (τ ^ 2 * V ^ 2) := by
    rw [← Real.norm_eq_abs]
    refine (norm_integral_le_of_norm_le_const (C := B * (τ ^ 2 * V ^ 2))
      (Filter.Eventually.of_forall fun x => ?_)).trans ?_
    · rw [Real.norm_eq_abs]; exact hrem _
    · simp
  have hb2 := hCE Φ B hΦp hC
  calc _ ≤ _ := abs_add_le _ _
    _ ≤ B * (τ ^ 2 * V ^ 2) + δ * B := add_le_add hb1 hb2
    _ = _ := by ring

end HRS.Uniform.Q12
