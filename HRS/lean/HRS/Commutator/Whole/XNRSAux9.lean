import HRS.Commutator.Whole.XNRSAux8

/-!
# Packet X-NRS, part 9: integration by parts at fixed `y`

`∫ ψ(x)(h(x)-h(y)) K_δ(x-y) dx = -½ ∫ (h(x)-h(y))² G_y(x) dx`.
-/

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal FourierTransform ContDiff SchwartzMap LineDeriv

noncomputable section

namespace HRS.Commutator.Whole.XNRS

variable {d : ℕ}

lemma xN_le_const {σ δ : ℝ} (hσ : 0 < σ) (hδ : 0 < δ) (z : Euc d) :
    xN d σ δ z ≤ δ ^ (-((d : ℝ) + 2 * σ)) := by
  unfold xN
  have h1 : (δ ^ 2) ^ (-((d : ℝ) + 2 * σ) / 2) = δ ^ (-((d : ℝ) + 2 * σ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hδ.le]; congr 1; push_cast; ring
  rw [← h1]
  apply Real.rpow_le_rpow_of_nonpos (by positivity) (by nlinarith [sq_nonneg ‖z‖])
  have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  linarith

lemma xNt_le_const {σ δ : ℝ} (hσ : 0 < σ) (hδ : 0 < δ) (z : Euc d) :
    ‖z‖ * xP d σ δ z ≤ δ ^ (-((d : ℝ) + 2 * σ + 1)) := by
  have hb : 0 < ‖z‖ ^ 2 + δ ^ 2 := by positivity
  have e1 : ‖z‖ * xP d σ δ z ≤ (‖z‖ ^ 2 + δ ^ 2) ^ (-((d : ℝ) + 2 * σ + 1) / 2) := by
    unfold xP
    have e2 : (‖z‖ ^ 2 + δ ^ 2) ^ (-((d : ℝ) + 2 * σ) / 2 - 1) *
        (‖z‖ ^ 2 + δ ^ 2) ^ ((1 : ℝ) / 2) = (‖z‖ ^ 2 + δ ^ 2) ^ (-((d : ℝ) + 2 * σ + 1) / 2) := by
      rw [← Real.rpow_add hb]; congr 1; ring
    have e3 : ‖z‖ ≤ (‖z‖ ^ 2 + δ ^ 2) ^ ((1 : ℝ) / 2) := by
      rw [← Real.sqrt_eq_rpow]
      exact Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg δ])
    rw [← e2, mul_comm]
    exact mul_le_mul_of_nonneg_left e3 (Real.rpow_nonneg hb.le _)
  refine e1.trans ?_
  have h1 : (δ ^ 2) ^ (-((d : ℝ) + 2 * σ + 1) / 2) = δ ^ (-((d : ℝ) + 2 * σ + 1)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hδ.le]; congr 1; push_cast; ring
  rw [← h1]
  apply Real.rpow_le_rpow_of_nonpos (by positivity) (by nlinarith [sq_nonneg ‖z‖])
  have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  linarith

lemma xint_schw_lin (f : 𝓢(Euc d, ℂ)) {g : Euc d → ℂ} (hg : AEStronglyMeasurable g volume) (A B : ℝ)
    (hb : ∀ x, ‖g x‖ ≤ A + B * ‖x‖) : Integrable (fun x => f x * g x) := by
  have h1 : Integrable (fun x : Euc d => A * ‖f x‖ + B * (‖x‖ ^ 1 * ‖f x‖)) :=
    (f.integrable.norm.const_mul A).add ((f.integrable_pow_mul volume 1).const_mul B)
  refine h1.mono' (f.continuous.aestronglyMeasurable.mul hg) (Eventually.of_forall fun x => ?_)
  rw [norm_mul]
  calc ‖f x‖ * ‖g x‖ ≤ ‖f x‖ * (A + B * ‖x‖) := mul_le_mul_of_nonneg_left (hb x) (norm_nonneg _)
    _ = A * ‖f x‖ + B * (‖x‖ ^ 1 * ‖f x‖) := by ring

lemma xint_schw_bdd (f : 𝓢(Euc d, ℂ)) {g : Euc d → ℂ} (hg : AEStronglyMeasurable g volume) (A : ℝ)
    (hb : ∀ x, ‖g x‖ ≤ A) : Integrable (fun x => f x * g x) :=
  xint_schw_lin f hg A 0 (fun x => by simpa using hb x)


lemma continuous_xQ {σ δ : ℝ} (hδ : 0 < δ) : Continuous (xQ d σ δ) := by
  unfold xQ
  exact (continuous_xPhi hδ).mul (((continuous_const.mul (continuous_xP σ δ hδ)).add
    ((continuous_const.mul (continuous_xPhi hδ)).mul (continuous_xN σ δ hδ))))

lemma continuous_xK {σ δ : ℝ} (hδ : 0 < δ) : Continuous (xK d σ δ) :=
  (continuous_xN σ δ hδ).mul (continuous_xPhi hδ)

lemma xtvf_continuous {v : Euc d → Euc d} (hv : XTVF v) (c : Fin d) :
    Continuous (fun x => v x c) := (hv c).1.continuous

lemma continuous_xg {v : Euc d → Euc d} (hv : XTVF v) {σ δ : ℝ} (hδ : 0 < δ) (y : Euc d) (c : Fin d) :
    Continuous (xg v σ δ y c) := by
  unfold xg
  exact (xtvf_continuous hv c).mul ((continuous_xK hδ).comp (continuous_id.sub continuous_const))

lemma continuous_xg' {v : Euc d → Euc d} (hv : XTVF v) {σ δ : ℝ} (hδ : 0 < δ) (y : Euc d)
    (c : Fin d) : Continuous (xg' v σ δ y c) := by
  unfold xg'
  have hw : Continuous (xw v c c) := (xtg_xw hv c c).1.continuous
  refine (hw.mul ((continuous_xK hδ).comp (continuous_id.sub continuous_const))).sub
    ((xtvf_continuous hv c).mul ?_)
  refine Continuous.mul ?_ ((continuous_xQ hδ).comp (continuous_id.sub continuous_const))
  exact (by fun_prop : Continuous fun x : Euc d => (x - y) c)

lemma xg_bdd {v : Euc d → Euc d} {L : ℝ} (hL0 : 0 ≤ L) (hL : XLip v L) {σ δ : ℝ} (hσ : 0 < σ)
    (hδ : 0 < δ) (y : Euc d) (c : Fin d) (x : Euc d) :
    |xg v σ δ y c x| ≤ ((‖v 0‖ + L * ‖y‖) + L * (2 * Real.sqrt δ)⁻¹) * δ ^ (-((d : ℝ) + 2 * σ)) := by
  refine (xg_bound hL0 hL hσ hδ y c x).trans ?_
  exact mul_le_mul_of_nonneg_left (xN_le_const hσ hδ _) (by positivity)

lemma xg'_bdd {v : Euc d → Euc d} (hv : XTVF v) {L : ℝ} (hL0 : 0 ≤ L) (hL : XLip v L) {σ δ : ℝ}
    (hσ : 0 < σ) (hδ : 0 < δ) (y : Euc d) (c : Fin d) (x : Euc d) :
    |xg' v σ δ y c x| ≤
      (L + (‖v 0‖ + L * ‖y‖) * Real.sqrt δ + L * ((d : ℝ) + 2 * σ + 2)) * δ ^ (-((d : ℝ) + 2 * σ)) +
      ((‖v 0‖ + L * ‖y‖) * ((d : ℝ) + 2 * σ)) * δ ^ (-((d : ℝ) + 2 * σ + 1)) := by
  refine (xg'_bound hv hL0 hL hσ hδ y c x).trans ?_
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have h1 := xN_le_const (d := d) hσ hδ (x - y)
  have h2 := xNt_le_const (d := d) hσ hδ (x - y)
  have ha : 0 ≤ ‖v 0‖ + L * ‖y‖ := by positivity
  gcongr


lemma xgC_int {v : Euc d → Euc d} (hv : XTVF v) {L : ℝ} (hL0 : 0 ≤ L) (hL : XLip v L) {σ δ : ℝ}
    (hσ : 0 < σ) (hδ : 0 < δ) (y : Euc d) (c : Fin d) :
    Integrable (fun x => ((xg v σ δ y c x : ℝ) : ℂ)) := by
  refine xint_dom (Complex.continuous_ofReal.comp (continuous_xg hv hδ y c)).aestronglyMeasurable
    hσ hδ y (((‖v 0‖ + L * ‖y‖) + L * (2 * Real.sqrt δ)⁻¹)) 0 fun x => ?_
  rw [Complex.norm_real, Real.norm_eq_abs]
  simpa using xg_bound hL0 hL hσ hδ y c x

lemma xg'C_int {v : Euc d → Euc d} (hv : XTVF v) {L : ℝ} (hL0 : 0 ≤ L) (hL : XLip v L) {σ δ : ℝ}
    (hσ : 0 < σ) (hδ : 0 < δ) (y : Euc d) (c : Fin d) :
    Integrable (fun x => ((xg' v σ δ y c x : ℝ) : ℂ)) := by
  refine xint_dom (Complex.continuous_ofReal.comp (continuous_xg' hv hδ y c)).aestronglyMeasurable
    hσ hδ y (L + (‖v 0‖ + L * ‖y‖) * Real.sqrt δ + L * ((d : ℝ) + 2 * σ + 2))
    (((‖v 0‖ + L * ‖y‖) * ((d : ℝ) + 2 * σ))) fun x => ?_
  rw [Complex.norm_real, Real.norm_eq_abs]
  exact xg'_bound hv hL0 hL hσ hδ y c x

lemma xGyC_int {v : Euc d → Euc d} (hv : XTVF v) {L : ℝ} (hL0 : 0 ≤ L) (hL : XLip v L) {σ δ : ℝ}
    (hσ : 0 < σ) (hδ : 0 < δ) (y : Euc d) :
    Integrable (fun x => ((xGy v σ δ y x : ℝ) : ℂ)) := by
  have : (fun x => ((xGy v σ δ y x : ℝ) : ℂ)) = fun x => ∑ c, ((xg' v σ δ y c x : ℝ) : ℂ) := by
    funext x; simp [xGy]
  rw [this]
  exact integrable_finsetSum _ fun c _ => xg'C_int hv hL0 hL hσ hδ y c

lemma hasLineDerivAt_xgC {v : Euc d → Euc d} (hv : XTVF v) {σ δ : ℝ} (hδ : 0 < δ) (y : Euc d)
    (c : Fin d) (x : Euc d) :
    HasLineDerivAt ℝ (fun x => ((xg v σ δ y c x : ℝ) : ℂ)) (((xg' v σ δ y c x : ℝ) : ℂ)) x (xe c) := by
  have h := (hasFDerivAt_xgC (σ := σ) hv hδ y c x).hasLineDerivAt (xe c)
  have hval : (((xg' v σ δ y c x : ℝ) : ℂ)) = (Complex.ofRealCLM.comp ((v x c) •
      ((-xQ d σ δ (x - y)) • innerSL ℝ (x - y)) +
        xK d σ δ (x - y) • fderiv ℝ (fun x : Euc d => v x c) x)) (xe c) := by
    rw [xg'_eq_fderiv hv y c x]; rfl
  rw [hval]
  exact h

/-- the flux of `v K_δ(·-y)` vanishes. -/
lemma xflux {v : Euc d → Euc d} (hv : XTVF v) {L : ℝ} (hL0 : 0 ≤ L) (hL : XLip v L) {σ δ : ℝ}
    (hσ : 0 < σ) (hδ : 0 < δ) (y : Euc d) (c : Fin d) :
    ∫ x, ((xg' v σ δ y c x : ℝ) : ℂ) = 0 := by
  have h := integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable
    (μ := (volume : Measure (Euc d))) (v := xe c) (B := ContinuousLinearMap.mul ℝ ℂ)
    (f := fun _ => (1 : ℂ)) (f' := fun _ => (0 : ℂ))
    (g := fun x => ((xg v σ δ y c x : ℝ) : ℂ)) (g' := fun x => ((xg' v σ δ y c x : ℝ) : ℂ))
    (by simpa using (integrable_zero (Euc d) ℂ volume))
    (by simpa using xg'C_int hv hL0 hL hσ hδ y c)
    (by simpa using xgC_int hv hL0 hL hσ hδ y c)
    (fun x _ => by simpa using (hasFDerivAt_const (1 : ℂ) x).hasLineDerivAt (xe c))
    (fun x _ => hasLineDerivAt_xgC hv hδ y c x)
  simpa using h


lemma xhbdd (h : 𝓢(Euc d, ℂ)) : ∃ M : ℝ, 0 ≤ M ∧ ∀ x, ‖h x‖ ≤ M := by
  refine ⟨SchwartzMap.seminorm ℝ 0 0 h, by positivity, fun x => ?_⟩
  simpa using SchwartzMap.le_seminorm ℝ 0 0 h x

theorem xibp_y {v : Euc d → Euc d} (hv : XTVF v) {L : ℝ} (hL0 : 0 ≤ L) (hL : XLip v L) {σ δ : ℝ}
    (hσ : 0 < σ) (hδ : 0 < δ) (h : 𝓢(Euc d, ℂ)) (y : Euc d) :
    ∫ x, xadv v h x * ((h x - h y) * ((xK d σ δ (x - y) : ℝ) : ℂ)) =
      -(1 / 2 : ℂ) * ∫ x, (h x - h y) ^ 2 * ((xGy v σ δ y x : ℝ) : ℂ) := by
  obtain ⟨M, hM0, hM⟩ := xhbdd h
  set ft : Euc d → ℂ := fun x => h x * (h x - 2 * h y) with hft
  set ft' : Fin d → Euc d → ℂ := fun c x => 2 * (h x - h y) * xdr c h x with hft'
  set gC : Fin d → Euc d → ℂ := fun c x => ((xg v σ δ y c x : ℝ) : ℂ) with hgC
  set g'C : Fin d → Euc d → ℂ := fun c x => ((xg' v σ δ y c x : ℝ) : ℂ) with hg'C
  -- derivative of ft
  have hdft : ∀ c x, HasLineDerivAt ℝ ft (ft' c x) x (xe c) := by
    intro c x
    have hh : HasFDerivAt (fun x => h x) (fderiv ℝ h x) x := h.differentiableAt.hasFDerivAt
    have h2 : HasFDerivAt (fun x => h x * (h x - 2 * h y))
        (h x • (fderiv ℝ h x) + (h x - 2 * h y) • (fderiv ℝ h x)) x := by
      exact hh.mul (hh.sub_const (2 * h y))
    have h3 := h2.hasLineDerivAt (xe c)
    have hval : ft' c x = (h x • (fderiv ℝ h x) + (h x - 2 * h y) • (fderiv ℝ h x)) (xe c) := by
      simp only [hft', ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
      rw [xdr_apply, h.differentiableAt.lineDeriv_eq_fderiv]
      ring
    rw [hval]
    exact h3
  -- bounds
  set Cg : ℝ := ((‖v 0‖ + L * ‖y‖) + L * (2 * Real.sqrt δ)⁻¹) * δ ^ (-((d : ℝ) + 2 * σ)) with hCg
  set Cg' : ℝ := (L + (‖v 0‖ + L * ‖y‖) * Real.sqrt δ + L * ((d : ℝ) + 2 * σ + 2)) *
      δ ^ (-((d : ℝ) + 2 * σ)) +
      ((‖v 0‖ + L * ‖y‖) * ((d : ℝ) + 2 * σ)) * δ ^ (-((d : ℝ) + 2 * σ + 1)) with hCg'
  have hgb : ∀ c x, ‖gC c x‖ ≤ Cg := fun c x => by
    simp only [hgC, Complex.norm_real, Real.norm_eq_abs]; exact xg_bdd hL0 hL hσ hδ y c x
  have hg'b : ∀ c x, ‖g'C c x‖ ≤ Cg' := fun c x => by
    simp only [hg'C, Complex.norm_real, Real.norm_eq_abs]; exact xg'_bdd hv hL0 hL hσ hδ y c x
  have hgm : ∀ c, Continuous (gC c) := fun c =>
    Complex.continuous_ofReal.comp (continuous_xg hv hδ y c)
  have hg'm : ∀ c, Continuous (g'C c) := fun c =>
    Complex.continuous_ofReal.comp (continuous_xg' hv hδ y c)
  -- integrability
  have ha : ∀ c, Integrable (fun x => ft' c x * gC c x) := by
    intro c
    have := xint_schw_bdd (xdr c h) (g := fun x => 2 * (h x - h y) * gC c x)
      ((continuous_const.mul (h.continuous.sub continuous_const)).mul (hgm c)).aestronglyMeasurable
      (2 * (M + ‖h y‖) * Cg) (fun x => by
        rw [norm_mul, norm_mul]
        have h1 : ‖(2 : ℂ)‖ = 2 := by simp
        have h2 : ‖h x - h y‖ ≤ M + ‖h y‖ := (norm_sub_le _ _).trans (by linarith [hM x])
        rw [h1]
        have h3 := hgb c x
        have : 0 ≤ ‖h x - h y‖ := norm_nonneg _
        have : 0 ≤ ‖gC c x‖ := norm_nonneg _
        nlinarith [norm_nonneg (h y)])
    refine this.congr (Eventually.of_forall fun x => ?_)
    simp only [hft']; ring
  have hb : ∀ c, Integrable (fun x => ft x * g'C c x) := by
    intro c
    have := xint_schw_bdd h (g := fun x => (h x - 2 * h y) * g'C c x)
      ((h.continuous.sub continuous_const).mul (hg'm c)).aestronglyMeasurable
      ((M + 2 * ‖h y‖) * Cg') (fun x => by
        rw [norm_mul]
        have h2 : ‖h x - 2 * h y‖ ≤ M + 2 * ‖h y‖ := by
          refine (norm_sub_le _ _).trans ?_
          have : ‖(2 : ℂ) * h y‖ = 2 * ‖h y‖ := by rw [norm_mul]; simp
          rw [this]; linarith [hM x]
        have h3 := hg'b c x
        exact mul_le_mul h2 h3 (norm_nonneg _) (by positivity))
    refine this.congr (Eventually.of_forall fun x => ?_)
    simp only [hft]; ring
  have hc : ∀ c, Integrable (fun x => ft x * gC c x) := by
    intro c
    have := xint_schw_bdd h (g := fun x => (h x - 2 * h y) * gC c x)
      ((h.continuous.sub continuous_const).mul (hgm c)).aestronglyMeasurable
      ((M + 2 * ‖h y‖) * Cg) (fun x => by
        rw [norm_mul]
        have h2 : ‖h x - 2 * h y‖ ≤ M + 2 * ‖h y‖ := by
          refine (norm_sub_le _ _).trans ?_
          have : ‖(2 : ℂ) * h y‖ = 2 * ‖h y‖ := by rw [norm_mul]; simp
          rw [this]; linarith [hM x]
        have h3 := hgb c x
        exact mul_le_mul h2 h3 (norm_nonneg _) (by positivity))
    refine this.congr (Eventually.of_forall fun x => ?_)
    simp only [hft]; ring
  -- integration by parts for each c
  have key : ∀ c, ∫ x, ft' c x * gC c x = -∫ x, ft x * g'C c x := by
    intro c
    have := integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable
      (μ := (volume : Measure (Euc d))) (v := xe c) (B := ContinuousLinearMap.mul ℝ ℂ)
      (f := ft) (f' := ft' c) (g := gC c) (g' := g'C c) (ha c) (hb c) (hc c)
      (fun x _ => hdft c x) (fun x _ => hasLineDerivAt_xgC hv hδ y c x)
    simp only [ContinuousLinearMap.mul_apply'] at this
    rw [this, neg_neg]
  have hsum : ∀ x, xadv v h x * ((h x - h y) * ((xK d σ δ (x - y) : ℝ) : ℂ)) =
      (1 / 2 : ℂ) * ∑ c, ft' c x * gC c x := by
    intro x
    rw [xadv_apply hv, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    simp only [hft', hgC, xg]
    push_cast
    ring
  have hG : ∀ x, ∑ c, ft x * g'C c x = ft x * ((xGy v σ δ y x : ℝ) : ℂ) := by
    intro x
    rw [← Finset.mul_sum]
    simp [xGy, hg'C]
  have hGint : Integrable (fun x => ((xGy v σ δ y x : ℝ) : ℂ)) :=
    xGyC_int hv hL0 hL hσ hδ y
  have hflux : ∫ x, ((xGy v σ δ y x : ℝ) : ℂ) = 0 := by
    have : (fun x => ((xGy v σ δ y x : ℝ) : ℂ)) = fun x => ∑ c, g'C c x := by
      funext x; simp [xGy, hg'C]
    rw [this, integral_finsetSum _ (fun c _ => xg'C_int hv hL0 hL hσ hδ y c)]
    exact Finset.sum_eq_zero fun c _ => xflux hv hL0 hL hσ hδ y c
  have hΘint : Integrable (fun x => (h x - h y) ^ 2 * ((xGy v σ δ y x : ℝ) : ℂ)) := by
    refine hGint.bdd_mul (c := (M + ‖h y‖) ^ 2) ?_ (Eventually.of_forall fun x => ?_)
    · exact ((h.continuous.sub continuous_const).pow 2).aestronglyMeasurable
    · rw [norm_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) ((norm_sub_le _ _).trans (by linarith [hM x])) 2
  have hft_eq : ∀ x, ft x * ((xGy v σ δ y x : ℝ) : ℂ) =
      (h x - h y) ^ 2 * ((xGy v σ δ y x : ℝ) : ℂ) - (h y) ^ 2 * ((xGy v σ δ y x : ℝ) : ℂ) := by
    intro x; simp only [hft]; ring
  simp_rw [hsum]
  rw [integral_const_mul, integral_finsetSum _ (fun c _ => ha c)]
  simp_rw [key]
  rw [Finset.sum_neg_distrib, ← neg_mul_eq_mul_neg]
  rw [show (-(1 / 2 : ℂ) * ∫ x, (h x - h y) ^ 2 * ((xGy v σ δ y x : ℝ) : ℂ)) =
      (1 / 2 : ℂ) * (-∫ x, (h x - h y) ^ 2 * ((xGy v σ δ y x : ℝ) : ℂ)) by ring]
  congr 1
  congr 1
  rw [← integral_finsetSum _ (fun c _ => hb c)]
  simp_rw [hG, hft_eq]
  rw [integral_sub hΘint (hGint.const_mul _), integral_const_mul, hflux]
  simp

end HRS.Commutator.Whole.XNRS
