import HRS.Whole.Basic

/-!
# C8 (part 1): rapid decay, singular-kernel potential bounds, smoothness of convolutions with `L¹_loc` kernels

Pure analysis on `ℝ^d` (no thermal input).  Namespace `HRS.MS.LogReg`, helper prefix `lreg_`.

* `lreg_RDec F`: `‖F x‖ ≤ C_N (1+‖x‖)^{-N}` for every `N`; `lreg_phi` is the weight `(1+‖x‖)^{-(d+1)}`.
* `lreg_K` / `lreg_integrable_B`: for `0 ≤ σ < d`, `∫ ‖z‖^{-σ} φ(x - z) dz ≤ A` uniformly in `x`
  (the kernel is locally integrable because `σ < d`; it is bounded by `1` off the unit ball).
* `lreg_conv_smooth`: if `κ` is a kernel with `‖κ z‖ ≤ ‖z‖^{-σ}` (`σ < d`) and `F ∈ C^m` has rapidly decaying
  derivatives up to order `m`, then `x ↦ ∫ B (κ z) (F (x - z)) dz` is `C^m` with the norm bound
  `‖D^m‖ ≤ ‖B‖ C A` whenever `‖D^m F‖ ≤ C φ`.  (Derivatives fall on the smooth factor `F`, differentiation under
  the integral sign by dominated convergence.)
-/

open MeasureTheory Filter Topology Metric
open scoped ContDiff

noncomputable section

namespace HRS.MS.LogReg

open HRS HRS.Whole

variable {d : ℕ}

/-- Rapid decay of a (vector valued) function on `ℝ^d`. -/
def lreg_RDec {G : Type*} [NormedAddCommGroup G] (F : Euc d → G) : Prop :=
  ∀ N : ℕ, ∃ C : ℝ, ∀ x, (1 + ‖x‖) ^ N * ‖F x‖ ≤ C

/-- The weight `(1+‖x‖)^{-(d+1)}`. -/
def lreg_phi (d : ℕ) (x : Euc d) : ℝ := ((1 + ‖x‖) ^ (d + 1))⁻¹

lemma lreg_phi_pos (x : Euc d) : 0 < lreg_phi d x := by
  unfold lreg_phi; positivity

lemma lreg_phi_le_one (x : Euc d) : lreg_phi d x ≤ 1 := by
  unfold lreg_phi
  refine inv_le_one_of_one_le₀ ?_
  exact one_le_pow₀ (by linarith [norm_nonneg x])

lemma lreg_phi_continuous : Continuous (lreg_phi d) := by
  unfold lreg_phi
  refine Continuous.inv₀ (by fun_prop) fun x => by positivity

lemma lreg_phi_integrable : Integrable (lreg_phi d) := by
  have h := integrable_one_add_norm (E := Euc d) (μ := volume) (r := ((d + 1 : ℕ) : ℝ))
    (by simp)
  refine h.congr (Eventually.of_forall fun x => ?_)
  have h0 : (0 : ℝ) ≤ 1 + ‖x‖ := by positivity
  show (1 + ‖x‖) ^ (-((d + 1 : ℕ) : ℝ)) = lreg_phi d x
  rw [lreg_phi, Real.rpow_neg h0, Real.rpow_natCast]

/-- Shift comparison of the weight. -/
lemma lreg_phi_shift {x x₀ : Euc d} (z : Euc d) (h : ‖x - x₀‖ ≤ 1) :
    lreg_phi d (x - z) ≤ 2 ^ (d + 1) * lreg_phi d (x₀ - z) := by
  unfold lreg_phi
  have h1 : 1 + ‖x₀ - z‖ ≤ 2 * (1 + ‖x - z‖) := by
    have : ‖x₀ - z‖ ≤ ‖x₀ - x‖ + ‖x - z‖ := by
      calc ‖x₀ - z‖ = ‖(x₀ - x) + (x - z)‖ := by congr 1; abel
        _ ≤ _ := norm_add_le _ _
    have h' : ‖x₀ - x‖ ≤ 1 := by rwa [norm_sub_rev]
    linarith [norm_nonneg (x - z)]
  have hp : (0 : ℝ) < (1 + ‖x - z‖) ^ (d + 1) := by positivity
  have hq : (0 : ℝ) < (1 + ‖x₀ - z‖) ^ (d + 1) := by positivity
  have h2 : (1 + ‖x₀ - z‖) ^ (d + 1) ≤ 2 ^ (d + 1) * (1 + ‖x - z‖) ^ (d + 1) := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) h1 _
  calc ((1 + ‖x - z‖) ^ (d + 1))⁻¹
      = 2 ^ (d + 1) * (2 ^ (d + 1) * (1 + ‖x - z‖) ^ (d + 1))⁻¹ := by
        field_simp
    _ ≤ 2 ^ (d + 1) * ((1 + ‖x₀ - z‖) ^ (d + 1))⁻¹ :=
        mul_le_mul_of_nonneg_left (inv_anti₀ hq h2) (by positivity)

lemma lreg_bound_of_rdec {G : Type*} [NormedAddCommGroup G] {F : Euc d → G} (hF : lreg_RDec F)
    (j : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ y, (1 + ‖y‖) ^ j * ‖F y‖ ≤ C * lreg_phi d y := by
  obtain ⟨C, hC⟩ := hF (d + 1 + j)
  refine ⟨max C 0, le_max_right _ _, fun y => ?_⟩
  have hp : (0 : ℝ) < (1 + ‖y‖) ^ (d + 1) := by positivity
  unfold lreg_phi
  rw [← div_eq_mul_inv, le_div_iff₀ hp]
  calc (1 + ‖y‖) ^ j * ‖F y‖ * (1 + ‖y‖) ^ (d + 1) = (1 + ‖y‖) ^ (d + 1 + j) * ‖F y‖ := by ring
    _ ≤ C := hC y
    _ ≤ max C 0 := le_max_left _ _

lemma lreg_integrable_of_bound {G : Type*} [NormedAddCommGroup G] {F : Euc d → G}
    (hm : AEStronglyMeasurable F volume) {C : ℝ} (hF : ∀ y, ‖F y‖ ≤ C * lreg_phi d y) :
    Integrable F :=
  (lreg_phi_integrable.const_mul C).mono' hm (ae_of_all _ hF)

/-- The constant bounding `∫ ‖z‖^{-σ} φ(x - z) dz`. -/
def lreg_A (d : ℕ) (σ : ℝ) : ℝ := (∫ z in ball (0 : Euc d) 1, ‖z‖ ^ (-σ)) + ∫ z, lreg_phi d z

lemma lreg_ball_integrable (hd : 1 ≤ d) {σ : ℝ} (hσ : σ < d) :
    IntegrableOn (fun z : Euc d => ‖z‖ ^ (-σ)) (ball 0 1) := by
  refine integrableOn_ball_of_norm_le_rpow (C := 1) (α := σ) (r := 1) (by simpa using hd)
    (by simpa using hσ) ?_ ?_
  · exact ae_of_all _ fun x => by
      simp [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg x) _)]
  · exact (measurable_norm.pow_const _).aestronglyMeasurable

lemma lreg_A_nonneg {σ : ℝ} : 0 ≤ lreg_A d σ := by
  unfold lreg_A
  refine add_nonneg (setIntegral_nonneg measurableSet_ball fun z _ => ?_)
    (integral_nonneg fun z => (lreg_phi_pos z).le)
  exact Real.rpow_nonneg (norm_nonneg z) _

lemma lreg_K_dom (hd : 1 ≤ d) {σ : ℝ} (hσ : σ < d) (hσ0 : 0 ≤ σ) {C : ℝ} (hC : 0 ≤ C)
    {G : Type*} [NormedAddCommGroup G] {h : Euc d → G} (hm : AEStronglyMeasurable h volume)
    (hb : ∀ y, ‖h y‖ ≤ C * lreg_phi d y) (x : Euc d) :
    Integrable (fun z : Euc d => ‖z‖ ^ (-σ) * ‖h (x - z)‖) ∧
      ∫ z, ‖z‖ ^ (-σ) * ‖h (x - z)‖ ≤ C * lreg_A d σ := by
  have hI1 : Integrable ((ball (0 : Euc d) 1).indicator fun z : Euc d => ‖z‖ ^ (-σ)) :=
    (lreg_ball_integrable hd hσ).integrable_indicator measurableSet_ball
  have hI2 : Integrable (fun z : Euc d => lreg_phi d (x - z)) := lreg_phi_integrable.comp_sub_left x
  have hint : Integrable (fun z : Euc d =>
      C * ((ball (0 : Euc d) 1).indicator (fun z : Euc d => ‖z‖ ^ (-σ)) z + lreg_phi d (x - z))) :=
    (hI1.add hI2).const_mul C
  have hmeas : AEStronglyMeasurable (fun z : Euc d => ‖z‖ ^ (-σ) * ‖h (x - z)‖) volume := by
    refine (measurable_norm.pow_const _).aestronglyMeasurable.mul ?_
    exact (hm.comp_measurePreserving (volume.measurePreserving_sub_left x)).norm
  have hpt : ∀ z : Euc d, ‖z‖ ^ (-σ) * ‖h (x - z)‖ ≤
      C * ((ball (0 : Euc d) 1).indicator (fun z : Euc d => ‖z‖ ^ (-σ)) z + lreg_phi d (x - z)) := by
    intro z
    have hz0 : 0 ≤ ‖z‖ ^ (-σ) := Real.rpow_nonneg (norm_nonneg z) _
    have hphi := lreg_phi_le_one (x - z)
    have hphi0 := (lreg_phi_pos (x - z)).le
    by_cases hz : z ∈ ball (0 : Euc d) 1
    · rw [Set.indicator_of_mem hz]
      calc ‖z‖ ^ (-σ) * ‖h (x - z)‖ ≤ ‖z‖ ^ (-σ) * (C * lreg_phi d (x - z)) :=
            mul_le_mul_of_nonneg_left (hb _) hz0
        _ ≤ ‖z‖ ^ (-σ) * (C * 1) := by gcongr
        _ ≤ _ := by nlinarith
    · rw [Set.indicator_of_notMem hz]
      have hz1 : 1 ≤ ‖z‖ := by simpa using hz
      have : ‖z‖ ^ (-σ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hz1 (by linarith)
      calc ‖z‖ ^ (-σ) * ‖h (x - z)‖ ≤ 1 * ‖h (x - z)‖ :=
            mul_le_mul_of_nonneg_right this (norm_nonneg _)
        _ ≤ C * lreg_phi d (x - z) := by rw [one_mul]; exact hb _
        _ = _ := by simp
  refine ⟨hint.mono' hmeas (ae_of_all _ fun z => ?_), ?_⟩
  · rw [Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg (norm_nonneg z) _) (norm_nonneg _))]
    exact hpt z
  · calc ∫ z, ‖z‖ ^ (-σ) * ‖h (x - z)‖
        ≤ ∫ z, C * ((ball (0 : Euc d) 1).indicator (fun z : Euc d => ‖z‖ ^ (-σ)) z +
          lreg_phi d (x - z)) :=
          integral_mono_of_nonneg (ae_of_all _ fun z => mul_nonneg
            (Real.rpow_nonneg (norm_nonneg z) _) (norm_nonneg _)) hint (ae_of_all _ hpt)
      _ = C * lreg_A d σ := by
        rw [integral_const_mul, integral_add hI1 hI2, integral_indicator measurableSet_ball,
          integral_sub_left_eq_self (fun z => lreg_phi d z) volume x]
        rfl

/-- Convolution of a vector kernel `κ` with `F`, paired through the bilinear map `B`. -/
def lreg_conv {E2 E3 : Type} [NormedAddCommGroup E2] [NormedSpace ℝ E2] [NormedAddCommGroup E3]
    [NormedSpace ℝ E3] (B : Euc d →L[ℝ] E2 →L[ℝ] E3) (κ : Euc d → Euc d) (F : Euc d → E2)
    (x : Euc d) : E3 :=
  ∫ z, B (κ z) (F (x - z))

section Conv

variable {E2 E3 : Type} [NormedAddCommGroup E2] [NormedSpace ℝ E2] [NormedAddCommGroup E3]
  [NormedSpace ℝ E3]

lemma lreg_integrable_B (hd : 1 ≤ d) {σ : ℝ} (hσ : σ < d) (hσ0 : 0 ≤ σ) {κ : Euc d → Euc d}
    (hκm : AEStronglyMeasurable κ volume) (hκ : ∀ z, ‖κ z‖ ≤ ‖z‖ ^ (-σ))
    (B : Euc d →L[ℝ] E2 →L[ℝ] E3) {M : ℝ} (hM : 0 ≤ M) (hB : ∀ v w, ‖B v w‖ ≤ M * ‖v‖ * ‖w‖)
    {G : Euc d → E2} (hGm : AEStronglyMeasurable G volume) {C : ℝ}
    (hC : 0 ≤ C) (hG : ∀ y, ‖G y‖ ≤ C * lreg_phi d y) (x : Euc d) :
    Integrable (fun z => B (κ z) (G (x - z))) ∧
      ‖∫ z, B (κ z) (G (x - z))‖ ≤ M * (C * lreg_A d σ) := by
  obtain ⟨hI, hJ⟩ := lreg_K_dom hd hσ hσ0 hC hGm hG x
  have hmeas : AEStronglyMeasurable (fun z => B (κ z) (G (x - z))) volume :=
    B.aestronglyMeasurable_comp₂ hκm (hGm.comp_measurePreserving (volume.measurePreserving_sub_left x))
  have hpt : ∀ z, ‖B (κ z) (G (x - z))‖ ≤ M * (‖z‖ ^ (-σ) * ‖G (x - z)‖) := by
    intro z
    calc ‖B (κ z) (G (x - z))‖ ≤ M * ‖κ z‖ * ‖G (x - z)‖ := hB _ _
      _ ≤ M * ‖z‖ ^ (-σ) * ‖G (x - z)‖ := by gcongr; exact hκ z
      _ = _ := by ring
  refine ⟨(hI.const_mul M).mono' hmeas (ae_of_all _ hpt), ?_⟩
  calc ‖∫ z, B (κ z) (G (x - z))‖ ≤ ∫ z, M * (‖z‖ ^ (-σ) * ‖G (x - z)‖) :=
        norm_integral_le_of_norm_le (hI.const_mul M) (ae_of_all _ hpt)
    _ = M * ∫ z, ‖z‖ ^ (-σ) * ‖G (x - z)‖ := integral_const_mul _ _
    _ ≤ M * (C * lreg_A d σ) := by gcongr

lemma lreg_conv_continuous (hd : 1 ≤ d) {σ : ℝ} (hσ : σ < d) (hσ0 : 0 ≤ σ) {κ : Euc d → Euc d}
    (hκm : AEStronglyMeasurable κ volume) (hκ : ∀ z, ‖κ z‖ ≤ ‖z‖ ^ (-σ)) [CompleteSpace E3]
    (B : Euc d →L[ℝ] E2 →L[ℝ] E3) {M : ℝ} (hM : 0 ≤ M) (hB : ∀ v w, ‖B v w‖ ≤ M * ‖v‖ * ‖w‖)
    {F : Euc d → E2} (hF : Continuous F) (h0 : lreg_RDec F) :
    Continuous (lreg_conv B κ F) := by
  obtain ⟨C0, hC0, hF0⟩ := lreg_bound_of_rdec h0 0
  have hFb : ∀ y, ‖F y‖ ≤ C0 * lreg_phi d y := fun y => by simpa using hF0 y
  rw [continuous_iff_continuousAt]
  intro x₀
  set h : Euc d → ℝ := fun y => 2 ^ (d + 1) * C0 * lreg_phi d y with hh
  have hhm : AEStronglyMeasurable h volume :=
    (continuous_const.mul lreg_phi_continuous).aestronglyMeasurable
  have hhb : ∀ y, ‖h y‖ ≤ (2 ^ (d + 1) * C0) * lreg_phi d y := fun y => by
    rw [hh]; simp only [Real.norm_eq_abs]
    rw [abs_of_nonneg (by have := lreg_phi_pos y; positivity)]
  obtain ⟨hI, -⟩ := lreg_K_dom hd hσ hσ0 (by positivity : (0 : ℝ) ≤ 2 ^ (d + 1) * C0) hhm hhb x₀
  refine continuousAt_of_dominated (bound := fun z => M * (‖z‖ ^ (-σ) * ‖h (x₀ - z)‖)) ?_ ?_
    (hI.const_mul _) ?_
  · exact Eventually.of_forall fun x =>
      B.aestronglyMeasurable_comp₂ hκm
        (hF.aestronglyMeasurable.comp_measurePreserving (volume.measurePreserving_sub_left x))
  · filter_upwards [ball_mem_nhds x₀ one_pos] with x hx
    refine ae_of_all _ fun z => ?_
    have hx' : ‖x - x₀‖ ≤ 1 := by simpa [dist_eq_norm] using hx.le
    have hsh := lreg_phi_shift (x := x) (x₀ := x₀) z hx'
    have hz0 : 0 ≤ ‖z‖ ^ (-σ) := Real.rpow_nonneg (norm_nonneg z) _
    calc ‖B (κ z) (F (x - z))‖ ≤ M * ‖κ z‖ * ‖F (x - z)‖ := hB _ _
      _ ≤ M * ‖z‖ ^ (-σ) * (C0 * lreg_phi d (x - z)) := by
          gcongr
          · exact hκ z
          · exact hFb _
      _ ≤ M * ‖z‖ ^ (-σ) * (C0 * (2 ^ (d + 1) * lreg_phi d (x₀ - z))) := by gcongr
      _ = M * (‖z‖ ^ (-σ) * ‖h (x₀ - z)‖) := by
          rw [hh]; simp only [Real.norm_eq_abs]
          rw [abs_of_nonneg (by have := lreg_phi_pos (x₀ - z); positivity)]
          ring
  · refine ae_of_all _ fun z => ?_
    exact ((B (κ z)).continuous.comp (hF.comp (continuous_id.sub continuous_const))).continuousAt

lemma lreg_conv_hasFDerivAt (hd : 1 ≤ d) {σ : ℝ} (hσ : σ < d) (hσ0 : 0 ≤ σ) {κ : Euc d → Euc d}
    (hκm : AEStronglyMeasurable κ volume) (hκ : ∀ z, ‖κ z‖ ≤ ‖z‖ ^ (-σ)) [CompleteSpace E3]
    (B : Euc d →L[ℝ] E2 →L[ℝ] E3) {M : ℝ} (hM : 0 ≤ M) (hB : ∀ v w, ‖B v w‖ ≤ M * ‖v‖ * ‖w‖)
    {F : Euc d → E2} (hF : ContDiff ℝ 1 F) (h0 : lreg_RDec F)
    (h1 : lreg_RDec (fderiv ℝ F)) (x₀ : Euc d) :
    HasFDerivAt (lreg_conv B κ F) (lreg_conv (B.precompR (Euc d)) κ (fderiv ℝ F) x₀) x₀ := by
  obtain ⟨C0, hC0, hF0⟩ := lreg_bound_of_rdec h0 0
  obtain ⟨C1, hC1, hF1⟩ := lreg_bound_of_rdec h1 0
  have hFb : ∀ y, ‖F y‖ ≤ C0 * lreg_phi d y := fun y => by simpa using hF0 y
  have hF1b : ∀ y, ‖fderiv ℝ F y‖ ≤ C1 * lreg_phi d y := fun y => by simpa using hF1 y
  have hFc : Continuous F := hF.continuous
  have hDc : Continuous (fderiv ℝ F) := hF.continuous_fderiv (by norm_num)
  set h : Euc d → ℝ := fun y => 2 ^ (d + 1) * C1 * lreg_phi d y with hh
  have hhm : AEStronglyMeasurable h volume :=
    (continuous_const.mul lreg_phi_continuous).aestronglyMeasurable
  have hhb : ∀ y, ‖h y‖ ≤ (2 ^ (d + 1) * C1) * lreg_phi d y := fun y => by
    rw [hh]; simp only [Real.norm_eq_abs]
    rw [abs_of_nonneg (by have := lreg_phi_pos y; positivity)]
  obtain ⟨hI, -⟩ := lreg_K_dom hd hσ hσ0 (by positivity : (0 : ℝ) ≤ 2 ^ (d + 1) * C1) hhm hhb x₀
  unfold lreg_conv
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℝ) (s := ball x₀ 1)
    (F := fun x z => B (κ z) (F (x - z)))
    (F' := fun x z => (B.precompR (Euc d) (κ z)) (fderiv ℝ F (x - z)))
    (bound := fun z => M * (‖z‖ ^ (-σ) * ‖h (x₀ - z)‖)) (ball_mem_nhds x₀ one_pos) ?_ ?_ ?_ ?_
    (hI.const_mul _) ?_
  · exact Eventually.of_forall fun x =>
      B.aestronglyMeasurable_comp₂ hκm
        (hFc.aestronglyMeasurable.comp_measurePreserving (volume.measurePreserving_sub_left x))
  · exact (lreg_integrable_B hd hσ hσ0 hκm hκ B hM hB hFc.aestronglyMeasurable hC0 hFb x₀).1
  · exact (B.precompR (Euc d)).aestronglyMeasurable_comp₂ hκm
      (hDc.aestronglyMeasurable.comp_measurePreserving (volume.measurePreserving_sub_left x₀))
  · refine ae_of_all _ fun z x hx => ?_
    have hx' : ‖x - x₀‖ ≤ 1 := by simpa [dist_eq_norm] using (mem_ball.1 hx).le
    have hsh := lreg_phi_shift (x := x) (x₀ := x₀) z hx'
    have hz0 : 0 ≤ ‖z‖ ^ (-σ) := Real.rpow_nonneg (norm_nonneg z) _
    have hBv : ‖B (κ z)‖ ≤ M * ‖κ z‖ :=
      (B (κ z)).opNorm_le_bound (by positivity) fun w => by
        have := hB (κ z) w; linarith [mul_assoc M ‖κ z‖ ‖w‖]
    calc ‖(B.precompR (Euc d) (κ z)) (fderiv ℝ F (x - z))‖
        = ‖(B (κ z)).comp (fderiv ℝ F (x - z))‖ := rfl
      _ ≤ ‖B (κ z)‖ * ‖fderiv ℝ F (x - z)‖ := (B (κ z)).opNorm_comp_le _
      _ ≤ (M * ‖κ z‖) * ‖fderiv ℝ F (x - z)‖ := by gcongr
      _ ≤ M * ‖z‖ ^ (-σ) * (C1 * lreg_phi d (x - z)) := by
          gcongr
          · exact hκ z
          · exact hF1b _
      _ ≤ M * ‖z‖ ^ (-σ) * (C1 * (2 ^ (d + 1) * lreg_phi d (x₀ - z))) := by gcongr
      _ = M * (‖z‖ ^ (-σ) * ‖h (x₀ - z)‖) := by
          rw [hh]; simp only [Real.norm_eq_abs]
          rw [abs_of_nonneg (by have := lreg_phi_pos (x₀ - z); positivity)]
          ring
  · refine ae_of_all _ fun z x _ => ?_
    have h1 : HasFDerivAt F (fderiv ℝ F (x - z)) (x - z) :=
      (hF.differentiable one_ne_zero (x - z)).hasFDerivAt
    have h2 : HasFDerivAt (fun x : Euc d => x - z) (ContinuousLinearMap.id ℝ (Euc d)) x :=
      (hasFDerivAt_id x).sub_const z
    have h3 := (B (κ z)).hasFDerivAt.comp x (h1.comp x h2)
    refine h3.congr_fderiv ?_
    ext w
    simp

/-- Smoothness of the convolution `κ ⋆ F`, derivatives falling on `F`. -/
theorem lreg_conv_smooth (hd : 1 ≤ d) {σ : ℝ} (hσ : σ < d) (hσ0 : 0 ≤ σ) {κ : Euc d → Euc d}
    (hκm : AEStronglyMeasurable κ volume) (hκ : ∀ z, ‖κ z‖ ≤ ‖z‖ ^ (-σ)) :
    ∀ (m : ℕ) {E2 E3 : Type} [NormedAddCommGroup E2] [NormedSpace ℝ E2] [NormedAddCommGroup E3]
      [NormedSpace ℝ E3] [CompleteSpace E3] (B : Euc d →L[ℝ] E2 →L[ℝ] E3) {M : ℝ}, 0 ≤ M →
      (∀ v w, ‖B v w‖ ≤ M * ‖v‖ * ‖w‖) → ∀ {F : Euc d → E2}, ContDiff ℝ m F →
      (∀ j ≤ m, lreg_RDec (iteratedFDeriv ℝ j F)) →
      ContDiff ℝ m (lreg_conv B κ F) ∧ ∀ C : ℝ, 0 ≤ C →
        (∀ y, ‖iteratedFDeriv ℝ m F y‖ ≤ C * lreg_phi d y) →
        ∀ x, ‖iteratedFDeriv ℝ m (lreg_conv B κ F) x‖ ≤ M * (C * lreg_A d σ) := by
  intro m
  induction m with
  | zero =>
    intro E2 E3 _ _ _ _ _ B M hM hB F hF hdec
    have hFc : Continuous F := by
      rw [Nat.cast_zero, contDiff_zero] at hF; exact hF
    have h0 : lreg_RDec F := by simpa [lreg_RDec] using hdec 0 le_rfl
    refine ⟨?_, fun C hC hCb x => ?_⟩
    · rw [Nat.cast_zero, contDiff_zero]
      exact lreg_conv_continuous hd hσ hσ0 hκm hκ B hM hB hFc h0
    · rw [norm_iteratedFDeriv_zero]
      exact (lreg_integrable_B hd hσ hσ0 hκm hκ B hM hB hFc.aestronglyMeasurable hC
        (fun y => by simpa using hCb y) x).2
  | succ m ih =>
    intro E2 E3 _ _ _ _ _ B M hM hB F hF hdec
    have hF1 : ContDiff ℝ 1 F := hF.of_le (by exact_mod_cast Nat.le_add_left 1 m)
    have h0 : lreg_RDec F := by simpa [lreg_RDec] using hdec 0 (Nat.zero_le _)
    have h1 : lreg_RDec (fderiv ℝ F) := by simpa [lreg_RDec] using hdec 1 (by omega)
    have hdec' : ∀ j ≤ m, lreg_RDec (iteratedFDeriv ℝ j (fderiv ℝ F)) := by
      intro j hj
      have := hdec (j + 1) (by omega)
      simpa [lreg_RDec, norm_iteratedFDeriv_fderiv] using this
    have hFd : ContDiff ℝ m (fderiv ℝ F) := hF.fderiv_right (by norm_cast)
    have hB' : ∀ (v : Euc d) (D : Euc d →L[ℝ] E2), ‖(B.precompR (Euc d)) v D‖ ≤ M * ‖v‖ * ‖D‖ := by
      intro v D
      have hBv : ‖B v‖ ≤ M * ‖v‖ :=
        (B v).opNorm_le_bound (by positivity) fun w => by
          have := hB v w; linarith [mul_assoc M ‖v‖ ‖w‖]
      calc ‖(B.precompR (Euc d)) v D‖ = ‖(B v).comp D‖ := rfl
        _ ≤ ‖B v‖ * ‖D‖ := (B v).opNorm_comp_le _
        _ ≤ _ := by gcongr
    obtain ⟨hcd, hbd⟩ := ih (B.precompR (Euc d)) hM hB' hFd hdec'
    have hfd : ∀ x, HasFDerivAt (lreg_conv B κ F)
        (lreg_conv (B.precompR (Euc d)) κ (fderiv ℝ F) x) x :=
      fun x => lreg_conv_hasFDerivAt hd hσ hσ0 hκm hκ B hM hB hF1 h0 h1 x
    have heq : fderiv ℝ (lreg_conv B κ F) = lreg_conv (B.precompR (Euc d)) κ (fderiv ℝ F) :=
      funext fun x => (hfd x).fderiv
    refine ⟨?_, fun C hC hCb x => ?_⟩
    · have hc : ((m + 1 : ℕ) : WithTop ℕ∞) = (m : WithTop ℕ∞) + 1 := by push_cast; rfl
      rw [hc, contDiff_succ_iff_fderiv]
      refine ⟨fun x => (hfd x).differentiableAt, fun h => absurd h (by simp), ?_⟩
      rw [heq]; exact hcd
    · rw [← norm_iteratedFDeriv_fderiv, heq]
      exact hbd C hC (fun y => by rw [norm_iteratedFDeriv_fderiv]; exact hCb y) x

end Conv

end HRS.MS.LogReg

end
