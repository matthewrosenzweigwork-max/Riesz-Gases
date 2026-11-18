import HRS.MS.R2SeAux33

/-!
# S9.9 `r2_static_edgeworth`, packet 34: the row integral of the commutator kernel

Worker S99, namespace `S99`.  For `r = ρ u`, `v = ∇χ` and `D_r(y) = ⟨∇r(y), v(y)⟩ + r(y) div v(y)` (the divergence of `r v`):
`s99_row`: `∫ r(y) h_v(x,y) dy = D G_u(x)[v(x)] - ∫ g(x-y) D_r(y) dy` (S4.5 `s45_obi` and `s99_Gpot_fderiv`).
-/

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace ContDiff

noncomputable section

namespace S99

open S45
open HRS.Whole
open HRS (Euc cbNorm MemCb)

variable {d N : ℕ}

/-- The weighted density `r = ρ u`. -/
def rr (d : ℕ) (s a β : ℝ) (u : Euc d → ℝ) (y : Euc d) : ℝ := thermalDensity d s a β y * u y

/-- The divergence `div (r v) = ⟨∇r, v⟩ + r div v`. -/
def Dd (r : Euc d → ℝ) (v : Euc d → Euc d) (y : Euc d) : ℝ :=
  ⟪gradient r y, v y⟫ + r y * s45_div v y

section PotD

variable (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {a β C c BU : ℝ} (hT : ThermalData d s a β C c BU)

include hd hs0 hsd hT

theorem s99_gauss_int {f : Euc d → ℝ} (hf : Continuous f) {K : ℝ}
    (hb : ∀ y, |f y| ≤ K * Real.exp (-c * ‖y‖ ^ 2)) : Integrable f := by
  refine Integrable.mono' ((HRS.MP.SelfSimP4Impl.p4g_integrable_gauss d hT.hc).const_mul K)
    hf.aestronglyMeasurable (Filter.Eventually.of_forall fun y => ?_)
  rw [Real.norm_eq_abs]
  simpa [neg_mul] using hb y

theorem s99_LI_g {h : Euc d → ℝ} (hh : Continuous h) {K : ℝ} (hK : 0 ≤ K)
    (hb : ∀ y, |h y| ≤ K * Real.exp (-c * ‖y‖ ^ 2)) (x : Euc d) :
    Integrable (fun y => rieszKernel d s (x - y) * h y) := by
  have hgm : Measurable (rieszKernel d s) := by
    rw [← movtr_gEps_zero d s]; exact movtr_gEps_measurable s 0
  have hkB : ∀ z : Euc d, z ≠ 0 → |rieszKernel d s z| ≤
      1 * (2 * ‖z‖ ^ (-movtr_sp s) + ‖z‖ + 1) := fun z hz => by
    rw [one_mul, ← movtr_gEps_zero d s]
    exact movtr_gEps_abs_le hs0 le_rfl zero_le_one hz
  exact s45_LI (by omega) hs0 hsd hT.hc (k := rieszKernel d s) (h := h) hgm.aestronglyMeasurable hh
    zero_le_one hkB hK hb x

theorem s99_Gpot_fderiv_gen {u : Euc d → ℝ} (hu : ContDiff ℝ 1 u) {Bu Du : ℝ} (hBu : ∀ x, |u x| ≤ Bu)
    (hDu : ∀ x, ‖fderiv ℝ u x‖ ≤ Du) (hdiff : Differentiable ℝ (Gpot d s a β u)) (x e : Euc d) :
    fderiv ℝ (Gpot d s a β u) x e = ∫ y, rieszKernel d s (x - y) *
      fderiv ℝ (fun y => thermalDensity d s a β y * u y) y e := by
  set t : ℝ := 1 + ‖e‖ with ht
  have ht0 : 0 < t := by have := norm_nonneg e; positivity
  set e' : Euc d := t⁻¹ • e with he'
  have he'1 : ‖e'‖ ≤ 1 := by
    rw [he', norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 ht0)]
    rw [inv_mul_le_iff₀ ht0]
    simp only [ht]; linarith
  have h1 := s99_Gpot_fderiv hd hs0 hsd hT hu hBu hDu hdiff x e' he'1
  have eq1 : e = t • e' := by
    rw [he', smul_smul, mul_inv_cancel₀ ht0.ne', one_smul]
  have e2 : fderiv ℝ (Gpot d s a β u) x e = t * fderiv ℝ (Gpot d s a β u) x e' := by
    conv_lhs => rw [eq1]
    rw [map_smul, smul_eq_mul]
  have e3 : ∀ y, fderiv ℝ (fun y => thermalDensity d s a β y * u y) y e =
      t * fderiv ℝ (fun y => thermalDensity d s a β y * u y) y e' := fun y => by
    conv_lhs => rw [eq1]
    rw [map_smul, smul_eq_mul]
  rw [e2, h1, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only [e3]; ring

theorem s99_row {u : Euc d → ℝ} (hu : ContDiff ℝ 1 u) {Bu Du : ℝ} (hBu : ∀ x, |u x| ≤ Bu)
    (hDu : ∀ x, ‖fderiv ℝ u x‖ ≤ Du) (hdiff : Differentiable ℝ (Gpot d s a β u)) {χ : Euc d → ℝ}
    (hχ : ContDiff ℝ 2 χ) {B1 B2 : ℝ} (hB1 : ∀ x, ‖gradient χ x‖ ≤ B1)
    (hB2 : ∀ x, ‖fderiv ℝ (gradient χ) x‖ ≤ B2) (x : Euc d) :
    ∫ y, rr d s a β u y * commutatorKernel d s (gradient χ) x y =
      fderiv ℝ (Gpot d s a β u) x (gradient χ x) -
        ∫ y, rieszKernel d s (x - y) * Dd (rr d s a β u) (gradient χ) y := by
  obtain ⟨hr1, hr0, hr1'⟩ := s99_r_bounds hd hs0 hsd hT hu hBu hDu
  have hBu0 : 0 ≤ Bu := (abs_nonneg _).trans (hBu 0)
  have hDu0 : 0 ≤ Du := (norm_nonneg _).trans (hDu 0)
  set C' : ℝ := C * (Bu + Du + 1) with hC'def
  have hC' : 0 ≤ C' := by have := hT.C0; positivity
  have hB10 : 0 ≤ B1 := (norm_nonneg _).trans (hB1 0)
  have hB20 : 0 ≤ B2 := (norm_nonneg _).trans (hB2 0)
  have hv1 : ContDiff ℝ 1 (gradient χ) := s45_contDiff_gradient hχ
  have hrr : rr d s a β u = fun y => thermalDensity d s a β y * u y := rfl
  have hobi := s45_obi (by omega) hs0 hsd hT.hc hC' hr1 hr0 hr1' hv1 hB1 hB2 x
  have hcomm : ∀ y, commutatorKernel d s (gradient χ) x y =
      ⟪gradient χ x - gradient χ y, rieszKernelGrad d s (x - y)⟫ := fun y => rfl
  simp_rw [hcomm]
  have hobi' : (∫ y, rr d s a β u y * ⟪gradient χ x - gradient χ y, rieszKernelGrad d s (x - y)⟫) =
      ∫ y, rieszKernel d s (x - y) * (⟪gradient (rr d s a β u) y, gradient χ x - gradient χ y⟫ -
        rr d s a β u y * s45_div (gradient χ) y) := hobi
  rw [hobi']
  have hpt : ∀ y, rieszKernel d s (x - y) * (⟪gradient (rr d s a β u) y, gradient χ x - gradient χ y⟫ -
      rr d s a β u y * s45_div (gradient χ) y) =
      rieszKernel d s (x - y) * fderiv ℝ (rr d s a β u) y (gradient χ x) -
        rieszKernel d s (x - y) * Dd (rr d s a β u) (gradient χ) y := by
    intro y
    unfold Dd
    have hin : ⟪gradient (rr d s a β u) y, gradient χ x⟫ = fderiv ℝ (rr d s a β u) y (gradient χ x) := by
      rw [real_inner_comm]
      exact HRS.MS.PoisKolm.kl_inner_gradient (rr d s a β u) y (gradient χ x)
    rw [inner_sub_right, hin]
    ring
  simp_rw [hpt]
  have hrc : Continuous (fderiv ℝ (rr d s a β u)) := hr1.continuous_fderiv one_ne_zero
  have hexp := fun y : Euc d => (Real.exp_pos (-c * ‖y‖ ^ 2)).le
  have I1 : Integrable (fun y => rieszKernel d s (x - y) * fderiv ℝ (rr d s a β u) y (gradient χ x)) := by
    refine s99_LI_g hd hs0 hsd hT (h := fun y => fderiv ℝ (rr d s a β u) y (gradient χ x))
      (hrc.clm_apply continuous_const) (K := C' * B1) (by positivity) (fun y => ?_) x
    calc |fderiv ℝ (rr d s a β u) y (gradient χ x)| ≤ ‖fderiv ℝ (rr d s a β u) y‖ * ‖gradient χ x‖ := by
          rw [← Real.norm_eq_abs]; exact ContinuousLinearMap.le_opNorm _ _
      _ ≤ (C' * Real.exp (-c * ‖y‖ ^ 2)) * B1 := mul_le_mul (hr1' y) (hB1 x) (norm_nonneg _) (by
          have := hexp y; positivity)
      _ = C' * B1 * Real.exp (-c * ‖y‖ ^ 2) := by ring
  have hDc : Continuous (Dd (rr d s a β u) (gradient χ)) := by
    unfold Dd
    exact ((s45_gradient_continuous hr1).inner hv1.continuous).add (hr1.continuous.mul (s45_continuous_div hv1))
  have I2 : Integrable (fun y => rieszKernel d s (x - y) * Dd (rr d s a β u) (gradient χ) y) := by
    refine s99_LI_g hd hs0 hsd hT (h := Dd (rr d s a β u) (gradient χ)) hDc
      (K := C' * (B1 + d * B2)) (by positivity) (fun y => ?_) x
    unfold Dd
    have e1 : |⟪gradient (rr d s a β u) y, gradient χ y⟫| ≤ (C' * Real.exp (-c * ‖y‖ ^ 2)) * B1 := by
      refine (abs_real_inner_le_norm _ _).trans ?_
      rw [s45_norm_gradient]
      exact mul_le_mul (hr1' y) (hB1 y) (norm_nonneg _) (by have := hexp y; positivity)
    have e2 : |rr d s a β u y * s45_div (gradient χ) y| ≤ (C' * Real.exp (-c * ‖y‖ ^ 2)) * (d * B2) := by
      rw [abs_mul]
      exact mul_le_mul (hr0 y) (s45_div_le hB2 y) (abs_nonneg _) (by have := hexp y; positivity)
    refine (abs_add_le _ _).trans ((add_le_add e1 e2).trans (le_of_eq ?_))
    ring
  rw [integral_sub I1 I2]
  have hgen := s99_Gpot_fderiv_gen hd hs0 hsd hT hu hBu hDu hdiff x (gradient χ x)
  have hgen' : fderiv ℝ (Gpot d s a β u) x (gradient χ x) = ∫ y, rieszKernel d s (x - y) *
      fderiv ℝ (rr d s a β u) y (gradient χ x) := hgen
  rw [hgen']

end PotD

end S99

end
