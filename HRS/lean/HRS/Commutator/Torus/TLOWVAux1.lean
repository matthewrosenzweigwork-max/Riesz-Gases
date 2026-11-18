import HRS.Commutator.Torus.Defs
import HRS.Commutator.Torus.TPOSAux16
import HRS.Commutator.Torus.TENAux2
import HRS.Commutator.Torus.TENAux4
import HRS.Commutator.Torus.TEN2Aux11
import HRS.Commutator.Torus.TKRAux13
import HRS.Commutator.Torus.TSAMPAux7
import HRS.Commutator.Torus.TSAMPAux10
import HRS.Commutator.Torus.TSAMPAux16
import HRS.Commutator.Torus.TSAMPAux30
import HRS.Commutator.Torus.TSAMPAux34
import HRS.Commutator.Torus.TPRODAux4

/-!
# T-LOWV / T-INHOM helpers, part 1: the commutator form for kernels with `L¹` weight `|x||F(x)|`

Prefix `tlowv_`.  For `F : 𝕋^d → ℝ^d` odd and measurable with `W_F(z) = |z|_𝕋 ‖F z‖` integrable, and `v` Lipschitz,
the integrand `commKernel F v x y f(x) g(y)` is integrable on `𝕋^d × 𝕋^d` for `f, g ∈ L²`, with the Schur bound
`|∬ ...| ≤ L ‖W_F‖₁ (t‖f‖² + t⁻¹‖g‖²)/2`; and the form is `L²`-continuous.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform

namespace HRS.Commutator.TorusNote

open HRS

variable {d : ℕ}

/-- `W_F(z) = |z|_𝕋 ‖F z‖`. -/
def tlowvW (F : Torus d → Euc d) (z : Torus d) : ℝ := KernelGrad.tdist z 0 * ‖F z‖

lemma tlowvW_nonneg (F : Torus d → Euc d) (z : Torus d) : 0 ≤ tlowvW F z :=
  mul_nonneg (KernelGrad.tdist_nonneg _ _) (norm_nonneg _)

lemma tlowvW_even {F : Torus d → Euc d} (hodd : ∀ z, F (-z) = -F z) (z : Torus d) :
    tlowvW F (-z) = tlowvW F z := by
  unfold tlowvW
  rw [hodd, norm_neg, KernelGrad.tdist_neg]

lemma tlowvW_measurable {F : Torus d → Euc d} (hF : Measurable F) : Measurable (tlowvW F) :=
  ((tsamp_measurable_tdist 0).mul hF.norm)

lemma tlowv_commKernel_abs {L : ℝ} (hL : 0 ≤ L) {v : Torus d → Euc d} (hv : IsLipschitzVF L v)
    (F : Torus d → Euc d) (x y : Torus d) : |commKernel F v x y| ≤ L * tlowvW F (x - y) := by
  unfold commKernel tlowvW
  split_ifs with h
  · simp only [abs_zero]
    exact mul_nonneg hL (mul_nonneg (KernelGrad.tdist_nonneg _ _) (norm_nonneg _))
  · calc |inner ℝ (v x - v y) (F (x - y))| ≤ ‖v x - v y‖ * ‖F (x - y)‖ := abs_real_inner_le_norm _ _
      _ ≤ (L * KernelGrad.tdist x y) * ‖F (x - y)‖ :=
          mul_le_mul_of_nonneg_right (hv x y) (norm_nonneg _)
      _ = L * (KernelGrad.tdist (x - y) 0 * ‖F (x - y)‖) := by
          rw [KernelGrad.tdist_eq_sub_zero x y]; ring

lemma tlowv_commKernel_meas {F : Torus d → Euc d} (hF : Measurable F) {v : Torus d → Euc d}
    (hv : Continuous v) :
    Measurable fun p : Torus d × Torus d => commKernel F v p.1 p.2 := by
  have h1 : Measurable fun p : Torus d × Torus d => inner ℝ (v p.1 - v p.2) (F (p.1 - p.2)) :=
    (((hv.measurable.comp measurable_fst).sub (hv.measurable.comp measurable_snd))).inner
      (hF.comp (measurable_fst.sub measurable_snd))
  unfold commKernel
  exact Measurable.ite (measurableSet_eq_fun measurable_fst measurable_snd) measurable_const h1

lemma tlowv_amgm {t : ℝ} (ht : 0 < t) (u w : ℝ) :
    2 * (|u| * |w|) ≤ t * u ^ 2 + t⁻¹ * w ^ 2 := by
  have e : t * (|u| - t⁻¹ * |w|) ^ 2 = t * |u| ^ 2 - 2 * (|u| * |w|) + t⁻¹ * |w| ^ 2 := by
    field_simp; ring
  have h := mul_nonneg ht.le (sq_nonneg (|u| - t⁻¹ * |w|))
  rw [e, sq_abs, sq_abs] at h
  linarith

lemma tlowv_int_shear1 {f g : Torus d → ℝ} (hf : Integrable f) (hg : Integrable g)
    (hgn : ∀ z, g (-z) = g z) :
    Integrable (fun p : Torus d × Torus d => f p.1 * g (p.1 - p.2)) (volume.prod volume) := by
  have h := text_integrable_prod hg hf
  have h2 := h.swap
  refine h2.congr (Eventually.of_forall fun p => ?_)
  simp only [Function.comp_apply, Prod.fst_swap, Prod.snd_swap]
  rw [← hgn (p.2 - p.1), neg_sub, mul_comm]

lemma tlowv_int_shear2 {f g : Torus d → ℝ} (hf : Integrable f) (hg : Integrable g) :
    Integrable (fun p : Torus d × Torus d => f p.2 * g (p.1 - p.2)) (volume.prod volume) := by
  have h := text_integrable_prod hg hf
  refine h.congr (Eventually.of_forall fun p => ?_)
  simp only [mul_comm]

/-- Schur test for a symmetric non-negative `L¹` kernel. -/
lemma tlowv_schur {W : Torus d → ℝ} (hWm : Measurable W) (hW : Integrable W)
    (hWn : ∀ z, 0 ≤ W z) (hWe : ∀ z, W (-z) = W z) {f g : Torus d → ℝ}
    (hf : AEStronglyMeasurable f volume) (hg : AEStronglyMeasurable g volume)
    (hf2 : Integrable (fun x => f x ^ 2)) (hg2 : Integrable (fun x => g x ^ 2))
    {t : ℝ} (ht : 0 < t) :
    Integrable (fun p : Torus d × Torus d => W (p.1 - p.2) * (|f p.1| * |g p.2|))
        (volume.prod volume) ∧
      ∫ p : Torus d × Torus d, W (p.1 - p.2) * (|f p.1| * |g p.2|) ∂(volume.prod volume) ≤
        (t * (∫ x, f x ^ 2) + t⁻¹ * (∫ x, g x ^ 2)) / 2 * ∫ z, W z := by
  have hA := tlowv_int_shear1 hf2 hW hWe
  have hB := tlowv_int_shear2 hg2 hW
  have hbound : ∀ p : Torus d × Torus d, W (p.1 - p.2) * (|f p.1| * |g p.2|) ≤
      (t / 2) * (f p.1 ^ 2 * W (p.1 - p.2)) + (t⁻¹ / 2) * (g p.2 ^ 2 * W (p.1 - p.2)) := by
    intro p
    have h := tlowv_amgm ht (f p.1) (g p.2)
    have hw := hWn (p.1 - p.2)
    nlinarith [mul_le_mul_of_nonneg_left h hw]
  have hmeasf : AEStronglyMeasurable (fun p : Torus d × Torus d => f p.1) (volume.prod volume) :=
    hf.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst
  have hmeasg : AEStronglyMeasurable (fun p : Torus d × Torus d => g p.2) (volume.prod volume) :=
    hg.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd
  have hWd : Measurable fun p : Torus d × Torus d => W (p.1 - p.2) :=
    hWm.comp (measurable_fst.sub measurable_snd)
  have hint : Integrable (fun p : Torus d × Torus d => W (p.1 - p.2) * (|f p.1| * |g p.2|))
      (volume.prod volume) := by
    refine (((hA.const_mul (t / 2)).add (hB.const_mul (t⁻¹ / 2)))).mono'
      (hWd.aestronglyMeasurable.mul (hmeasf.norm.mul hmeasg.norm)) (Eventually.of_forall fun p => ?_)
    rw [Real.norm_of_nonneg (mul_nonneg (hWn _) (mul_nonneg (abs_nonneg _) (abs_nonneg _)))]
    exact hbound p
  refine ⟨hint, ?_⟩
  have hI1 : ∫ p : Torus d × Torus d, f p.1 ^ 2 * W (p.1 - p.2) ∂(volume.prod volume) =
      (∫ x, f x ^ 2) * ∫ z, W z := by
    rw [integral_prod _ hA]
    have : ∀ x : Torus d, ∫ y : Torus d, f x ^ 2 * W (x - y) = f x ^ 2 * ∫ z, W z := by
      intro x
      rw [integral_const_mul, integral_sub_left_eq_self W volume x]
    simp_rw [this]
    rw [integral_mul_const]
  have hI2 : ∫ p : Torus d × Torus d, g p.2 ^ 2 * W (p.1 - p.2) ∂(volume.prod volume) =
      (∫ x, g x ^ 2) * ∫ z, W z := by
    rw [integral_prod_symm _ hB]
    have : ∀ y : Torus d, ∫ x : Torus d, g y ^ 2 * W (x - y) = g y ^ 2 * ∫ z, W z := by
      intro y
      rw [integral_const_mul, integral_sub_right_eq_self W y]
    simp_rw [this]
    rw [integral_mul_const]
  calc ∫ p : Torus d × Torus d, W (p.1 - p.2) * (|f p.1| * |g p.2|) ∂(volume.prod volume)
      ≤ ∫ p : Torus d × Torus d, ((t / 2) * (f p.1 ^ 2 * W (p.1 - p.2)) +
          (t⁻¹ / 2) * (g p.2 ^ 2 * W (p.1 - p.2))) ∂(volume.prod volume) :=
        integral_mono hint ((hA.const_mul (t / 2)).add (hB.const_mul (t⁻¹ / 2))) hbound
    _ = (t / 2) * ((∫ x, f x ^ 2) * ∫ z, W z) + (t⁻¹ / 2) * ((∫ x, g x ^ 2) * ∫ z, W z) := by
        rw [integral_add (hA.const_mul (t / 2)) (hB.const_mul (t⁻¹ / 2)), integral_const_mul,
          integral_const_mul, hI1, hI2]
    _ = _ := by ring

/-- The commutator form with `L²` entries: integrability and the Schur bound. -/
theorem tlowv_L2_form {F : Torus d → Euc d} (hFm : Measurable F) (hodd : ∀ z, F (-z) = -F z)
    (hW : Integrable (tlowvW F)) {v : Torus d → Euc d} {L : ℝ} (hL : 0 ≤ L)
    (hv : IsLipschitzVF L v) (hvc : Continuous v) {f g : Torus d → ℝ}
    (hf : AEStronglyMeasurable f volume) (hg : AEStronglyMeasurable g volume)
    (hf2 : Integrable (fun x => f x ^ 2)) (hg2 : Integrable (fun x => g x ^ 2))
    {t : ℝ} (ht : 0 < t) :
    Integrable (fun p : Torus d × Torus d => commKernel F v p.1 p.2 * f p.1 * g p.2)
        (volume.prod volume) ∧
      |∫ p : Torus d × Torus d, commKernel F v p.1 p.2 * f p.1 * g p.2 ∂(volume.prod volume)| ≤
        L * ((t * (∫ x, f x ^ 2) + t⁻¹ * (∫ x, g x ^ 2)) / 2 * ∫ z, tlowvW F z) := by
  obtain ⟨hS1, hS2⟩ := tlowv_schur (tlowvW_measurable hFm) hW (tlowvW_nonneg F) (tlowvW_even hodd)
    hf hg hf2 hg2 ht
  have hKm := tlowv_commKernel_meas hFm hvc
  have hmeasf : AEStronglyMeasurable (fun p : Torus d × Torus d => f p.1) (volume.prod volume) :=
    hf.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst
  have hmeasg : AEStronglyMeasurable (fun p : Torus d × Torus d => g p.2) (volume.prod volume) :=
    hg.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd
  have hdom : Integrable (fun p : Torus d × Torus d =>
      L * (tlowvW F (p.1 - p.2) * (|f p.1| * |g p.2|))) (volume.prod volume) :=
    hS1.const_mul _
  have hbd : ∀ p : Torus d × Torus d, ‖commKernel F v p.1 p.2 * f p.1 * g p.2‖ ≤
      L * (tlowvW F (p.1 - p.2) * (|f p.1| * |g p.2|)) := by
    intro p
    rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs]
    calc |commKernel F v p.1 p.2| * |f p.1| * |g p.2|
        ≤ (L * tlowvW F (p.1 - p.2)) * |f p.1| * |g p.2| := by
          gcongr; exact tlowv_commKernel_abs hL hv F _ _
      _ = _ := by ring
  have hint : Integrable (fun p : Torus d × Torus d => commKernel F v p.1 p.2 * f p.1 * g p.2)
      (volume.prod volume) :=
    hdom.mono' ((hKm.aestronglyMeasurable.mul hmeasf).mul hmeasg) (Eventually.of_forall hbd)
  refine ⟨hint, ?_⟩
  rw [← Real.norm_eq_abs]
  calc ‖∫ p : Torus d × Torus d, commKernel F v p.1 p.2 * f p.1 * g p.2 ∂(volume.prod volume)‖
      ≤ ∫ p : Torus d × Torus d, L * (tlowvW F (p.1 - p.2) * (|f p.1| * |g p.2|))
          ∂(volume.prod volume) := norm_integral_le_of_norm_le hdom (Eventually.of_forall hbd)
    _ = L * ∫ p : Torus d × Torus d, tlowvW F (p.1 - p.2) * (|f p.1| * |g p.2|)
          ∂(volume.prod volume) := integral_const_mul _ _
    _ ≤ _ := by gcongr

/-- The iterated integral is the product integral. -/
lemma tlowv_CcommFun_eq {F : Torus d → Euc d} {v : Torus d → Euc d} {f : Torus d → ℝ}
    (h : Integrable (fun p : Torus d × Torus d => commKernel F v p.1 p.2 * f p.1 * f p.2)
      (volume.prod volume)) :
    CcommFunT F v f =
      ∫ p : Torus d × Torus d, commKernel F v p.1 p.2 * f p.1 * f p.2 ∂(volume.prod volume) := by
  unfold CcommFunT
  rw [integral_prod _ h]

/-- `L²`-continuity of the form `a ↦ 𝒞_F(v,a)`. -/
theorem tlowv_Ccomm_cont {F : Torus d → Euc d} (hFm : Measurable F) (hodd : ∀ z, F (-z) = -F z)
    (hW : Integrable (tlowvW F)) {v : Torus d → Euc d} {L : ℝ} (hL : 0 ≤ L)
    (hv : IsLipschitzVF L v) (hvc : Continuous v) {b b' : Torus d → ℝ}
    (hb : AEStronglyMeasurable b volume) (hb' : AEStronglyMeasurable b' volume)
    (hb2 : Integrable (fun x => b x ^ 2)) (hb'2 : Integrable (fun x => b' x ^ 2))
    {η : ℝ} (hη : 0 < η) (hδ : ∫ x, (b x - b' x) ^ 2 ≤ η ^ 2) :
    |CcommFunT F v b - CcommFunT F v b'| ≤
      L * (∫ z, tlowvW F z) * η * (2 + (∫ x, b x ^ 2) + ∫ x, b' x ^ 2) / 2 := by
  have hδm : AEStronglyMeasurable (fun x => b x - b' x) volume := hb.sub hb'
  have hδ2 : Integrable (fun x => (b x - b' x) ^ 2) := by
    refine ((hb2.const_mul 2).add (hb'2.const_mul 2)).mono' (hδm.pow 2)
      (Eventually.of_forall fun x => ?_)
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    simp only [Pi.add_apply]
    nlinarith [sq_nonneg (b x + b' x)]
  have hWn : ∀ z, 0 ≤ tlowvW F z := tlowvW_nonneg F
  have hW1 : 0 ≤ ∫ z, tlowvW F z := integral_nonneg hWn
  have hint : ∀ {f g : Torus d → ℝ}, AEStronglyMeasurable f volume → AEStronglyMeasurable g volume →
      Integrable (fun x => f x ^ 2) → Integrable (fun x => g x ^ 2) →
      Integrable (fun p : Torus d × Torus d => commKernel F v p.1 p.2 * f p.1 * g p.2)
        (volume.prod volume) := fun hf hg hf2 hg2 =>
    (tlowv_L2_form hFm hodd hW hL hv hvc hf hg hf2 hg2 one_pos).1
  have hrepr : ∀ {f : Torus d → ℝ}, AEStronglyMeasurable f volume → Integrable (fun x => f x ^ 2) →
      CcommFunT F v f =
        ∫ p : Torus d × Torus d, commKernel F v p.1 p.2 * f p.1 * f p.2 ∂(volume.prod volume) :=
    fun hf hf2 => tlowv_CcommFun_eq (hint hf hf hf2 hf2)
  have e1 := hint hδm hb hδ2 hb2
  have e2 := hint hb' hδm hb'2 hδ2
  have hdiff : CcommFunT F v b - CcommFunT F v b' =
      (∫ p : Torus d × Torus d, commKernel F v p.1 p.2 * (b p.1 - b' p.1) * b p.2
        ∂(volume.prod volume)) +
      ∫ p : Torus d × Torus d, commKernel F v p.1 p.2 * b' p.1 * (b p.2 - b' p.2)
        ∂(volume.prod volume) := by
    rw [hrepr hb hb2, hrepr hb' hb'2, ← integral_add e1 e2,
      ← integral_sub (hint hb hb hb2 hb2) (hint hb' hb' hb'2 hb'2)]
    refine integral_congr_ae (Eventually.of_forall fun p => ?_)
    ring
  have h1 := (tlowv_L2_form hFm hodd hW hL hv hvc hδm hb hδ2 hb2 (t := η⁻¹) (inv_pos.2 hη)).2
  have h2 := (tlowv_L2_form hFm hodd hW hL hv hvc hb' hδm hb'2 hδ2 (t := η) hη).2
  rw [inv_inv] at h1
  rw [hdiff]
  set Dδ := ∫ x, (b x - b' x) ^ 2 with hDδ
  set B2 := ∫ x, b x ^ 2 with hB2
  set B2' := ∫ x, b' x ^ 2 with hB2'
  set W1 := ∫ z, tlowvW F z with hW1def
  have hDη : η⁻¹ * Dδ ≤ η := by
    rw [inv_mul_le_iff₀ hη]; nlinarith
  refine (abs_add_le _ _).trans ?_
  have hb1 : (η⁻¹ * Dδ + η * B2) / 2 ≤ (η + η * B2) / 2 := by linarith
  have hb2' : (η * B2' + η⁻¹ * Dδ) / 2 ≤ (η * B2' + η) / 2 := by linarith
  calc _ ≤ L * ((η⁻¹ * Dδ + η * B2) / 2 * W1) + L * ((η * B2' + η⁻¹ * Dδ) / 2 * W1) :=
        add_le_add h1 h2
    _ ≤ L * ((η + η * B2) / 2 * W1) + L * ((η * B2' + η) / 2 * W1) := by gcongr
    _ = _ := by ring

end HRS.Commutator.TorusNote
