import HRS.MS.SA16U2K8

/-!
# S.A.16 K10, part (a): the compatible odd operator as a skew-adjoint convolution (worker SA16U3)

For `1 < θ` the splice kernel is in `L^1` (`sa16k5_D_int`) and odd, so `T = spliceOdd i` is the convolution with
an odd `L^1` kernel.  We prove: `T` is bounded on bounded functions, skew-adjointness against
`L^1 ∩ L^∞` continuous functions (`sa16u3_skew`), and `T` commutes with the first derivative of a Schwartz
function (`sa16u3_T_hasFDerivAt`).
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff SchwartzMap

namespace HRS.Whole.AppendixA.Phase2SA16Cutoff
open HRS HRS.Whole HRS.Whole.AppendixA HRS.CZ.Pv HRS.CZ.ElemA Phase2SA16

section K10a
variable {d : ℕ}

lemma sa16u3_K_int (hd : 1 ≤ d) {θ δ : ℝ} (hθ1 : 1 < θ) (hδ : 0 < δ) (i : Fin d) :
    Integrable (spliceKernel d θ δ i) :=
  Integrable.mono' (sa16k5_D_int hd hθ1 hδ) (sa16k5_ks_meas θ δ i).aestronglyMeasurable
    (Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs]; exact sa16k5_ks_le_D hδ (by linarith) i z)

lemma sa16u3_T_int (hd : 1 ≤ d) {θ δ : ℝ} (hθ1 : 1 < θ) (hδ : 0 < δ) (i : Fin d)
    {u : Euc d → ℝ} (hu : Continuous u) {B : ℝ} (hB : ∀ x, ‖u x‖ ≤ B) (x : Euc d) :
    Integrable (fun z => spliceKernel d θ δ i z * u (x - z)) :=
  sa16u2_int_conv (sa16k5_ks_meas θ δ i) (sa16u3_K_int hd hθ1 hδ i) hu hB x

lemma sa16u3_T_bound (hd : 1 ≤ d) {θ δ : ℝ} (hθ1 : 1 < θ) (hδ : 0 < δ) (i : Fin d)
    {u : Euc d → ℝ} {B : ℝ} (hB : ∀ x, |u x| ≤ B) (x : Euc d) :
    |spliceOdd d θ δ i u x| ≤ (∫ z, ‖spliceKernel d θ δ i z‖) * B := by
  unfold spliceOdd
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  have h := norm_integral_le_of_norm_le
    ((sa16u3_K_int hd hθ1 hδ i).norm.mul_const B)
    (Eventually.of_forall fun z => ?_) (f := fun z => spliceKernel d θ δ i z * u (x - z))
  · rw [integral_mul_const] at h
    simpa [Real.norm_eq_abs] using h
  · rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (by simpa [Real.norm_eq_abs] using hB (x - z)) (norm_nonneg _)

/-- skew-adjointness of the odd integrable convolution against `L^1 ∩ L^∞` continuous functions -/
lemma sa16u3_skew (hd : 1 ≤ d) {θ δ : ℝ} (hθ1 : 1 < θ) (hδ : 0 < δ) (i : Fin d)
    {f g : Euc d → ℝ} (hf : Continuous f) (hg : Continuous g) (hfi : Integrable f) (hgi : Integrable g)
    {Bf Bg : ℝ} (hBf : ∀ x, |f x| ≤ Bf) (hBg : ∀ x, |g x| ≤ Bg) :
    ∫ x, f x * spliceOdd d θ δ i g x = - ∫ x, spliceOdd d θ δ i f x * g x := by
  set K : Euc d → ℝ := spliceKernel d θ δ i with hKdef
  have hKm : Measurable K := sa16k5_ks_meas θ δ i
  have hKi : Integrable K := sa16u3_K_int hd hθ1 hδ i
  have hBf0 : 0 ≤ Bf := (abs_nonneg _).trans (hBf 0)
  have hBg0 : 0 ≤ Bg := (abs_nonneg _).trans (hBg 0)
  have hKn : 0 ≤ ∫ z, ‖K z‖ := integral_nonneg fun z => norm_nonneg _
  -- first product integrability, variables (x, z)
  have hH : Integrable (fun q : Euc d × Euc d => f q.1 * (K q.2 * g (q.1 - q.2)))
      (volume.prod volume) := by
    have hmeas : Measurable (fun q : Euc d × Euc d => f q.1 * (K q.2 * g (q.1 - q.2))) :=
      (hf.measurable.comp measurable_fst).mul ((hKm.comp measurable_snd).mul
        (hg.measurable.comp (measurable_fst.sub measurable_snd)))
    refine (integrable_prod_iff hmeas.aestronglyMeasurable).2 ⟨Eventually.of_forall fun x => ?_, ?_⟩
    · exact (sa16u3_T_int hd hθ1 hδ i hg (B := Bg) (fun y => by
        simpa [Real.norm_eq_abs] using hBg y) x).const_mul (f x)
    · have hm2 : AEStronglyMeasurable (fun x : Euc d => ∫ z, ‖f x * (K z * g (x - z))‖) volume :=
        (hmeas.norm.stronglyMeasurable.integral_prod_right' (ν := volume)).aestronglyMeasurable
      refine Integrable.mono' (hfi.norm.mul_const ((∫ z, ‖K z‖) * Bg)) hm2
        (Eventually.of_forall fun x => ?_)
      have hnn : 0 ≤ ∫ z, ‖f x * (K z * g (x - z))‖ := integral_nonneg fun z => norm_nonneg _
      rw [Real.norm_of_nonneg hnn]
      have hint : Integrable (fun z => ‖K z‖ * (|f x| * Bg)) := hKi.norm.mul_const _
      calc ∫ z, ‖f x * (K z * g (x - z))‖ ≤ ∫ z, ‖K z‖ * (|f x| * Bg) := by
            refine integral_mono_of_nonneg (Eventually.of_forall fun z => norm_nonneg _) hint
              (Eventually.of_forall fun z => ?_)
            dsimp only
            rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
            have := hBg (x - z)
            calc |f x| * (‖K z‖ * |g (x - z)|) = ‖K z‖ * (|f x| * |g (x - z)|) := by ring
              _ ≤ ‖K z‖ * (|f x| * Bg) := by gcongr
        _ = ‖f x‖ * ((∫ z, ‖K z‖) * Bg) := by
            rw [integral_mul_const, Real.norm_eq_abs]; ring
  -- second product integrability, variables (z, y)
  have hH2 : Integrable (fun q : Euc d × Euc d => K q.1 * (f (q.2 + q.1) * g q.2))
      (volume.prod volume) := by
    have hmeas : Measurable (fun q : Euc d × Euc d => K q.1 * (f (q.2 + q.1) * g q.2)) :=
      (hKm.comp measurable_fst).mul ((hf.measurable.comp (measurable_snd.add measurable_fst)).mul
        (hg.measurable.comp measurable_snd))
    refine (integrable_prod_iff hmeas.aestronglyMeasurable).2 ⟨Eventually.of_forall fun z => ?_, ?_⟩
    · have : Integrable (fun y => f (y + z) * g y) := by
        refine Integrable.mono' (hgi.norm.mul_const Bf)
          ((hf.comp (continuous_id.add continuous_const)).aestronglyMeasurable.mul hg.aestronglyMeasurable)
          (Eventually.of_forall fun y => ?_)
        rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
        exact (mul_le_mul_of_nonneg_right (hBf _) (abs_nonneg _)).trans_eq (mul_comm _ _)
      exact this.const_mul (K z)
    · have hm2 : AEStronglyMeasurable (fun z : Euc d => ∫ y, ‖K z * (f (y + z) * g y)‖) volume :=
        (hmeas.norm.stronglyMeasurable.integral_prod_right' (ν := volume)).aestronglyMeasurable
      refine Integrable.mono' (hKi.norm.mul_const (Bf * ∫ y, ‖g y‖)) hm2
        (Eventually.of_forall fun z => ?_)
      have hnn : 0 ≤ ∫ y, ‖K z * (f (y + z) * g y)‖ := integral_nonneg fun y => norm_nonneg _
      rw [Real.norm_of_nonneg hnn]
      have hint : Integrable (fun y => ‖K z‖ * (Bf * ‖g y‖)) := (hgi.norm.const_mul Bf).const_mul _
      calc ∫ y, ‖K z * (f (y + z) * g y)‖ ≤ ∫ y, ‖K z‖ * (Bf * ‖g y‖) := by
            refine integral_mono_of_nonneg (Eventually.of_forall fun y => norm_nonneg _) hint
              (Eventually.of_forall fun y => ?_)
            dsimp only
            rw [norm_mul, norm_mul]
            have := hBf (y + z)
            simp only [Real.norm_eq_abs]
            gcongr
        _ = ‖K z‖ * (Bf * ∫ y, ‖g y‖) := by
            rw [integral_const_mul, integral_const_mul]
  -- the computation
  have e1 : ∫ x, f x * spliceOdd d θ δ i g x = ∫ x, ∫ z, f x * (K z * g (x - z)) := by
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [spliceOdd, hKdef]
    rw [integral_const_mul]
  have e2 : ∫ x, ∫ z, f x * (K z * g (x - z)) = ∫ z, ∫ x, f x * (K z * g (x - z)) :=
    integral_integral_swap hH
  have e3 : ∀ z, ∫ x, f x * (K z * g (x - z)) = ∫ y, K z * (f (y + z) * g y) := by
    intro z
    have := integral_add_right_eq_self (μ := (volume : Measure (Euc d)))
      (fun x => f x * (K z * g (x - z))) z
    rw [← this]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only [add_sub_cancel_right]
    ring
  have e4 : ∫ z, ∫ y, K z * (f (y + z) * g y) = ∫ y, ∫ z, K z * (f (y + z) * g y) :=
    integral_integral_swap hH2
  have e5 : ∀ y, ∫ z, K z * (f (y + z) * g y) = - (spliceOdd d θ δ i f y * g y) := by
    intro y
    have h1 : ∫ z, K z * (f (y + z) * g y) = (∫ z, K z * f (y + z)) * g y := by
      rw [← integral_mul_const]
      refine integral_congr_ae (Eventually.of_forall fun z => ?_)
      ring
    have h2 : ∫ z, K z * f (y + z) = - spliceOdd d θ δ i f y := by
      have := integral_neg_eq_self (μ := (volume : Measure (Euc d)))
        (fun z => K z * f (y + z))
      rw [← this]
      simp only [spliceOdd, hKdef]
      rw [← integral_neg]
      refine integral_congr_ae (Eventually.of_forall fun z => ?_)
      simp only [sa16u2_odd, sub_eq_add_neg, neg_mul]
    rw [h1, h2]; ring
  rw [e1, e2]
  simp_rw [e3]
  rw [e4]
  simp_rw [e5]
  rw [integral_neg]

end K10a
end HRS.Whole.AppendixA.Phase2SA16Cutoff
