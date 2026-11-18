import HRS.MS.SpecAux14

/-!
# S8P: the double-integral bound for the kernel `g(x-y) √ρ(x) √ρ(y)` on `L²` (S8.7, packet E0)

Namespace `HRS.MS.Spec`, helper prefix `s8p_`.  With `C = M·∫_{B_1} g + 1`:
`∬ g(x-y) √ρ(x) √ρ(y) |v(x)| |w(y)| ≤ (C/2)(∫ v² + ∫ w²)` (`s8p_schur_double`), whence integrability of
`g(x-y) √ρ(x) √ρ(y) v(x) w(y)` for `v, w ∈ L²` (`s8p_kern_integrable`).
-/

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace HRS.MS.Spec

open HRS HRS.Whole

variable {d : ℕ}

/-- The symmetric kernel `g(x-y) √ρ(x) √ρ(y)`. -/
def s8p_kern (d : ℕ) (s : ℝ) (ρ : Euc d → ℝ) (p : Euc d × Euc d) : ℝ :=
  rieszKernel d s (p.1 - p.2) * (Real.sqrt (ρ p.1) * Real.sqrt (ρ p.2))

theorem s8p_kern_nonneg {s : ℝ} (hs0 : 0 < s) (ρ : Euc d → ℝ) (p : Euc d × Euc d) :
    0 ≤ s8p_kern d s ρ p :=
  mul_nonneg (s8p_riesz_nonneg hs0 _) (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))

theorem s8p_kern_meas (s : ℝ) {ρ : Euc d → ℝ} (hρm : Measurable ρ) :
    Measurable (s8p_kern d s ρ) := by
  unfold s8p_kern
  exact ((s8p_riesz_meas s).comp (measurable_fst.sub measurable_snd)).mul
    ((hρm.comp measurable_fst).sqrt.mul (hρm.comp measurable_snd).sqrt)

theorem s8p_schur_double {s : ℝ} (hs0 : 0 < s) (hsd : s < d) (ρ : Euc d → ℝ) (hρm : Measurable ρ)
    (hρ0 : ∀ x, 0 ≤ ρ x) {M : ℝ} (hM : ∀ x, ρ x ≤ M) (hint : Integrable ρ) (hone : ∫ x, ρ x = 1)
    (v w : Euc d → ℝ) (hv : AEMeasurable v) (hw : AEMeasurable w) :
    ∫⁻ p : Euc d × Euc d, ENNReal.ofReal (s8p_kern d s ρ p * (|v p.1| * |w p.2|))
        ∂(volume.prod volume) ≤
      (ENNReal.ofReal M * s8p_Iball d s + 1) *
        ((∫⁻ x, ENNReal.ofReal (v x ^ 2)) + ∫⁻ x, ENNReal.ofReal (w x ^ 2)) := by
  set C : ℝ≥0∞ := ENNReal.ofReal M * s8p_Iball d s + 1 with hC
  have hCtop : C ≠ ⊤ := by
    have h1 : s8p_Iball d s < ⊤ := s8p_Iball_lt_top hs0.le hsd
    exact ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top h1.ne, ENNReal.one_ne_top⟩
  have hgm : Measurable fun p : Euc d × Euc d => rieszKernel d s (p.1 - p.2) :=
    (s8p_riesz_meas s).comp (measurable_fst.sub measurable_snd)
  have hv1 : AEMeasurable (fun p : Euc d × Euc d => v p.1) (volume.prod volume) :=
    hv.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst
  have hw2 : AEMeasurable (fun p : Euc d × Euc d => w p.2) (volume.prod volume) :=
    hw.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd
  have hρ1 : Measurable fun p : Euc d × Euc d => ρ p.1 := hρm.comp measurable_fst
  have hρ2 : Measurable fun p : Euc d × Euc d => ρ p.2 := hρm.comp measurable_snd
  -- pointwise bound
  have hpt : ∀ p : Euc d × Euc d, ENNReal.ofReal (s8p_kern d s ρ p * (|v p.1| * |w p.2|)) ≤
      ENNReal.ofReal (rieszKernel d s (p.1 - p.2) * v p.1 ^ 2 * ρ p.2) +
        ENNReal.ofReal (rieszKernel d s (p.1 - p.2) * w p.2 ^ 2 * ρ p.1) := by
    intro p
    have hg := s8p_riesz_nonneg hs0 (p.1 - p.2)
    have h1 := hρ0 p.1
    have h2 := hρ0 p.2
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    unfold s8p_kern
    set a := |v p.1| * Real.sqrt (ρ p.2) with ha
    set b := |w p.2| * Real.sqrt (ρ p.1) with hb
    have hab : (Real.sqrt (ρ p.1) * Real.sqrt (ρ p.2)) * (|v p.1| * |w p.2|) = a * b := by
      rw [ha, hb]; ring
    have ha2 : a ^ 2 = v p.1 ^ 2 * ρ p.2 := by
      rw [ha, mul_pow, sq_abs, Real.sq_sqrt h2]
    have hb2 : b ^ 2 = w p.2 ^ 2 * ρ p.1 := by
      rw [hb, mul_pow, sq_abs, Real.sq_sqrt h1]
    have : rieszKernel d s (p.1 - p.2) * (Real.sqrt (ρ p.1) * Real.sqrt (ρ p.2)) *
        (|v p.1| * |w p.2|) = rieszKernel d s (p.1 - p.2) * (a * b) := by
      rw [← hab]; ring
    rw [this]
    have hab' : a * b ≤ a ^ 2 + b ^ 2 := by nlinarith [sq_nonneg (a - b), sq_nonneg a, sq_nonneg b]
    calc rieszKernel d s (p.1 - p.2) * (a * b) ≤ rieszKernel d s (p.1 - p.2) * (a ^ 2 + b ^ 2) :=
          mul_le_mul_of_nonneg_left hab' hg
      _ = _ := by rw [ha2, hb2]; ring
  refine (lintegral_mono hpt).trans ?_
  have hm1 : AEMeasurable (fun p : Euc d × Euc d =>
      ENNReal.ofReal (rieszKernel d s (p.1 - p.2) * v p.1 ^ 2 * ρ p.2)) (volume.prod volume) :=
    ENNReal.measurable_ofReal.comp_aemeasurable
      (((hgm.aemeasurable.mul (hv1.pow_const 2)).mul hρ2.aemeasurable))
  rw [lintegral_add_left' hm1]
  have hT1 : ∫⁻ p : Euc d × Euc d, ENNReal.ofReal (rieszKernel d s (p.1 - p.2) * v p.1 ^ 2 * ρ p.2)
      ∂(volume.prod volume) ≤ C * ∫⁻ x, ENNReal.ofReal (v x ^ 2) := by
    rw [lintegral_prod _ hm1]
    calc ∫⁻ x, ∫⁻ y, ENNReal.ofReal (rieszKernel d s (x - y) * v x ^ 2 * ρ y)
        ≤ ∫⁻ x, ENNReal.ofReal (v x ^ 2) * C := by
          refine lintegral_mono fun x => ?_
          have : ∀ y, ENNReal.ofReal (rieszKernel d s (x - y) * v x ^ 2 * ρ y) =
              ENNReal.ofReal (v x ^ 2) * ENNReal.ofReal (rieszKernel d s (x - y) * ρ y) := by
            intro y
            rw [← ENNReal.ofReal_mul (sq_nonneg _)]; congr 1; ring
          simp_rw [this]
          have hmeas : Measurable fun y => ENNReal.ofReal (rieszKernel d s (x - y) * ρ y) :=
            ENNReal.measurable_ofReal.comp
              (((s8p_riesz_meas s).comp (measurable_const.sub measurable_id)).mul hρm)
          rw [lintegral_const_mul _ hmeas]
          exact mul_le_mul_right (s8p_schur_sup hs0 ρ hρm hρ0 hM hint hone x) _
      _ = C * ∫⁻ x, ENNReal.ofReal (v x ^ 2) := by
          rw [lintegral_mul_const' _ _ hCtop, mul_comm]
  have hm2 : AEMeasurable (fun p : Euc d × Euc d =>
      ENNReal.ofReal (rieszKernel d s (p.1 - p.2) * w p.2 ^ 2 * ρ p.1)) (volume.prod volume) :=
    ENNReal.measurable_ofReal.comp_aemeasurable
      (((hgm.aemeasurable.mul (hw2.pow_const 2)).mul hρ1.aemeasurable))
  have hT2 : ∫⁻ p : Euc d × Euc d, ENNReal.ofReal (rieszKernel d s (p.1 - p.2) * w p.2 ^ 2 * ρ p.1)
      ∂(volume.prod volume) ≤ C * ∫⁻ y, ENNReal.ofReal (w y ^ 2) := by
    rw [lintegral_prod_symm _ hm2]
    calc ∫⁻ y, ∫⁻ x, ENNReal.ofReal (rieszKernel d s (x - y) * w y ^ 2 * ρ x)
        ≤ ∫⁻ y, ENNReal.ofReal (w y ^ 2) * C := by
          refine lintegral_mono fun y => ?_
          have : ∀ x, ENNReal.ofReal (rieszKernel d s (x - y) * w y ^ 2 * ρ x) =
              ENNReal.ofReal (w y ^ 2) * ENNReal.ofReal (rieszKernel d s (y - x) * ρ x) := by
            intro x
            rw [← ENNReal.ofReal_mul (sq_nonneg _)]
            have hneg : rieszKernel d s (x - y) = rieszKernel d s (y - x) := by
              rw [← rieszKernel_neg (d := d) (s := s) (y - x), neg_sub]
            rw [hneg]; congr 1; ring
          simp_rw [this]
          have hmeas : Measurable fun x => ENNReal.ofReal (rieszKernel d s (y - x) * ρ x) :=
            ENNReal.measurable_ofReal.comp
              (((s8p_riesz_meas s).comp (measurable_const.sub measurable_id)).mul hρm)
          rw [lintegral_const_mul _ hmeas]
          exact mul_le_mul_right (s8p_schur_sup hs0 ρ hρm hρ0 hM hint hone y) _
      _ = C * ∫⁻ y, ENNReal.ofReal (w y ^ 2) := by
          rw [lintegral_mul_const' _ _ hCtop, mul_comm]
  calc _ ≤ (C * ∫⁻ x, ENNReal.ofReal (v x ^ 2)) + C * ∫⁻ y, ENNReal.ofReal (w y ^ 2) :=
        add_le_add hT1 hT2
    _ = _ := by rw [mul_add]

end HRS.MS.Spec
