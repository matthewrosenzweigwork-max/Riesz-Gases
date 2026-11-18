import HRS.MS.S111K4P2
import HRS.MS.S111X1G2

/-!
# S11.1 / T03 (S11K4), packet `R26-T6C.P06` (part 1): the commutator splitting of the interaction term

For bounded measurable data, `∫ ρ u ⟨a, W[v]⟩ + ∫ ρ v ⟨a, W[u]⟩ = ∬ ρ(x)ρ(y) ⟨a(x) - a(y), ∇g(x-y)⟩ u(x) v(y)`.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S111K4

open HRS HRS.Whole
open HRS.MS.S111X1 (KData Wf Wf_bdd Wf_meas nl_swap plain_integrable kG_weighted kA kG_measurable)

variable {d : ℕ}

theorem k4_commutator_split {s : ℝ} {ρ : Euc d → ℝ} {M : ℝ} (K : KData d s ρ M) {a : Euc d → Euc d}
    (ham : Measurable a) {Ba : ℝ} (hBa : ∀ y, ‖a y‖ ≤ Ba) {u v : Euc d → ℝ} (hum : Measurable u)
    {Bu : ℝ} (hBu : ∀ x, |u x| ≤ Bu) (hvm : Measurable v) {Bv : ℝ} (hBv : ∀ x, |v x| ≤ Bv) :
    (∫ x, ρ x * (u x * inner ℝ (a x) (Wf d s ρ v x))) + (∫ x, ρ x * (v x * inner ℝ (a x) (Wf d s ρ u x))) =
      ∫ x, ρ x * ∫ y, ρ y * (inner ℝ (a x - a y) (rieszKernelGrad d s (x - y)) * u x * v y) := by
  have hBa0 : 0 ≤ Ba := (norm_nonneg _).trans (hBa 0)
  have hBu0 : 0 ≤ Bu := (abs_nonneg _).trans (hBu 0)
  have hBv0 : 0 ≤ Bv := (abs_nonneg _).trans (hBv 0)
  have hA0 := HRS.MS.S111X1.kA_nonneg K
  -- the swap identity
  have hvam : Measurable fun y => v y • a y := hvm.smul ham
  have hBva : ∀ y, ‖v y • a y‖ ≤ Bv * Ba := fun y => by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul (hBv y) (hBa y) (norm_nonneg _) hBv0
  have hsw := nl_swap K hvam hBva hum hBu
  -- the fixed-x identity
  have hfix : ∀ x, ∫ y, ρ y * (inner ℝ (a x - a y) (rieszKernelGrad d s (x - y)) * u x * v y) =
      u x * inner ℝ (a x) (Wf d s ρ v x) - u x * ∫ y, ρ y * inner ℝ (v y • a y) (rieszKernelGrad d s (x - y)) := by
    intro x
    have hvρ : ∀ y, |v y * ρ y| ≤ Bv * ρ y := fun y => by
      rw [abs_mul, abs_of_nonneg (K.nonneg y)]
      exact mul_le_mul_of_nonneg_right (hBv y) (K.nonneg y)
    have hint : Integrable (fun y => (v y * ρ y) • rieszKernelGrad d s (x - y)) :=
      plain_integrable K.hd K.hs0 K.hs1 K.meas K.nonneg K.int K.bdd (hvm.mul K.meas) hvρ x
    have hint1 : Integrable (fun y => inner ℝ (a x) ((v y * ρ y) • rieszKernelGrad d s (x - y))) :=
      (innerSL ℝ (a x)).integrable_comp hint
    have hint2 : Integrable (fun y => ρ y * inner ℝ (v y • a y) (rieszKernelGrad d s (x - y))) := by
      have hw := (kG_weighted K.hd K.hs0 K.hs1 K.meas K.nonneg K.int K.bdd x).1
      refine (hw.const_mul (Bv * Ba)).mono' ?_ (Filter.Eventually.of_forall fun y => ?_)
      · exact K.meas.aestronglyMeasurable.mul ((hvam.inner ((kG_measurable s).comp
          (measurable_const.sub measurable_id))).aestronglyMeasurable)
      · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (K.nonneg y)]
        have h1 : |inner ℝ (v y • a y) (rieszKernelGrad d s (x - y))| ≤
            Bv * Ba * ‖rieszKernelGrad d s (x - y)‖ :=
          (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (hBva y) (norm_nonneg _))
        calc ρ y * |inner ℝ (v y • a y) (rieszKernelGrad d s (x - y))|
            ≤ ρ y * (Bv * Ba * ‖rieszKernelGrad d s (x - y)‖) := mul_le_mul_of_nonneg_left h1 (K.nonneg y)
          _ = Bv * Ba * (ρ y * ‖rieszKernelGrad d s (x - y)‖) := by ring
    have e : ∀ y, ρ y * (inner ℝ (a x - a y) (rieszKernelGrad d s (x - y)) * u x * v y) =
        u x * inner ℝ (a x) ((v y * ρ y) • rieszKernelGrad d s (x - y)) -
          u x * (ρ y * inner ℝ (v y • a y) (rieszKernelGrad d s (x - y))) := fun y => by
      rw [inner_sub_left, inner_smul_right, inner_smul_left]
      simp only [conj_trivial]
      ring
    simp_rw [e]
    rw [integral_sub (hint1.const_mul _) (hint2.const_mul _), integral_const_mul, integral_const_mul]
    congr 2
    unfold Wf
    rw [integral_inner hint]
  set Iy : Euc d → ℝ := fun x => ∫ y, ρ y * inner ℝ (v y • a y) (rieszKernelGrad d s (x - y)) with hIy
  have hfix' : ∀ x, ∫ y, ρ y * (inner ℝ (a x - a y) (rieszKernelGrad d s (x - y)) * u x * v y) =
      u x * inner ℝ (a x) (Wf d s ρ v x) - u x * Iy x := hfix
  simp_rw [hfix']
  have hIym : Measurable Iy := by
    have : Measurable fun p : Euc d × Euc d =>
        ρ p.2 * inner ℝ (v p.2 • a p.2) (rieszKernelGrad d s (p.1 - p.2)) :=
      (K.meas.comp measurable_snd).mul (Measurable.inner (hvam.comp measurable_snd)
        ((kG_measurable s).comp (measurable_fst.sub measurable_snd)))
    exact (this.stronglyMeasurable.integral_prod_right').measurable
  have hIyb : ∀ x, |Iy x| ≤ Bv * Ba * kA d s M ρ := fun x => by
    have hw := kG_weighted K.hd K.hs0 K.hs1 K.meas K.nonneg K.int K.bdd x
    simp only [hIy]
    rw [← Real.norm_eq_abs]
    refine (norm_integral_le_of_norm_le (hw.1.const_mul (Bv * Ba)) (Filter.Eventually.of_forall fun y => ?_)).trans ?_
    · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (K.nonneg y)]
      have h1 : |inner ℝ (v y • a y) (rieszKernelGrad d s (x - y))| ≤
          Bv * Ba * ‖rieszKernelGrad d s (x - y)‖ :=
        (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (hBva y) (norm_nonneg _))
      calc ρ y * |inner ℝ (v y • a y) (rieszKernelGrad d s (x - y))|
          ≤ ρ y * (Bv * Ba * ‖rieszKernelGrad d s (x - y)‖) := mul_le_mul_of_nonneg_left h1 (K.nonneg y)
        _ = Bv * Ba * (ρ y * ‖rieszKernelGrad d s (x - y)‖) := by ring
    · rw [integral_const_mul]
      exact mul_le_mul_of_nonneg_left hw.2 (mul_nonneg hBv0 hBa0)
  have hI1 : Integrable (fun x => ρ x * (u x * inner ℝ (a x) (Wf d s ρ v x))) := by
    refine (K.int.mul_const (Bu * (Ba * (kA d s M ρ * Bv)))).mono' ?_ (Filter.Eventually.of_forall fun x => ?_)
    · exact K.meas.aestronglyMeasurable.mul ((hum.mul (Measurable.inner ham (Wf_meas K hvm))).aestronglyMeasurable)
    · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (K.nonneg x), abs_mul]
      have h1 : |inner ℝ (a x) (Wf d s ρ v x)| ≤ Ba * (kA d s M ρ * Bv) :=
        (abs_real_inner_le_norm _ _).trans (mul_le_mul (hBa x) (Wf_bdd K hBv x) (norm_nonneg _) hBa0)
      calc ρ x * (|u x| * |inner ℝ (a x) (Wf d s ρ v x)|)
          ≤ ρ x * (Bu * (Ba * (kA d s M ρ * Bv))) :=
            mul_le_mul_of_nonneg_left (mul_le_mul (hBu x) h1 (abs_nonneg _) hBu0) (K.nonneg x)
        _ = _ := by ring
  have hI2 : Integrable (fun x => ρ x * (u x * Iy x)) := by
    refine (K.int.mul_const (Bu * (Bv * Ba * kA d s M ρ))).mono' ?_ (Filter.Eventually.of_forall fun x => ?_)
    · exact K.meas.aestronglyMeasurable.mul ((hum.mul hIym).aestronglyMeasurable)
    · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (K.nonneg x), abs_mul]
      calc ρ x * (|u x| * |Iy x|) ≤ ρ x * (Bu * (Bv * Ba * kA d s M ρ)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul (hBu x) (hIyb x) (abs_nonneg _) hBu0) (K.nonneg x)
        _ = _ := by ring
  have e1 : ∀ x, ρ x * (u x * inner ℝ (a x) (Wf d s ρ v x) - u x * Iy x) =
      ρ x * (u x * inner ℝ (a x) (Wf d s ρ v x)) - u x * ρ x * Iy x := fun x => by ring
  simp_rw [e1]
  have hI2' : Integrable (fun x => u x * ρ x * Iy x) := hI2.congr (Filter.Eventually.of_forall fun x => by ring)
  rw [integral_sub hI1 hI2', show (∫ x, u x * ρ x * Iy x) =
      -∫ y, ρ y * (v y * inner ℝ (a y) (Wf d s ρ u y)) from ?_]
  · ring
  · rw [show (∫ x, u x * ρ x * Iy x) = ∫ x, u x * ρ x * ∫ y, ρ y * inner ℝ (v y • a y) (rieszKernelGrad d s (x - y)) from rfl,
      hsw]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [inner_smul_left, conj_trivial]

end HRS.MS.S111K4
