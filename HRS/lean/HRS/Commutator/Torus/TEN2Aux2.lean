import HRS.Commutator.Torus.TEN2Aux1
import HRS.PDE.Fourier

/-!
# Torus energy layer (packet T-EN2), helper part 2: the quadratic form of an `L¹` kernel

Prefix `ten2_`.  For `h ∈ L¹(𝕋^d)` with real Fourier coefficients `c k` and a bounded density `ρ`,
`∬ h(x-y)ρ(x)ρ(y) = ∑_k c_k |ρ̂(k)|²` (convolution theorem + Parseval, no summability of `c` needed).
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS.Commutator.TorusNote

open HRS

variable {d : ℕ}

theorem ten2_mode_zero_pt (k : Lattice d) : Torus.mode k (0 : Torus d) = 1 := by
  simp [Torus.mode, UnitAddTorus.mFourier]

theorem ten2_mode_neg_arg (k : Lattice d) (y : Torus d) :
    Torus.mode k (-y) = Torus.mode (-k) y := by
  have h := ten_mode_sub k 0 y
  rw [Torus.mode_neg]
  simpa [ten2_mode_zero_pt] using h

/-- `(x,y) ↦ h(x-y) ρ(y)` is integrable on the product. -/
theorem ten2_conv_integrable {h : Torus d → ℝ} (hh : Integrable h) {ρ : Torus d → ℝ}
    (hρ : BddDensityT ρ) : Integrable (fun p : Torus d × Torus d => h (p.1 - p.2) * ρ p.2) := by
  obtain ⟨B, hB⟩ := hρ.bdd
  have hρint : Integrable ρ :=
    ten_integrable_of_bdd (μ := volume) hρ.measurable B (fun x => by
      rw [Real.norm_eq_abs]; exact hB x)
  have hconv := MeasureTheory.Integrable.convolution_integrand (ContinuousLinearMap.mul ℝ ℝ) hρint hh
  refine hconv.congr (ae_of_all _ fun p => ?_)
  simp only [ContinuousLinearMap.mul_apply']
  ring

/-- The convolution `x ↦ ∫ h(x-y) ρ(y) dy`. -/
def ten2conv (h ρ : Torus d → ℝ) (x : Torus d) : ℝ := ∫ y, h (x - y) * ρ y

theorem ten2_conv_bound {h : Torus d → ℝ} (hh : Integrable h) {ρ : Torus d → ℝ}
    (hρ : BddDensityT ρ) : ∃ C : ℝ, ∀ x, ‖ten2conv h ρ x‖ ≤ C := by
  obtain ⟨B, hB⟩ := hρ.bdd
  refine ⟨B * ∫ z, ‖h z‖, fun x => ?_⟩
  have hg : Integrable (fun y => B * ‖h (x - y)‖) := (hh.norm.comp_sub_left x).const_mul B
  calc ‖ten2conv h ρ x‖ ≤ ∫ y, B * ‖h (x - y)‖ := by
        refine norm_integral_le_of_norm_le hg (ae_of_all _ fun y => ?_)
        rw [norm_mul, mul_comm]
        exact mul_le_mul_of_nonneg_right (by simpa [Real.norm_eq_abs] using hB y) (norm_nonneg _)
    _ = B * ∫ z, ‖h z‖ := by
        rw [integral_const_mul]
        congr 1
        exact integral_sub_left_eq_self (fun z => ‖h z‖) volume x

theorem ten2_conv_memLp {h : Torus d → ℝ} (hh : Integrable h) {ρ : Torus d → ℝ}
    (hρ : BddDensityT ρ) : MemLp (ten2conv h ρ) 2 volume := by
  obtain ⟨C, hC⟩ := ten2_conv_bound hh hρ
  have hm : AEStronglyMeasurable (ten2conv h ρ) volume :=
    (ten2_conv_integrable hh hρ).integral_prod_left.aestronglyMeasurable
  exact MemLp.of_bound hm C (ae_of_all _ hC)

/-- Convolution theorem: `fcoef (h * ρ) k = ĥ(k) ρ̂(k)`. -/
theorem ten2_fcoef_conv {h : Torus d → ℝ} (hh : Integrable h) {ρ : Torus d → ℝ}
    (hρ : BddDensityT ρ) (k : Lattice d) :
    Torus.fcoef (ten2conv h ρ) k = Torus.fcoef h k * Torus.fcoef ρ k := by
  have hJ := ten2_conv_integrable hh hρ
  set F : Torus d × Torus d → ℂ := fun p =>
    Torus.mode (-k) p.1 * (((h (p.1 - p.2) * ρ p.2 : ℝ)) : ℂ) with hF
  have hFi : Integrable F := by
    refine hJ.norm.mono' ?_ (ae_of_all _ fun p => ?_)
    · exact ((Torus.continuous_mode (-k)).comp continuous_fst).aestronglyMeasurable.mul
        (Complex.continuous_ofReal.comp_aestronglyMeasurable hJ.aestronglyMeasurable)
    · simp [hF, Torus.norm_mode]
  have hswap := integral_integral_swap (f := fun x y => F (x, y)) hFi
  have h1 : Torus.fcoef (ten2conv h ρ) k = ∫ x, ∫ y, F (x, y) := by
    unfold Torus.fcoef ten2conv
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp only [hF]
    rw [← integral_complex_ofReal (f := fun y => h (x - y) * ρ y), ← integral_const_mul]
  have h2 : ∀ y : Torus d, ∫ x, F (x, y) = Torus.fcoef h k * (Torus.mode (-k) y * (ρ y : ℂ)) := by
    intro y
    have e1 : ∀ x : Torus d, F (x, y) = (ρ y : ℂ) * (Torus.mode (-k) x * (h (x + -y) : ℂ)) := by
      intro x
      simp only [hF, sub_eq_add_neg]
      push_cast
      ring
    simp_rw [e1]
    rw [integral_const_mul, Torus.fcoef_translate h k (-y), ten2_mode_neg_arg]
    ring
  rw [h1, hswap]
  simp_rw [h2]
  rw [integral_const_mul]
  rfl

/-- The quadratic form of an `L¹` kernel with real coefficients `c`: `∬ h(x-y)ρ(x)ρ(y) = ∑ c_k |ρ̂(k)|²`. -/
theorem ten2_quadform {h : Torus d → ℝ} (hh : Integrable h) {ρ : Torus d → ℝ}
    (hρ : BddDensityT ρ) {c : Lattice d → ℝ} (hc : ∀ k, Torus.fcoef h k = (c k : ℂ)) :
    HasSum (fun k => c k * ‖Torus.fcoef ρ k‖ ^ 2) (∫ x, ∫ y, h (x - y) * ρ x * ρ y) := by
  obtain ⟨B, hB⟩ := hρ.bdd
  have hρm : MemLp ρ 2 volume :=
    MemLp.of_bound hρ.measurable.aestronglyMeasurable B
      (ae_of_all _ fun x => by simpa [Real.norm_eq_abs] using hB x)
  have hum := ten2_conv_memLp hh hρ
  have hP := HRS.PDE.hasSum_parseval (fun x => (ρ x : ℂ)) (fun x => (ten2conv h ρ x : ℂ))
    hρm.ofReal hum.ofReal
  have e1 : ∀ n : Lattice d, conj (Torus.funFourierCoeff (fun x => (ρ x : ℂ)) n) *
      Torus.funFourierCoeff (fun x => (ten2conv h ρ x : ℂ)) n = ((c n * ‖Torus.fcoef ρ n‖ ^ 2 : ℝ) : ℂ) := by
    intro n
    rw [← tpos_fcoef_eq_funFourier, ← tpos_fcoef_eq_funFourier, ten2_fcoef_conv hh hρ, hc]
    have : conj (Torus.fcoef ρ n) * ((c n : ℂ) * Torus.fcoef ρ n) =
        (c n : ℂ) * (conj (Torus.fcoef ρ n) * Torus.fcoef ρ n) := by ring
    rw [this, Complex.conj_mul']
    push_cast
    ring
  have e2 : ∫ t, conj ((ρ t : ℝ) : ℂ) * ((ten2conv h ρ t : ℝ) : ℂ) =
      ((∫ x, ∫ y, h (x - y) * ρ x * ρ y : ℝ) : ℂ) := by
    have : ∫ x, ∫ y, h (x - y) * ρ x * ρ y = ∫ t, ρ t * ten2conv h ρ t := by
      refine integral_congr_ae (ae_of_all _ fun x => ?_)
      show ∫ y, h (x - y) * ρ x * ρ y = ρ x * ∫ y, h (x - y) * ρ y
      rw [← integral_const_mul]
      exact integral_congr_ae (ae_of_all _ fun y => by ring)
    rw [this, ← integral_complex_ofReal (f := fun t => ρ t * ten2conv h ρ t)]
    exact integral_congr_ae (ae_of_all _ fun t => by simp)
  simp_rw [e1, e2] at hP
  exact Complex.hasSum_ofReal.1 hP

end HRS.Commutator.TorusNote
