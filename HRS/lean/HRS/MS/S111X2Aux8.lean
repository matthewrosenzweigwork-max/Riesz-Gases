import HRS.MS.S111X2Aux7
import HRS.MS.S111X2Aux5

/-!
# S11.1 X2, packet E02 (part 3): the thermal data `TD` and the pointwise structure of the generator

`TD` collects the analytic facts about the thermal reference used by E02/E03.  `s111x2_gen_split`:
`G h = -β⁻¹ L h + N h` with `L = -Δ - ρ⁻¹∇ρ·∇` and `N h = Nnl d s ρ (∇h)` (the nonlocal term).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S111X2

open HRS HRS.Whole
open HRS.MS.S111X1 (EnData KData Nnl)

variable {d : ℕ}

/-- Analytic facts about the thermal reference used for the response calculus. -/
structure TD (d : ℕ) (s β : ℝ) (ρ : Euc d → ℝ) (M : ℝ) (C : WholeCoeff d) : Prop where
  en : EnData d s β ρ M C
  pos : ∀ x, 0 < ρ x
  gauss : ∃ C0 c : ℝ, 0 ≤ C0 ∧ 0 < c ∧ (∀ y, |ρ y| ≤ C0 * Real.exp (-c * ‖y‖ ^ 2)) ∧
    (∀ y, ‖fderiv ℝ ρ y‖ ≤ C0 * Real.exp (-c * ‖y‖ ^ 2))
  mom2 : Integrable (fun x => ‖x‖ ^ 2 * ρ x)
  one : ∫ x, ρ x = 1
  uniq : ∀ (ψ h1 h2 : Euc d → ℝ),
    HRS.Whole.IsResponse (HRS.Whole.rieszKernel d s) (HRS.Whole.withDensityReal ρ) β ψ h1 →
    HRS.Whole.IsResponse (HRS.Whole.rieszKernel d s) (HRS.Whole.withDensityReal ρ) β ψ h2 →
    h1 =ᵐ[HRS.Whole.withDensityReal ρ] h2

/-- The weighted operator `L h = -Δh - ρ⁻¹ ⟨∇ρ,∇h⟩`. -/
def s111x2_L (ρ : Euc d → ℝ) (h : Euc d → ℝ) (x : Euc d) : ℝ :=
  -Laplacian.laplacian h x - (ρ x)⁻¹ * inner ℝ (gradient ρ x) (gradient h x)

/-- `C²` data with bounded first and second derivatives. -/
structure CbD (h : Euc d → ℝ) (B1 B2 : ℝ) : Prop where
  smooth : ContDiff ℝ 2 h
  d1 : ∀ x, ‖fderiv ℝ h x‖ ≤ B1
  d2 : ∀ x, ‖fderiv ℝ (fderiv ℝ h) x‖ ≤ B2

theorem CbD.B1_nonneg {h : Euc d → ℝ} {B1 B2 : ℝ} (H : CbD h B1 B2) : 0 ≤ B1 :=
  (norm_nonneg _).trans (H.d1 0)

theorem CbD.B2_nonneg {h : Euc d → ℝ} {B1 B2 : ℝ} (H : CbD h B1 B2) : 0 ≤ B2 :=
  (norm_nonneg (fderiv ℝ (fderiv ℝ h) 0)).trans (H.d2 0)

theorem s111x2_gradient_continuous {h : Euc d → ℝ} (hh : ContDiff ℝ 1 h) : Continuous (gradient h) := by
  have : Continuous fun x => (InnerProductSpace.toDual ℝ (Euc d)).symm (fderiv ℝ h x) :=
    (InnerProductSpace.toDual ℝ (Euc d)).symm.continuous.comp (hh.continuous_fderiv (by norm_num))
  exact this

theorem s111x2_norm_gradient {h : Euc d → ℝ} (x : Euc d) : ‖gradient h x‖ = ‖fderiv ℝ h x‖ := by
  simp [gradient]

/-- The Laplacian of a `C²` function with bounded second derivative is bounded by `d B2`. -/
theorem s111x2_laplacian_bound {h : Euc d → ℝ} {B1 B2 : ℝ} (H : CbD h B1 B2) (x : Euc d) :
    |Laplacian.laplacian h x| ≤ d * B2 := by
  set b := EuclideanSpace.basisFun (Fin d) ℝ with hb
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis h b]
  simp only [iteratedFDeriv_two_apply]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have : ∀ i : Fin d, |fderiv ℝ (fderiv ℝ h) x (b i) (b i)| ≤ B2 := fun i => by
    have h3 := (fderiv ℝ (fderiv ℝ h) x).le_opNorm₂ (b i) (b i)
    rw [b.norm_eq_one i, mul_one, mul_one] at h3
    rw [← Real.norm_eq_abs]
    exact h3.trans (H.d2 x)
  calc ∑ i : Fin d, |fderiv ℝ (fderiv ℝ h) x (b i) (b i)| ≤ ∑ _i : Fin d, B2 :=
        Finset.sum_le_sum fun i _ => this i
    _ = d * B2 := by simp

theorem s111x2_laplacian_continuous {h : Euc d → ℝ} (hh : ContDiff ℝ 2 h) :
    Continuous (Laplacian.laplacian h) := by
  set b := EuclideanSpace.basisFun (Fin d) ℝ with hb
  have hf1 : ContDiff ℝ 1 (fderiv ℝ h) := hh.fderiv_right (by norm_num)
  have hc2 : Continuous (fderiv ℝ (fderiv ℝ h)) := hf1.continuous_fderiv (by norm_num)
  have : Laplacian.laplacian h = fun x => ∑ i, fderiv ℝ (fderiv ℝ h) x (b i) (b i) := by
    rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis h b]
    simp [iteratedFDeriv_two_apply]
  rw [this]
  exact continuous_finsetSum _ fun i _ => (hc2.clm_apply continuous_const).clm_apply continuous_const

section Core

variable {s β : ℝ} {ρ : Euc d → ℝ} {M : ℝ} {C : WholeCoeff d}

/-- `∇ρ` has an integrable norm. -/
theorem s111x2_grad_integrable (E : EnData d s β ρ M C) : Integrable (fun x => ‖gradient ρ x‖) := by
  obtain ⟨c0, hc0⟩ := E.dgrow
  have hβ := E.hβ
  have : Integrable (fun x => β * (c0 * ((1 + ‖x‖) * ρ x))) := by
    have h1 : Integrable (fun x => (1 + ‖x‖) * ρ x) := by
      have := E.K.int.add E.mom
      refine this.congr (Filter.Eventually.of_forall fun x => ?_)
      simp only [Pi.add_apply]; ring
    exact (h1.const_mul c0).const_mul β
  refine this.mono' ?_ (Filter.Eventually.of_forall fun x => ?_)
  · exact (s111x2_gradient_continuous (E.smooth.of_le (by norm_num))).norm.aestronglyMeasurable
  · rw [E.grad 0 x, norm_smul, Real.norm_of_nonneg (mul_nonneg hβ.le (E.K.nonneg x))]
    have := hc0 0 x
    have h3 := E.K.nonneg x
    rw [Real.norm_of_nonneg (mul_nonneg (mul_nonneg hβ.le h3) (norm_nonneg _))]
    calc β * ρ x * ‖C.drift 0 x‖ ≤ β * ρ x * (c0 * (1 + ‖x‖)) := by gcongr
      _ = β * (c0 * ((1 + ‖x‖) * ρ x)) := by ring

/-- Generator = `-β⁻¹ L + N` pointwise. -/
theorem s111x2_gen_split (T : TD d s β ρ M C) {h : Euc d → ℝ} {B1 B2 : ℝ} (H : CbD h B1 B2) (x : Euc d) :
    generatorW C 0 h x = -β⁻¹ * s111x2_L ρ h x + Nnl d s ρ (gradient h) x := by
  have hg1 : ∀ y, ‖gradient h y‖ ≤ B1 := fun y => by rw [s111x2_norm_gradient]; exact H.d1 y
  rw [HRS.MS.S111X1.gen_formula T.en H.smooth hg1 0 x]
  have hβ := T.en.hβ
  have hρ := T.pos x
  have hgr := T.en.grad 0 x
  have : inner ℝ (C.drift 0 x) (gradient h x) = (β * ρ x)⁻¹ * inner ℝ (gradient ρ x) (gradient h x) := by
    rw [hgr, inner_smul_left]
    simp only [conj_trivial]
    field_simp
  rw [this]
  unfold s111x2_L Nnl
  field_simp
  ring

end Core

end HRS.MS.S111X2
