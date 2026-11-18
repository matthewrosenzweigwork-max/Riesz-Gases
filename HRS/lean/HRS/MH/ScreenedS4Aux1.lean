import HRS.MH.ScreenedDefs
import HRS.MS.QMulAux1

/-!
# Packet S4, part 1: the `L²` inverse Fourier transform of an `L¹ ∩ L²` function

`s4_symm_eq`: `(FT d).symm f = negLp (FT d f)`; `s4_bridge`: for `M ∈ L¹ ∩ L²` the `L²` inverse transform
of `M` is a.e. the pointwise integral `y ↦ ∫ M(ξ) e^{2πi⟨y,ξ⟩} dξ`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal ComplexConjugate FourierTransform ContDiff

namespace HRS.MH.Screened

open HRS HRS.Whole HRS.PDE.ToolboxRd.FourierAux

variable {d : ℕ}

lemma s4_symm_eq (f : Lp (α := Euc d) ℂ 2) : (FT d).symm f = negLp (FT d f) := by
  refine (SchwartzMap.denseRange_toLpCLM (E := Euc d) (F := ℂ) (p := 2)
    ENNReal.ofNat_ne_top).induction_on f (isClosed_eq ?_ ?_) ?_
  · exact (FT d).symm.continuous
  · exact continuous_negLp.comp (FT d).continuous
  · intro φ
    simp only [SchwartzMap.toLpCLM_apply]
    have e1 : (FT d).symm (φ.toLp 2) = ((𝓕⁻ φ : SchwartzMap (Euc d) ℂ)).toLp 2 :=
      SchwartzMap.toLp_fourierInv_eq _
    have e2 : FT d (φ.toLp 2) = ((𝓕 φ : SchwartzMap (Euc d) ℂ)).toLp 2 :=
      SchwartzMap.toLp_fourier_eq _
    rw [e1, e2]
    apply Lp.ext
    have hq := (Measure.measurePreserving_neg (volume : Measure (Euc d))).quasiMeasurePreserving
    have h1 := negLp_coe (((𝓕 φ : SchwartzMap (Euc d) ℂ)).toLp 2 : Lp (α := Euc d) ℂ 2)
    have h2 := hq.ae_eq_comp (SchwartzMap.coeFn_toLp (𝓕 φ : SchwartzMap (Euc d) ℂ) 2 volume)
    filter_upwards [SchwartzMap.coeFn_toLp (𝓕⁻ φ : SchwartzMap (Euc d) ℂ) 2 volume, h1, h2]
      with ξ a b c
    rw [a, b]
    simp only [Function.comp_apply] at c
    rw [c, SchwartzMap.fourierInv_coe, SchwartzMap.fourier_coe, Real.fourierInv_eq_fourier_neg]

lemma s4_bridge {M : Euc d → ℂ} (h1 : Integrable M) (h2 : MemLp M 2 volume) :
    ∀ᵐ y : Euc d ∂volume, ((FT d).symm (h2.toLp M) : Euc d → ℂ) y =
      ∫ ξ : Euc d, M ξ * Complex.exp (2 * Real.pi * Complex.I * (inner ℝ y ξ : ℝ)) := by
  rw [s4_symm_eq]
  have hq := (Measure.measurePreserving_neg (volume : Measure (Euc d))).quasiMeasurePreserving
  have h3 := hq.ae_eq_comp (HRS.MS.QMul.qm_L1L2 h1 h2)
  filter_upwards [negLp_coe (FT d (h2.toLp M)), h3] with y a b
  rw [a]
  simp only [Function.comp_apply] at b
  rw [b, Real.fourier_eq']
  refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
  simp only [smul_eq_mul, inner_neg_right]
  rw [mul_comm]
  congr 2
  push_cast
  rw [real_inner_comm y ξ]
  ring

end HRS.MH.Screened
