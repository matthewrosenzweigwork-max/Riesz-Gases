import HRS.Commutator.Torus.TPRODAux1
import HRS.Commutator.Torus.TEXTAux14
import HRS.Commutator.Torus.TSAMPAux13
import HRS.Commutator.Torus.TSAMPAux8
import HRS.Commutator.Torus.TSAMPAux5
import HRS.PDE.MeanFieldFejer
import HRS.PDE.EnergyR2Fn

/-!
# T-PROD helper file 2: Fejér smoothing on the torus

For `f ∈ L¹(𝕋^d)` and `N ≥ 1`, the Fejér mean `F_N ⋆ f` is a.e. equal to a smooth function `φ_N` with
`φ̂_N(k) = c_N(k) f̂(k)`, `c_N(k) = ∏_i (1 - |k_i|/N)_+`; `‖F_N ⋆ f‖_p ≤ ‖f‖_p`; for continuous `f` the
Fejér means converge uniformly, hence `\widehat{φ_N g}(k) → \widehat{f g}(k)` for continuous `g`.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform ComplexConjugate

namespace HRS.Commutator.TorusNote

open HRS

variable {d : ℕ}

/-- The Fourier coefficients `∏_i (1 - |k_i|/N)_+` of the Fejér kernel. -/
def tprod_fc (N : ℕ) (k : Lattice d) : ℝ := ∏ i : Fin d, max (1 - |(k i : ℝ)| / N) 0

lemma tprod_fc_neg (N : ℕ) (k : Lattice d) : tprod_fc N (-k) = tprod_fc N k := by
  unfold tprod_fc
  simp

lemma tprod_fejer_fcoef {N : ℕ} (hN : 0 < N) (k : Lattice d) :
    Torus.fcoef (HRS.PDE.MFThermalExist.fejer N : Torus d → ℝ) k = ((tprod_fc N k : ℝ) : ℂ) := by
  rw [tsamp_fcoef_eq_coeffOf, HRS.PDE.MFThermalExist.coeffOf_fejer N hN k]
  unfold tprod_fc
  push_cast
  rfl

lemma tprod_fcoef_conj {f : Torus d → ℝ} (hf : Integrable f) (k : Lattice d) :
    Torus.fcoef f (-k) = conj (Torus.fcoef f k) := by
  rw [tsamp_fcoef_eq_coeffOf, tsamp_fcoef_eq_coeffOf]
  exact HRS.PDE.isRealCoeff_coeffOf f hf k

lemma tprod_exists_smooth {f : Torus d → ℝ} (hf : Integrable f) {N : ℕ} (hN : 0 < N) :
    ∃ φ : Torus d → ℝ, Torus.IsSmooth φ ∧
      (∀ k, Torus.fcoef φ k = ((tprod_fc N k : ℝ) : ℂ) * Torus.fcoef f k) ∧
      φ =ᵐ[volume] textConv (HRS.PDE.MFThermalExist.fejer N : Torus d → ℝ) f := by
  set c : Lattice d → ℂ := fun k => ((tprod_fc N k : ℝ) : ℂ) * Torus.fcoef f k with hc
  have hr : HRS.PDE.IsRealCoeff c := by
    intro k
    simp only [hc, tprod_fc_neg, tprod_fcoef_conj hf, map_mul, Complex.conj_ofReal]
  have ht : HRS.PDE.IsTrigPoly N c := by
    intro k hk
    by_contra hbox
    apply hk
    have : tprod_fc N k = 0 := by
      unfold HRS.PDE.InBox at hbox
      push_neg at hbox
      obtain ⟨i, hi⟩ := hbox
      unfold tprod_fc
      refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
      have hN' : (0 : ℝ) < N := by exact_mod_cast hN
      have : (N : ℝ) < |(k i : ℝ)| := by
        have h1 : (N : ℤ) < |k i| := hi
        have h2 : ((N : ℤ) : ℝ) < ((|k i| : ℤ) : ℝ) := by exact_mod_cast h1
        simpa using h2
      refine max_eq_right ?_
      rw [sub_nonpos, one_le_div hN']
      exact this.le
    simp [hc, this]
  refine ⟨HRS.PDE.toFun c, ?_, ?_, ?_⟩
  · unfold Torus.IsSmooth Torus.IsCk
    rw [contDiff_infty]
    intro n
    exact HRS.PDE.R2Aux.isCk_toFun_trig hr ht n
  · intro k
    rw [tsamp_fcoef_eq_coeffOf, HRS.PDE.R2Aux.coeffOf_toFun_trig hr ht]
  · have hK : Integrable (HRS.PDE.MFThermalExist.fejer N : Torus d → ℝ) :=
      HRS.PDE.MFThermalExist.integrable_of_continuous' (HRS.PDE.MFThermalExist.fejer_continuous N)
    have hφc : Continuous (HRS.PDE.toFun c) := HRS.PDE.R2Aux.continuous_toFun_trig hr ht
    have hφi : Integrable (HRS.PDE.toFun c) :=
      HRS.PDE.MFThermalExist.integrable_of_continuous' hφc
    have hci := text_integrable_conv hK hf
    have h0 : ∀ k, Torus.fcoef (fun x => HRS.PDE.toFun c x - textConv (HRS.PDE.MFThermalExist.fejer N : Torus d → ℝ) f x) k = 0 := by
      intro k
      rw [text_fcoef_sub hφi hci, text_fcoef_conv hK hf, tprod_fejer_fcoef hN,
        tsamp_fcoef_eq_coeffOf, HRS.PDE.R2Aux.coeffOf_toFun_trig hr ht]
      simp [hc, tsamp_fcoef_eq_coeffOf]
    have := text_ae_eq_zero_of_fcoef (hφi.sub hci) h0
    filter_upwards [this] with x hx
    simpa [sub_eq_zero] using hx

lemma tprod_conv_eLpNorm_le {f : Torus d → ℝ} (hf : Measurable f) {p : ℝ} (hp : 1 < p) {N : ℕ}
    (hN : 0 < N) :
    eLpNorm (textConv (HRS.PDE.MFThermalExist.fejer N : Torus d → ℝ) f) (ENNReal.ofReal p) volume ≤
      eLpNorm f (ENNReal.ofReal p) volume := by
  have hK : Integrable (HRS.PDE.MFThermalExist.fejer N : Torus d → ℝ) :=
    HRS.PDE.MFThermalExist.integrable_of_continuous' (HRS.PDE.MFThermalExist.fejer_continuous N)
  have hKm : Measurable (HRS.PDE.MFThermalExist.fejer N : Torus d → ℝ) :=
    (HRS.PDE.MFThermalExist.fejer_continuous N).measurable
  have h := tsamp_conv_eLpNorm_le (E := ℝ) hK hKm hf hp
  rw [tsamp_conv_real] at h
  have hone : ∫ y, ‖(HRS.PDE.MFThermalExist.fejer N : Torus d → ℝ) y‖ = 1 := by
    refine (integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)).trans
      (HRS.PDE.MFThermalExist.integral_fejer (d := d) N hN)
    exact Real.norm_of_nonneg (HRS.PDE.MFThermalExist.fejer_nonneg N y)
  rw [hone, ENNReal.ofReal_one, one_mul] at h
  exact h

/-- Uniform convergence of the Fejér means of a continuous function (shifted index `N+1`). -/
lemma tprod_fejer_unif {f : Torus d → ℝ} (hf : Continuous f) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ x, |textConv (HRS.PDE.MFThermalExist.fejer (N + 1) : Torus d → ℝ) f x - f x| < ε := by
  have h := (Metric.tendstoUniformly_iff.1 (HRS.PDE.MFThermalExist.fejer_tendsto_uniformly f hf)) ε hε
  have h' := (tendsto_add_atTop_nat 1).eventually h
  filter_upwards [h'] with N hN x
  have := hN x
  rw [Real.dist_eq, abs_sub_comm] at this
  exact this

end HRS.Commutator.TorusNote
