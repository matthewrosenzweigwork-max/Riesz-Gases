import HRS.PDE.TorusFPEntropySpec
import HRS.PDE.TorusFPExist
import HRS.PDE.TorusFPCompare

/-!
# D3-a (classical layer), helper 1: torus calculus, the Gibbs measure, weighted Green identity

Relocated helpers for the frozen specifications of `HRS/PDE/TorusFPEntropySpec.lean`
(statements there are unchanged).  Contents:

* product rule, logarithm, tilted potential for `Torus.partialDeriv`; coordinates of norms/inner products;
* the Gibbs probability measure `P = d1_gibbsMeasure κ U`: `P` is a probability measure, `∫ g dP = c ∫ g G dx`,
  integrals against `P.withDensity (ofReal w)`;
* the weighted Green identity `∫ (L w) f dP = -κ ∫ ⟨∇f, ∇w⟩ dP` for `f, w ∈ C²` and the `G`-self-adjointness of
  `L = d1_gen κ (d1_gradDrift U)`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace HRS

variable {n : ℕ}

/-! ### Regularity bookkeeping -/

theorem d3a_smooth_ck1 {φ : Torus n → ℝ} (hφ : Torus.IsSmooth φ) : Torus.IsCk 1 φ := by
  simpa using d1_isCk_of_isSmooth hφ 1

theorem d3a_smooth_ck2 {φ : Torus n → ℝ} (hφ : Torus.IsSmooth φ) : Torus.IsCk 2 φ := by
  simpa using d1_isCk_of_isSmooth hφ 2

theorem d3a_ck2_ck1 {φ : Torus n → ℝ} (hφ : Torus.IsCk 2 φ) : Torus.IsCk 1 φ :=
  (show ContDiff ℝ 2 (Torus.lift φ) from hφ).of_le (by norm_num)

theorem d3a_continuous_of_ck1 {φ : Torus n → ℝ} (hφ : Torus.IsCk 1 φ) : Continuous φ :=
  Torus.continuous_of_continuous_lift (show ContDiff ℝ 1 (Torus.lift φ) from hφ).continuous

theorem d3a_hint (ρ : Measure (Torus n)) [IsFiniteMeasure ρ] {g : Torus n → ℝ} (hg : Continuous g) :
    Integrable g ρ :=
  hg.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-! ### Partial derivatives: product rule, logarithm, tilted potential -/

theorem d3a_pd_mul {φ ψ : Torus n → ℝ} (hφ : Torus.IsCk 1 φ) (hψ : Torus.IsCk 1 ψ) (j : Fin n)
    (x : Torus n) :
    Torus.partialDeriv j (fun y => φ y * ψ y) x =
      Torus.partialDeriv j φ x * ψ x + φ x * Torus.partialDeriv j ψ x := by
  have e1 : Torus.lift (fun y => φ y * ψ y) = fun y => Torus.lift φ y * Torus.lift ψ y := rfl
  have h := fderiv_fun_mul ((hφ.differentiable one_ne_zero) (Torus.rep x))
    ((hψ.differentiable one_ne_zero) (Torus.rep x))
  simp only [Torus.partialDeriv]
  rw [e1, h]
  simp [Torus.lift, Torus.mk_rep]
  try ring

theorem d3a_isCk_log {k : WithTop ℕ∞} {w : Torus n → ℝ} (hw : Torus.IsCk k w) (hpos : ∀ x, 0 < w x) :
    Torus.IsCk k (fun y => Real.log (w y)) := by
  unfold Torus.IsCk
  have e1 : Torus.lift (fun y => Real.log (w y)) = fun y => Real.log (Torus.lift w y) := rfl
  rw [e1]
  exact ContDiff.log hw (fun y => (hpos _).ne')

theorem d3a_pd_log {w : Torus n → ℝ} (hw : Torus.IsCk 1 w) (hpos : ∀ x, 0 < w x) (j : Fin n)
    (x : Torus n) :
    Torus.partialDeriv j (fun y => Real.log (w y)) x = Torus.partialDeriv j w x / w x := by
  have e1 : Torus.lift (fun y => Real.log (w y)) = fun y => Real.log (Torus.lift w y) := rfl
  have hd := (hw.differentiable one_ne_zero) (Torus.rep x)
  have hne : Torus.lift w (Torus.rep x) ≠ 0 := by
    simp only [Torus.lift, Function.comp_apply, Torus.mk_rep]
    exact (hpos x).ne'
  simp only [Torus.partialDeriv]
  rw [e1, fderiv.log hd hne]
  simp [Torus.lift, Torus.mk_rep, div_eq_inv_mul]

theorem d3a_pd_tilt {κ : ℝ} {U ψ : Torus n → ℝ} (hU : Torus.IsCk 1 U) (hψ : Torus.IsCk 1 ψ) (j : Fin n)
    (x : Torus n) :
    Torus.partialDeriv j (d3_tiltPot κ U ψ) x =
      Torus.partialDeriv j U x - κ * Torus.partialDeriv j ψ x := by
  have e1 : Torus.lift (d3_tiltPot κ U ψ) = fun y => Torus.lift U y - κ * Torus.lift ψ y := rfl
  have h1 := (hU.differentiable one_ne_zero) (Torus.rep x)
  have h2 := (hψ.differentiable one_ne_zero) (Torus.rep x)
  have h0 : HasFDerivAt (fun y => Torus.lift U y - κ * Torus.lift ψ y)
      (fderiv ℝ (Torus.lift U) (Torus.rep x) - κ • fderiv ℝ (Torus.lift ψ) (Torus.rep x))
      (Torus.rep x) := h1.hasFDerivAt.sub (h2.hasFDerivAt.const_mul κ)
  have h := h0.fderiv
  simp only [Torus.partialDeriv]
  rw [e1, h]
  simp

/-! ### Coordinates of norms and inner products -/

theorem d3a_norm_sq_eq (v : Euc n) : ‖v‖ ^ 2 = ∑ j, (v.ofLp j) ^ 2 :=
  EuclideanSpace.real_norm_sq_eq v

theorem d3a_inner_eq_sum (a b : Euc n) : inner ℝ a b = ∑ j, a.ofLp j * b.ofLp j := by
  rw [PiLp.inner_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [mul_comm]

theorem d3a_norm_sq_grad (φ : Torus n → ℝ) (x : Torus n) :
    ‖Torus.grad φ x‖ ^ 2 = ∑ j, (Torus.partialDeriv j φ x) ^ 2 := by
  rw [d3a_norm_sq_eq]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [d1c_grad_component]

theorem d3a_norm_sq_grad_sub (φ ψ : Torus n → ℝ) (x : Torus n) :
    ‖Torus.grad φ x - Torus.grad ψ x‖ ^ 2 =
      ∑ j, (Torus.partialDeriv j φ x - Torus.partialDeriv j ψ x) ^ 2 := by
  rw [d3a_norm_sq_eq]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [PiLp.sub_apply, d1c_grad_component]

theorem d3a_grad_log {w : Torus n → ℝ} (hw : Torus.IsCk 1 w) (hpos : ∀ x, 0 < w x) (x : Torus n) :
    Torus.grad (fun y => Real.log (w y)) x = (w x)⁻¹ • Torus.grad w x := by
  ext j
  rw [d1c_grad_component, d3a_pd_log hw hpos]
  simp [d1c_grad_component, div_eq_inv_mul]

theorem d3a_grad_eq_smul_log {w : Torus n → ℝ} (hw : Torus.IsCk 1 w) (hpos : ∀ x, 0 < w x)
    (x : Torus n) :
    Torus.grad w x = w x • Torus.grad (fun y => Real.log (w y)) x := by
  rw [d3a_grad_log hw hpos x, smul_smul, mul_inv_cancel₀ (hpos x).ne', one_smul]

/-! ### The Gibbs measure -/

theorem d3a_gibbs_isProb {κ : ℝ} {U : Torus n → ℝ} (hU : Torus.IsSmooth U) :
    IsProbabilityMeasure (d1_gibbsMeasure κ U) := by
  haveI := d1c_isFinite_gibbsRaw (κ := κ) hU
  have hraw : d1_gibbsRaw κ U Set.univ = ∫⁻ x, ENNReal.ofReal (d1_gibbsWeight κ U x) := by
    unfold d1_gibbsRaw
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  have hZtop : (∫⁻ x, ENNReal.ofReal (d1_gibbsWeight κ U x)) ≠ ⊤ := by
    rw [← hraw]; exact measure_ne_top _ _
  have hZ0 : (∫⁻ x, ENNReal.ofReal (d1_gibbsWeight κ U x)) ≠ 0 := by
    intro h
    have hm : Measurable (fun x => ENNReal.ofReal (d1_gibbsWeight κ U x)) :=
      (d1c_gibbs_continuous hU).measurable.ennreal_ofReal
    rw [lintegral_eq_zero_iff hm] at h
    have h2 : ∀ᵐ x ∂(volume : Measure (Torus n)), False := h.mono fun x hx => by
      have hx' : ENNReal.ofReal (d1_gibbsWeight κ U x) = 0 := hx
      rw [ENNReal.ofReal_eq_zero] at hx'
      exact absurd hx' (not_le.2 (Real.exp_pos _))
    have h3 : MeasureTheory.ae (volume : Measure (Torus n)) = ⊥ := Filter.eventually_false_iff_eq_bot.1 h2
    exact (IsProbabilityMeasure.ne_zero (volume : Measure (Torus n))) (ae_eq_bot.1 h3)
  refine ⟨?_⟩
  simp only [d1_gibbsMeasure, Measure.smul_apply, smul_eq_mul]
  rw [hraw, ENNReal.inv_mul_cancel hZ0 hZtop]

theorem d3a_exists_c {κ : ℝ} {U : Torus n → ℝ} (hU : Torus.IsSmooth U) :
    ∃ c : ℝ, ∀ g : Torus n → ℝ,
      ∫ x, g x ∂(d1_gibbsMeasure κ U) = c * ∫ x, g x * d1_gibbsWeight κ U x := by
  refine ⟨((∫⁻ x, ENNReal.ofReal (d1_gibbsWeight κ U x))⁻¹).toReal, fun g => ?_⟩
  unfold d1_gibbsMeasure
  rw [integral_smul_measure, d1c_integral_gibbsRaw hU, smul_eq_mul]

theorem d3a_integral_withDensity {P : Measure (Torus n)} {w : Torus n → ℝ} (hw : Measurable w)
    (hw0 : ∀ x, 0 ≤ w x) (g : Torus n → ℝ) :
    ∫ x, g x ∂(P.withDensity fun x => ENNReal.ofReal (w x)) = ∫ x, w x * g x ∂P := by
  rw [integral_withDensity_eq_integral_toReal_smul hw.ennreal_ofReal
    (ae_of_all _ fun x => ENNReal.ofReal_lt_top) g]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  simp only [ENNReal.toReal_ofReal (hw0 x), smul_eq_mul]

/-! ### Weighted Green identity -/

/-- Lebesgue form of the weighted Green identity:
`∫ (L w) f G dx = -κ ∑_j ∫ ∂_j f ∂_j w G dx`. -/
theorem d3a_green_leb {κ : ℝ} (hκ : 0 < κ) {U : Torus n → ℝ} (hU : Torus.IsSmooth U)
    {f w : Torus n → ℝ} (hf : Torus.IsCk 2 f) (hw : Torus.IsCk 2 w) :
    ∫ x, d1_gen κ (d1_gradDrift U) w x * f x * d1_gibbsWeight κ U x =
      -κ * ∑ j, ∫ x, Torus.partialDeriv j f x * Torus.partialDeriv j w x * d1_gibbsWeight κ U x := by
  have hκ0 : κ ≠ 0 := hκ.ne'
  have hU1 : Torus.IsCk 1 U := d3a_smooth_ck1 hU
  have hf1 : Torus.IsCk 1 f := d3a_ck2_ck1 hf
  have hw1 : Torus.IsCk 1 w := d3a_ck2_ck1 hw
  have hG1 := d1c_gibbs_isCk1 (κ := κ) hU1
  have hGc := d1c_gibbs_continuous (κ := κ) hU
  have hcU : ∀ j : Fin n, Continuous (Torus.partialDeriv j U) := fun j =>
    PDE.continuous_partialDeriv j U hU1
  have hcf : ∀ j : Fin n, Continuous (Torus.partialDeriv j f) := fun j =>
    PDE.continuous_partialDeriv j f hf1
  have hcw : ∀ j : Fin n, Continuous (Torus.partialDeriv j w) := fun j =>
    PDE.continuous_partialDeriv j w hw1
  have hcw2 : ∀ j : Fin n, Continuous (Torus.partialDeriv j (Torus.partialDeriv j w)) := fun j =>
    PDE.continuous_partialDeriv j _ (d1c_isCk1_partialDeriv hw j)
  have hcf0 : Continuous f := d3a_continuous_of_ck1 hf1
  -- the flux `A j = G ∂_j w`
  have hA1 : ∀ j : Fin n, Torus.IsCk 1 (fun y => d1_gibbsWeight κ U y * Torus.partialDeriv j w y) :=
    fun j => hG1.mul (d1c_isCk1_partialDeriv hw j)
  have hAd : ∀ (j : Fin n) (x : Torus n),
      Torus.partialDeriv j (fun y => d1_gibbsWeight κ U y * Torus.partialDeriv j w y) x =
        (-(κ⁻¹ * Torus.partialDeriv j U x) * d1_gibbsWeight κ U x) * Torus.partialDeriv j w x +
          d1_gibbsWeight κ U x * Torus.partialDeriv j (Torus.partialDeriv j w) x := by
    intro j x
    rw [d3a_pd_mul hG1 (d1c_isCk1_partialDeriv hw j) j x, d1c_partialDeriv_gibbs hU1 j x]
  have step1 : ∀ x, d1_gen κ (d1_gradDrift U) w x * f x * d1_gibbsWeight κ U x =
      ∑ j, κ * (Torus.partialDeriv j (fun y => d1_gibbsWeight κ U y * Torus.partialDeriv j w y) x *
        f x) := by
    intro x
    rw [d1c_gen_gradDrift κ U hw x]
    have hj : ∀ j : Fin n, κ * (Torus.partialDeriv j
        (fun y => d1_gibbsWeight κ U y * Torus.partialDeriv j w y) x * f x) =
        (κ * Torus.partialDeriv j (Torus.partialDeriv j w) x -
          Torus.partialDeriv j U x * Torus.partialDeriv j w x) * f x * d1_gibbsWeight κ U x := by
      intro j
      rw [hAd j x]
      field_simp
      ring
    rw [Finset.sum_congr rfl fun j _ => hj j]
    simp only [← Finset.sum_mul, Finset.sum_sub_distrib, ← Finset.mul_sum]
  have hint_j : ∀ j : Fin n, Integrable (fun x => Torus.partialDeriv j
      (fun y => d1_gibbsWeight κ U y * Torus.partialDeriv j w y) x * f x) := fun j =>
    d3a_hint volume ((PDE.continuous_partialDeriv j _ (hA1 j)).mul hcf0)
  have hj : ∀ j : Fin n, ∫ x, κ * (Torus.partialDeriv j
      (fun y => d1_gibbsWeight κ U y * Torus.partialDeriv j w y) x * f x) =
      -κ * ∫ x, Torus.partialDeriv j f x * Torus.partialDeriv j w x * d1_gibbsWeight κ U x := by
    intro j
    rw [integral_const_mul, PDE.integral_partialDeriv_mul j _ f (hA1 j) hf1]
    have hpt : ∀ x, d1_gibbsWeight κ U x * Torus.partialDeriv j w x * Torus.partialDeriv j f x =
        Torus.partialDeriv j f x * Torus.partialDeriv j w x * d1_gibbsWeight κ U x := fun x => by ring
    simp_rw [hpt]
    ring
  simp_rw [step1]
  rw [integral_finsetSum _ fun j _ => (hint_j j).const_mul κ]
  rw [Finset.sum_congr rfl fun j _ => hj j, ← Finset.mul_sum]

/-- Weighted Green identity for the Gibbs probability measure. -/
theorem d3a_green_P {κ : ℝ} (hκ : 0 < κ) {U : Torus n → ℝ} (hU : Torus.IsSmooth U)
    {f w : Torus n → ℝ} (hf : Torus.IsCk 2 f) (hw : Torus.IsCk 2 w) :
    ∫ x, d1_gen κ (d1_gradDrift U) w x * f x ∂(d1_gibbsMeasure κ U) =
      -κ * ∫ x, inner ℝ (Torus.grad f x) (Torus.grad w x) ∂(d1_gibbsMeasure κ U) := by
  obtain ⟨c, hc⟩ := d3a_exists_c (κ := κ) hU
  have hf1 : Torus.IsCk 1 f := d3a_ck2_ck1 hf
  have hw1 : Torus.IsCk 1 w := d3a_ck2_ck1 hw
  have hG := d1c_gibbs_continuous (κ := κ) hU
  have hsum : ∫ x, inner ℝ (Torus.grad f x) (Torus.grad w x) * d1_gibbsWeight κ U x =
      ∑ j, ∫ x, Torus.partialDeriv j f x * Torus.partialDeriv j w x * d1_gibbsWeight κ U x := by
    simp_rw [d1c_inner_grad, Finset.sum_mul]
    rw [integral_finsetSum]
    intro j _
    exact d3a_hint volume (((PDE.continuous_partialDeriv j f hf1).mul
      (PDE.continuous_partialDeriv j w hw1)).mul hG)
  rw [hc, hc, d3a_green_leb hκ hU hf hw, hsum]
  ring

/-- `G`-self-adjointness of `L = d1_gen κ (d1_gradDrift U)` on `C²` functions. -/
theorem d3a_selfadj {κ : ℝ} (hκ : 0 < κ) {U : Torus n → ℝ} (hU : Torus.IsSmooth U)
    {f w : Torus n → ℝ} (hf : Torus.IsCk 2 f) (hw : Torus.IsCk 2 w) :
    ∫ x, d1_gen κ (d1_gradDrift U) w x * f x ∂(d1_gibbsMeasure κ U) =
      ∫ x, d1_gen κ (d1_gradDrift U) f x * w x ∂(d1_gibbsMeasure κ U) := by
  rw [d3a_green_P hκ hU hf hw, d3a_green_P hκ hU hw hf]
  have : (fun x => inner ℝ (Torus.grad f x) (Torus.grad w x)) =
      fun x => inner ℝ (Torus.grad w x) (Torus.grad f x) :=
    funext fun x => real_inner_comm _ _
  rw [this]

/-- `∫ L w dP = 0`. -/
theorem d3a_int_gen_zero {κ : ℝ} (hκ : 0 < κ) {U : Torus n → ℝ} (hU : Torus.IsSmooth U)
    {w : Torus n → ℝ} (hw : Torus.IsCk 2 w) :
    ∫ x, d1_gen κ (d1_gradDrift U) w x ∂(d1_gibbsMeasure κ U) = 0 := by
  obtain ⟨c, hc⟩ := d3a_exists_c (κ := κ) hU
  rw [hc, d1c_ibp hκ hU hw, mul_zero]

end HRS
