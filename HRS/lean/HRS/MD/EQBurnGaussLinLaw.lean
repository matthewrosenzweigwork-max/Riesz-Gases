import HRS.MD.EQBurnGaussLinGP

/-!
# EQ-BURN P2 (`eq_gauss_lin`), part 3: the law of the increment vector `G`

`G_a = Z^{τ_a}(φ_a) - Z^0(U^{0,τ_a}φ_a)` is a linear image of the Gaussian vector `(Z^{τ_a}φ_a, Z^0(U^{0,τ_a}φ_a))_a`
(`2p` coordinates); its covariance is computed from the kernel `eglK` and the Lyapunov identity `eqgld_cov_total`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open HRS HRS.PDE HRS.MD.EQGaussLyapDet HRS.MD.EQGaussLyapDet2
open scoped Matrix

namespace HRS.MD.EQBurnGaussLin

variable {d : ℕ}

section Law

variable (hd : 2 ≤ d) {s β : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (V : Torus d → ℝ)
  (hV : Torus.IsSmooth V) (hβ : 0 < β) (ρβ : Torus d → ℝ)
  (hρβ : IsThermalDensity (periodicRiesz d s) V β ρβ) {m : ℝ}
  {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
  {Z : ℝ → Ω → NegSobolev d m}

include hd hV hρβ in
/-- The frozen propagator `U^{0,t}` maps smooth tests to smooth tests. -/
theorem egl_prop_smooth {f : Torus d → ℝ} (hf : Torus.IsSmooth f) {t : ℝ} (ht : 0 ≤ t) :
    Torus.IsSmooth (propagator (mfData d s hs0 hsd V β hβ) (fun _ => ρβ) 0 t f) := by
  obtain ⟨hpos, hsm, -⟩ := eqgld_frozen hd hs0 hsd V hV hβ ρβ hρβ
  exact eqgld_prop_smooth (by omega : 1 ≤ d) hs0 hsd V hV hβ ρβ hρβ.1 hsm hpos f hf 0 t le_rfl ht

include hd hV hρβ in
/-- The law of the increment vector `G`. -/
theorem egl_law (hZ : IsStationaryGaussianField P s β hs0 hsd hβ V ρβ m Z) {p : ℕ}
    (τ : Fin p → ℝ) (hτ : ∀ a, 0 ≤ τ a) (φ : Fin p → Torus d → ℝ) (hφ : ∀ a, Torus.IsSmooth (φ a)) :
    law P (fun ω => (WithLp.toLp 2 fun a =>
        NegSobolev.eval (Z (τ a) ω) (φ a) - NegSobolev.eval (Z 0 ω)
          (propagator (mfData d s hs0 hsd V β hβ) (fun _ => ρβ) 0 (τ a) (φ a)) :
        EuclideanSpace ℝ (Fin p))) =
      ProbabilityTheory.multivariateGaussian 0 (Matrix.of fun a b =>
        2 * β⁻¹ * ∫ r in Set.Icc 0 (min (τ a) (τ b)), ∫ x,
          inner ℝ (Torus.grad (propagator (mfData d s hs0 hsd V β hβ) (fun _ => ρβ) r (τ a) (φ a)) x)
            (Torus.grad (propagator (mfData d s hs0 hsd V β hβ) (fun _ => ρβ) r (τ b) (φ b)) x) * ρβ x) := by
  classical
  obtain ⟨hpos, hsm, -⟩ := eqgld_frozen hd hs0 hsd V hV hβ ρβ hρβ
  have hρC : Continuous ρβ := MFLinear.continuous_of_isSmooth hsm
  set D := mfData d s hs0 hsd V β hβ with hD
  let U : Fin p → Torus d → ℝ := fun a => propagator D (fun _ => ρβ) 0 (τ a) (φ a)
  have hU : ∀ a, Torus.IsSmooth (U a) := fun a =>
    egl_prop_smooth hd hs0 hsd V hV hβ ρβ hρβ (hφ a) (hτ a)
  let τ' : Fin (p + p) → ℝ := Fin.append τ (fun _ => (0 : ℝ))
  let φ' : Fin (p + p) → Torus d → ℝ := Fin.append φ U
  have hτ' : ∀ i, 0 ≤ τ' i := by
    intro i
    refine Fin.addCases (fun a => ?_) (fun a => ?_) i
    · simp only [τ', Fin.append_left]; exact hτ a
    · simp only [τ', Fin.append_right]; exact le_rfl
  have hφ' : ∀ i, Torus.IsSmooth (φ' i) := by
    intro i
    refine Fin.addCases (fun a => ?_) (fun a => ?_) i
    · simp only [φ', Fin.append_left]; exact hφ a
    · simp only [φ', Fin.append_right]; exact hU a
  have hpsd := HRS.Q41.q41_lagcov_psd hd hs0 hsd hβ hV hρβ hρC hpos τ' hτ' φ' hφ'
  have hlaw := hZ.gaussian (p + p) τ' φ' hτ' hφ'
  let W : Ω → EuclideanSpace ℝ (Fin (p + p)) := fun ω =>
    WithLp.toLp 2 fun i => NegSobolev.eval (Z (τ' i) ω) (φ' i)
  have hWm : Measurable W :=
    (PiLp.continuous_toLp 2 _).measurable.comp (measurable_pi_iff.2 fun i =>
      (HRS.MD.EQGaussWindow.eqgw_eval_continuous (m := m) (hφ' i)).measurable.comp (hZ.meas _))
  have hmap : P.map W = ProbabilityTheory.multivariateGaussian 0
      (PDE.stationaryLagCov d s β D ρβ τ' φ') := hlaw
  let L : Matrix (Fin p) (Fin (p + p)) ℝ := Matrix.of fun a j =>
    (if j = Fin.castAdd p a then 1 else 0) - (if j = Fin.natAdd p a then 1 else 0)
  have hlin := HRS.Q41.q41_linear_image_law P W hWm.aemeasurable _ hpsd hmap L
  have hmv : ∀ (w : EuclideanSpace ℝ (Fin (p + p))) (a : Fin p),
      (L *ᵥ w.ofLp) a = w (Fin.castAdd p a) - w (Fin.natAdd p a) := by
    intro w a
    simp only [L, Matrix.mulVec, dotProduct, Matrix.of_apply, sub_mul, Finset.sum_sub_distrib,
      ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  have hG : (fun ω => (WithLp.toLp 2 fun a =>
        NegSobolev.eval (Z (τ a) ω) (φ a) - NegSobolev.eval (Z 0 ω) (U a) :
        EuclideanSpace ℝ (Fin p))) =
      fun ω => (WithLp.toLp 2 (L *ᵥ (W ω).ofLp) : EuclideanSpace ℝ (Fin p)) := by
    funext ω
    ext a
    rw [PiLp.toLp_apply, PiLp.toLp_apply, hmv]
    have e1 : W ω (Fin.castAdd p a) = NegSobolev.eval (Z (τ a) ω) (φ a) := by
      simp [W, τ', φ', Fin.append_left]
    have e2 : W ω (Fin.natAdd p a) = NegSobolev.eval (Z 0 ω) (U a) := by
      show NegSobolev.eval (Z (τ' (Fin.natAdd p a)) ω) (φ' (Fin.natAdd p a)) = _
      simp only [τ', φ', Fin.append_right]
    rw [e1, e2]
  have hmat : L * PDE.stationaryLagCov d s β D ρβ τ' φ' * Lᵀ = Matrix.of fun a b =>
      2 * β⁻¹ * ∫ r in Set.Icc 0 (min (τ a) (τ b)), eqgld_E D ρβ (φ a) (φ b) (τ a) (τ b) r := by
    ext a b
    have key : (L * PDE.stationaryLagCov d s β D ρβ τ' φ' * Lᵀ) a b =
        PDE.stationaryLagCov d s β D ρβ τ' φ' (Fin.castAdd p a) (Fin.castAdd p b) -
        PDE.stationaryLagCov d s β D ρβ τ' φ' (Fin.castAdd p a) (Fin.natAdd p b) -
        PDE.stationaryLagCov d s β D ρβ τ' φ' (Fin.natAdd p a) (Fin.castAdd p b) +
        PDE.stationaryLagCov d s β D ρβ τ' φ' (Fin.natAdd p a) (Fin.natAdd p b) := by
      simp only [L, Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, sub_mul, mul_sub,
        Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq', Finset.mem_univ, if_true]
      ring
    rw [key]
    simp only [eglK_entry, τ', φ', Fin.append_left, Fin.append_right]
    have htot := congrFun (congrFun (eqgld_cov_total hd hs0 hsd V hV hβ ρβ hρβ τ hτ φ hφ) a) b
    simp only [Matrix.of_apply] at htot
    rw [← eglK_entry d s β D ρβ τ φ a b, ← htot]
    have e1 := eglK_zero_right hd hs0 hsd V hV hβ ρβ hρβ (hτ a) (hφ a) (hU b)
    have e2 := eglK_zero_left hs0 hsd V hβ ρβ hρβ (τ := τ b) (hτ b) (φ := φ b) (g := U a)
    have e3 := eglK_zero_zero hd hs0 hsd V hV hβ ρβ hρβ (hU a) (hU b)
    rw [e1, e2, e3]
    simp only [Matrix.of_apply, U]
    ring
  have hlaw2 := hlin
  rw [← hG, hmat] at hlaw2
  exact hlaw2

end Law

end HRS.MD.EQBurnGaussLin

end
