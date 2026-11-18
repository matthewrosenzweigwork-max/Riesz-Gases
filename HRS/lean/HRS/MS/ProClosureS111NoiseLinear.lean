import HRS.MS.ProClosureS111NoiseFeatures
import HRS.MS.S111X1Aux6

/-!
The actual common-noise feature is linear on the original oscillator test
space. The proof uses physical classical superposition before taking
gradients, and equality of the resulting L² classes. In particular, no
linearity of a totalized integral is used without membership.
-/
set_option autoImplicit false
set_option maxHeartbeats 6400000
noncomputable section
open Classical MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.ProClosureS111
open HRS HRS.Whole HRS.MS.S111X1

variable {d : ℕ} {s a beta gamma : ℝ} {rho : Euc d → ℝ}

theorem gradient_add_const_mul {f g : Euc d → ℝ} {x : Euc d}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) (c : ℝ) :
    gradient (fun y => f y + c * g y) x = gradient f x + c • gradient g x := by
  change gradient (f + fun y => c * g y) x = _
  unfold gradient
  rw [fderiv_add hf (hg.const_mul c), fderiv_const_mul hg c]
  simp only [map_add, map_smul]

variable [IsProbabilityMeasure (HRS.Whole.withDensityReal rho)]

theorem actual_noise_memLp (hX : X1Input d s a beta gamma rho)
    {t : ℝ} (ht : 0 ≤ t) (phi : oscSub d (wholeSpaceIndex d)) :
    MemLp (noiseVector (x1C d s a beta rho) t (phi : Euc d → ℝ)) 2
      ((volume : Measure ℝ).prod (HRS.Whole.withDensityReal rho)) :=
  noiseVector_memLp ht (x1_prop_classical (hX.exist t ht phi phi.property))

theorem noiseClass_linear (hX : X1Input d s a beta gamma rho)
    {t : ℝ} (ht : 0 ≤ t) (phi psi : oscSub d (wholeSpaceIndex d)) (c : ℝ) :
    noiseClass (x1C d s a beta rho) (HRS.Whole.withDensityReal rho) t
        ((phi + c • psi : oscSub d (wholeSpaceIndex d)) : Euc d → ℝ) =
      noiseClass (x1C d s a beta rho) (HRS.Whole.withDensityReal rho) t (phi : Euc d → ℝ) +
        c • noiseClass (x1C d s a beta rho) (HRS.Whole.withDensityReal rho) t (psi : Euc d → ℝ) := by
  let C := x1C d s a beta rho
  let mu := HRS.Whole.withDensityReal rho
  have hf := x1_prop_classical (hX.exist t ht phi phi.property)
  have hg := x1_prop_classical (hX.exist t ht psi psi.property)
  have hraw : noiseVector C t
      ((phi + c • psi : oscSub d (wholeSpaceIndex d)) : Euc d → ℝ) =
      fun p => noiseVector C t (phi : Euc d → ℝ) p +
        c • noiseVector C t (psi : Euc d → ℝ) p := by
    funext p
    by_cases hp : p.1 ∈ Icc (0 : ℝ) t
    · simp only [noiseVector, if_pos hp]
      change gradient (propagatorW C p.1 t
        (fun y => (phi : Euc d → ℝ) y + c * (psi : Euc d → ℝ) y)) p.2 = _
      rw [hX.prop_lin ht phi.property psi.property c p.1 hp]
      exact gradient_add_const_mul
        ((hf.c2 p.1 hp).differentiable (by norm_num) p.2)
        ((hg.c2 p.1 hp).differentiable (by norm_num) p.2) c
    · simp [noiseVector, hp]
  apply Lp.ext
  filter_upwards [noiseClass_ae (actual_noise_memLp hX ht (phi + c • psi)),
    noiseClass_ae (actual_noise_memLp hX ht phi),
    noiseClass_ae (actual_noise_memLp hX ht psi),
    Lp.coeFn_add (noiseClass C mu t (phi : Euc d → ℝ))
      (c • noiseClass C mu t (psi : Euc d → ℝ)),
    Lp.coeFn_smul c (noiseClass C mu t (psi : Euc d → ℝ))]
      with p h1 h2 h3 h4 h5
  rw [h1, h4, Pi.add_apply, h5, Pi.smul_apply, h2, h3]
  exact congrFun hraw p

theorem scaledNoiseClass_linear (hX : X1Input d s a beta gamma rho)
    (q : ℝ) {t : ℝ} (ht : 0 ≤ t)
    (phi psi : oscSub d (wholeSpaceIndex d)) (c : ℝ) :
    scaledNoiseClass (x1C d s a beta rho) (HRS.Whole.withDensityReal rho) q t
        ((phi + c • psi : oscSub d (wholeSpaceIndex d)) : Euc d → ℝ) =
      scaledNoiseClass (x1C d s a beta rho) (HRS.Whole.withDensityReal rho) q t (phi : Euc d → ℝ) +
        c • scaledNoiseClass (x1C d s a beta rho) (HRS.Whole.withDensityReal rho) q t (psi : Euc d → ℝ) := by
  simp only [scaledNoiseClass, noiseClass_linear hX ht phi psi c,
    smul_add, smul_smul, mul_comm]

theorem scaledNoiseClass_zero (hX : X1Input d s a beta gamma rho)
    (q : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    scaledNoiseClass (x1C d s a beta rho) (HRS.Whole.withDensityReal rho) q t
      ((0 : oscSub d (wholeSpaceIndex d)) : Euc d → ℝ) = 0 := by
  have he := scaledNoiseClass_linear hX q ht 0 0 1
  simp only [one_smul, zero_add] at he
  exact add_left_cancel (he.symm.trans (add_zero _).symm)

def noiseLinear (hX : X1Input d s a beta gamma rho) (q : ℝ)
    {t : ℝ} (ht : 0 ≤ t) :
    oscSub d (wholeSpaceIndex d) →ₗ[ℝ] NoiseHilbert (HRS.Whole.withDensityReal rho) where
  toFun phi := scaledNoiseClass (x1C d s a beta rho) (HRS.Whole.withDensityReal rho) q t
    (phi : Euc d → ℝ)
  map_add' phi psi := by
    simpa only [one_smul] using scaledNoiseClass_linear hX q ht phi psi 1
  map_smul' c phi := by
    have he := scaledNoiseClass_linear hX q ht 0 phi c
    simpa only [zero_add, scaledNoiseClass_zero hX q ht, RingHom.id_apply] using he

theorem noiseLinear_apply (hX : X1Input d s a beta gamma rho) (q : ℝ)
    {t : ℝ} (ht : 0 ≤ t) (phi : oscSub d (wholeSpaceIndex d)) :
    noiseLinear hX q ht phi =
      scaledNoiseClass (x1C d s a beta rho) (HRS.Whole.withDensityReal rho) q t (phi : Euc d → ℝ) := rfl

#print axioms noiseClass_linear

end HRS.MS.ProClosureS111
