import HRS.MS.WadAux6
import HRS.Whole.CriticalNoise

/-!
# S8.3, interface with the frozen generator

`s83_generator_decomp`: for `h ∈ C²`, the frozen backward generator `generatorW (critCoeff d a β ρβ) r` of the
critical quadratic model splits as `L_0 h + B h`, with `L_0 = νΔ - a x·∇` the Ornstein-Uhlenbeck generator
(`s83_L0`, `ν = β⁻¹`) and the *first order* remainder
`B h = ⟨M(∇g*ρ_β), ∇h⟩ - Σ_j (∇g * (ρ_β (Mᵀ∇h)_j))_j` (`M = -1`); no second derivative of `h` occurs in `B h`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ContDiff

namespace HRS.MS.Wad

open HRS HRS.Whole

variable {d : ℕ}

theorem s83_gradient_confinement (a : ℝ) (x : Euc d) : gradient (confinement a) x = a • x := by
  have h1 : HasFDerivAt (fun y : Euc d => ‖y‖ ^ 2) (2 • innerSL ℝ x) x :=
    (hasStrictFDerivAt_norm_sq x).hasFDerivAt
  have h2 : HasFDerivAt (confinement a) ((a / 2) • (2 • innerSL ℝ x)) x := by
    have := h1.const_mul (a / 2)
    convert this using 1
    funext y
    unfold confinement
    ring
  unfold gradient
  rw [h2.fderiv]
  have : ((a / 2) • (2 • innerSL ℝ x) : Euc d →L[ℝ] ℝ) = a • innerSL ℝ x := by
    ext v; simp; ring
  rw [this]
  apply (InnerProductSpace.toDual ℝ (Euc d)).injective
  rw [LinearIsometryEquiv.apply_symm_apply]
  ext v
  simp [InnerProductSpace.toDual_apply_apply]

theorem s83_lap_eq {h : Euc d → ℝ} (x : Euc d) : Laplacian.laplacian h x = s83_lap h x := by
  have := congrFun (InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis
    (f := h) (EuclideanSpace.basisFun (Fin d) ℝ)) x
  unfold s83_lap
  rw [this]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [iteratedFDeriv_two_apply]
  simp

theorem s83_inner_gradient (h : Euc d → ℝ) (x v : Euc d) : inner ℝ (gradient h x) v = fderiv ℝ h x v := by
  unfold gradient
  exact InnerProductSpace.toDual_symm_apply

/-- **Splitting of the frozen generator**: `generatorW = L_0 + B` with `B` of first order. -/
theorem s83_generator_decomp (a β : ℝ) (ρβ : Euc d → ℝ) (r : ℝ) (h : Euc d → ℝ) (x : Euc d) :
    generatorW (critCoeff d a β ρβ) r h x = s83_L0 a β⁻¹ h x +
      (inner ℝ (Torus.matVec (-1 : Matrix (Fin d) (Fin d) ℝ)
          (convGradConvW (rieszKernelGrad d ((d : ℝ) / 2)) ρβ x)) (gradient h x) -
        ∑ j : Fin d, (convGradConvW (rieszKernelGrad d ((d : ℝ) / 2))
          (fun y => ρβ y * (Torus.matVec (-1 : Matrix (Fin d) (Fin d) ℝ).transpose (gradient h y)) j) x) j) := by
  unfold generatorW critCoeff WholeDyn.coeff quadraticGradientDyn meanFieldDriftW s83_L0
  simp only [s83_gradient_confinement, s83_lap_eq]
  have e : inner ℝ x (gradient h x) = fderiv ℝ h x x := by
    rw [real_inner_comm]; exact s83_inner_gradient h x x
  rw [inner_sub_left, inner_smul_left, e]
  simp only [conj_trivial]
  ring

end HRS.MS.Wad
