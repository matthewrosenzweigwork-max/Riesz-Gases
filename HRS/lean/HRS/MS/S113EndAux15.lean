import HRS.MS.S113EndAux14

/-!
# S11.3 endpoint (worker S11X), part 15: the Fokker-Planck operator on the modulated Gibbs density

`s113x_movFP_eq`: for a positive `C²` density `f` with `u = movU f` differentiable and `∇(g*f) = movForce f`, off the collision set
`movFP q_N = q_N ∑_i [div u(X_i) + ∑_k Ψ_{ik}(X) u_k(X_i)]`, `Ψ_{ik} = ∂_{ik} log q_N = β(u_k(X_i) - b_{ik}(X))`.
(Physical Fokker-Planck `𝓛_N^* q_N = ∑_i div_i(q_N u(x_i))`.)
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S113BD

open HRS HRS.Whole

variable {d N : ℕ}

theorem s113x_hasDerivAt_line_gen {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {φ : Euc d → F}
    {φ' : Euc d →L[ℝ] F} {z w : Euc d} (h : HasFDerivAt φ φ' z) :
    HasDerivAt (fun τ : ℝ => φ (z + τ • w)) (φ' w) 0 := by
  have hline : HasDerivAt (fun τ : ℝ => z + τ • w) w 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).smul_const w).const_add z
    simpa using this
  have h' : HasFDerivAt φ φ' (z + (0 : ℝ) • w) := by simpa using h
  exact h'.comp_hasDerivAt (0 : ℝ) hline

/-- The coordinate `k` of a vector function along a line. -/
theorem s113x_hasDerivAt_line_coord {φ : Euc d → Euc d} {z : Euc d} (hφ : DifferentiableAt ℝ φ z) (k : Fin d) :
    HasDerivAt (fun τ : ℝ => (φ (z + τ • EuclideanSpace.single k (1 : ℝ))) k)
      ((fderiv ℝ φ z (EuclideanSpace.single k (1 : ℝ))) k) 0 := by
  have h1 := s113x_hasDerivAt_line_gen (w := EuclideanSpace.single k (1 : ℝ)) hφ.hasFDerivAt
  exact ((EuclideanSpace.proj k : Euc d →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h1)

theorem s113x_drift_line_hasDerivAt (s q : ℝ) {Y : EucConfig d N} (hY : Y ∉ eucCollisionSet d N) (i : Fin N) (k : Fin d) :
    HasDerivAt (fun τ => s113x_drift d s q N i k (s113x_line Y i k τ))
      (q + (1 / (N : ℝ)) * ∑ j ∈ Finset.univ.erase i,
        (fderiv ℝ (rieszKernelGrad d s) (Y i - Y j) (EuclideanSpace.single k (1 : ℝ))) k) 0 := by
  have h1 : HasDerivAt (fun τ : ℝ => q * (Y i + τ • EuclideanSpace.single k (1 : ℝ)) k) q 0 := by
    have : HasDerivAt (fun τ : ℝ => (Y i + τ • EuclideanSpace.single k (1 : ℝ)) k) 1 0 := by
      have h := (hasDerivAt_id (0 : ℝ)).const_add ((Y i) k)
      refine h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun τ => ?_)
      simp
    simpa using this.const_mul q
  have h2 : ∀ j ∈ Finset.univ.erase i, HasDerivAt (fun τ : ℝ => (rieszKernelGrad d s ((Y i - Y j) + τ • EuclideanSpace.single k (1 : ℝ))) k)
      ((fderiv ℝ (rieszKernelGrad d s) (Y i - Y j) (EuclideanSpace.single k (1 : ℝ))) k) 0 := by
    intro j hj
    have hne : Y i - Y j ≠ 0 := fun h => hY ⟨i, j, (Finset.ne_of_mem_erase hj).symm, sub_eq_zero.1 h⟩
    exact s113x_hasDerivAt_line_coord (s113x_G_diffAt s hne) k
  have h3 := (HasDerivAt.fun_sum h2).const_mul (1 / (N : ℝ))
  have h4 := h1.add h3
  unfold s113x_drift
  refine h4.congr_of_eventuallyEq (Filter.Eventually.of_forall fun τ => ?_)
  simp only [s113x_line_apply_same]
  congr 2
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [s113x_line_apply_ne Y i k (Finset.ne_of_mem_erase hj)]
  have e1 : Y i + τ • EuclideanSpace.single k (1 : ℝ) - Y j = Y i - Y j + τ • EuclideanSpace.single k (1 : ℝ) := by abel
  rw [e1]


theorem s113x_Psi_line_hasDerivAt (s q β : ℝ) {u : Euc d → Euc d} (hu : Differentiable ℝ u) {Y : EucConfig d N}
    (hY : Y ∉ eucCollisionSet d N) (i : Fin N) (k : Fin d) :
    HasDerivAt (fun τ => s113x_Psi d s q β N u i k (s113x_line Y i k τ))
      (β * ((fderiv ℝ u (Y i) (EuclideanSpace.single k (1 : ℝ))) k - (q + (1 / (N : ℝ)) * ∑ j ∈ Finset.univ.erase i,
        (fderiv ℝ (rieszKernelGrad d s) (Y i - Y j) (EuclideanSpace.single k (1 : ℝ))) k))) 0 := by
  have h1 := s113x_hasDerivAt_line_coord (hu (Y i)) k
  have h2 := s113x_drift_line_hasDerivAt s q hY i k
  have h3 := (h1.sub h2).const_mul β
  unfold s113x_Psi
  refine h3.congr_of_eventuallyEq (Filter.Eventually.of_forall fun τ => ?_)
  simp [s113x_Psi, s113x_line_apply_same]

/-- One summand of `movFP`. -/
theorem s113x_fp_term {s q β : ℝ} (hβ : β ≠ 0) {f : Euc d → ℝ} (hf : ∀ x, DifferentiableAt ℝ f x)
    (hpos : ∀ x, 0 < f x)
    (hΓ : ∀ x, HasFDerivAt (HRS.Whole.convMeasure (rieszKernel d s) (HRS.Whole.withDensityReal f))
      (innerSL ℝ (movForce d s f x)) x)
    (hu : Differentiable ℝ (movU d s q β f)) {X : EucConfig d N} (hX : X ∉ eucCollisionSet d N)
    (i : Fin N) (k : Fin d) :
    β⁻¹ * movPartial (movPartial (movQDensity d s β N f) i k) i k X +
      movPartial (fun Y => movQDensity d s β N f Y * (q * Y i k + (1 / (N : ℝ)) *
        ∑ j ∈ Finset.univ.erase i, rieszKernelGrad d s (Y i - Y j) k)) i k X =
    movQDensity d s β N f X * ((fderiv ℝ (movU d s q β f) (X i) (EuclideanSpace.single k (1 : ℝ))) k +
      s113x_Psi d s q β N (movU d s q β f) i k X * (movU d s q β f (X i)) k) := by
  set Q := movQDensity d s β N f with hQ
  set u := movU d s q β f with hu_def
  have hQl : ∀ Y : EucConfig d N, Y ∉ eucCollisionSet d N →
      HasDerivAt (fun τ => Q (s113x_line Y i k τ)) (Q Y * s113x_Psi d s q β N u i k Y) 0 :=
    fun Y hY => s113x_Q_line hβ hf hpos hΓ hY i k
  have hmp : ∀ Y : EucConfig d N, Y ∉ eucCollisionSet d N →
      movPartial Q i k Y = Q Y * s113x_Psi d s q β N u i k Y :=
    fun Y hY => (hQl Y hY).deriv
  have hnc := s113x_line_noncoll X i k hX
  -- second derivative
  have hA : HasDerivAt (fun τ => movPartial Q i k (s113x_line X i k τ))
      (Q X * s113x_Psi d s q β N u i k X * s113x_Psi d s q β N u i k X + Q X * (β * ((fderiv ℝ u (X i)
        (EuclideanSpace.single k (1 : ℝ))) k - (q + (1 / (N : ℝ)) * ∑ j ∈ Finset.univ.erase i,
        (fderiv ℝ (rieszKernelGrad d s) (X i - X j) (EuclideanSpace.single k (1 : ℝ))) k)))) 0 := by
    have := (hQl X hX).mul (s113x_Psi_line_hasDerivAt s q β hu hX i k)
    simp only [s113x_line_zero] at this
    refine this.congr_of_eventuallyEq ?_
    filter_upwards [hnc] with τ hτ
    exact hmp _ hτ
  have hB : HasDerivAt (fun τ => Q (s113x_line X i k τ) * s113x_drift d s q N i k (s113x_line X i k τ))
      (Q X * s113x_Psi d s q β N u i k X * s113x_drift d s q N i k X + Q X * (q + (1 / (N : ℝ)) * ∑ j ∈ Finset.univ.erase i,
        (fderiv ℝ (rieszKernelGrad d s) (X i - X j) (EuclideanSpace.single k (1 : ℝ))) k)) 0 := by
    have := (hQl X hX).mul (s113x_drift_line_hasDerivAt s q hX i k)
    simp only [s113x_line_zero] at this
    exact this
  have e1 : movPartial (movPartial Q i k) i k X = Q X * s113x_Psi d s q β N u i k X * s113x_Psi d s q β N u i k X +
      Q X * (β * ((fderiv ℝ u (X i) (EuclideanSpace.single k (1 : ℝ))) k - (q + (1 / (N : ℝ)) * ∑ j ∈ Finset.univ.erase i,
        (fderiv ℝ (rieszKernelGrad d s) (X i - X j) (EuclideanSpace.single k (1 : ℝ))) k))) := hA.deriv
  have e2 : movPartial (fun Y => Q Y * (q * Y i k + (1 / (N : ℝ)) *
        ∑ j ∈ Finset.univ.erase i, rieszKernelGrad d s (Y i - Y j) k)) i k X =
      Q X * s113x_Psi d s q β N u i k X * s113x_drift d s q N i k X + Q X * (q + (1 / (N : ℝ)) * ∑ j ∈ Finset.univ.erase i,
        (fderiv ℝ (rieszKernelGrad d s) (X i - X j) (EuclideanSpace.single k (1 : ℝ))) k) := hB.deriv
  rw [e1, e2]
  have hΨ : s113x_Psi d s q β N u i k X = β * (u (X i) k - s113x_drift d s q N i k X) := rfl
  rw [hΨ]
  field_simp
  ring


theorem s113x_movFP_eq {s q β : ℝ} (hβ : β ≠ 0) {f : Euc d → ℝ} (hf : ∀ x, DifferentiableAt ℝ f x)
    (hpos : ∀ x, 0 < f x)
    (hΓ : ∀ x, HasFDerivAt (HRS.Whole.convMeasure (rieszKernel d s) (HRS.Whole.withDensityReal f))
      (innerSL ℝ (movForce d s f x)) x)
    (hu : Differentiable ℝ (movU d s q β f)) {X : EucConfig d N} (hX : X ∉ eucCollisionSet d N) :
    movFP d s q β N (movQDensity d s β N f) X =
      movQDensity d s β N f X * ∑ i, (movDiv (movU d s q β f) (X i) +
        ∑ k, s113x_Psi d s q β N (movU d s q β f) i k X * (movU d s q β f (X i)) k) := by
  unfold movFP
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hdiv : movDiv (movU d s q β f) (X i) =
      ∑ k, (fderiv ℝ (movU d s q β f) (X i) (EuclideanSpace.single k (1 : ℝ))) k := rfl
  rw [hdiv, ← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  exact s113x_fp_term hβ hf hpos hΓ hu hX i k

end HRS.MS.S113BD

end
