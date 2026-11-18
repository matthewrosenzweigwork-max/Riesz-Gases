import HRS.MS.QsfAsm1

/-!
# S4.5 packet B5 (assembly), part 2: the vector Stein identity

`s45_vec_stein`: for `n` features `φ_i` with correctors `χ_i`, `f ∈ C_b^∞(ℝⁿ)` with bounded `Df` and
`Y = (√N(μ_N - ν)(φ_i))_{i<n}` (`ν = m_N`), `P = canonicalGibbs`:
`E[Y_i f(Y)] = E[√N R_i f(Y)] + ∑_j E[T_ij ∂_j f(Y)]`, `T_ij = β⁻¹ μ_N(∇χ_i · ∇φ_j)`.
-/

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal RealInnerProductSpace ContDiff

noncomputable section

namespace S45

open HRS.Whole
open HRS (Euc cbNorm MemCb)

variable {d N : ℕ}

/-- The canonical Gibbs law of S4.5. -/
abbrev s45_P (d : ℕ) (s a β : ℝ) (N : ℕ) : Measure (EucConfig d N) :=
  canonicalGibbs (rieszKernel d s) (confinement a) N β

/-- Its one-particle marginal `m_N`. -/
abbrev s45_nu (d : ℕ) (s a β : ℝ) (N : ℕ) : Measure (Euc d) :=
  firstMarginal (s45_P d s a β N)

/-- The data of one corrected feature. -/
structure S45Feat (d : ℕ) (s a β : ℝ) (φ χ : Euc d → ℝ) (B : ℝ) : Prop where
  smooth : ContDiff ℝ 2 χ
  B1 : ∀ x, ‖gradient χ x‖ ≤ B
  B2 : ∀ x, ‖fderiv ℝ (gradient χ) x‖ ≤ B
  corr : ∀ᵐ x ∂(thermalMeasure d s a β),
    susceptibilityOp (rieszKernel d s) (thermalMeasure d s a β) β (thermalGen d s a β χ) x =
      projMean (thermalMeasure d s a β) φ x
  r2 : MemLp (thermalGen d s a β χ) 2 (thermalMeasure d s a β)

theorem s45_norm_fderiv_gradient {χ : Euc d → ℝ} (hχ : ContDiff ℝ 2 χ) (x : Euc d) :
    ‖fderiv ℝ (gradient χ) x‖ ≤ ‖iteratedFDeriv ℝ 2 χ x‖ := by
  have hd : DifferentiableAt ℝ (fderiv ℝ χ) x :=
    (hχ.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) x
  have h : gradient χ = (InnerProductSpace.toDual ℝ (Euc d)).symm.toContinuousLinearEquiv ∘ fderiv ℝ χ := rfl
  have e : ‖iteratedFDeriv ℝ 2 χ x‖ = ‖fderiv ℝ (fderiv ℝ χ) x‖ := by
    rw [← norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_one]
  rw [h, ContinuousLinearEquiv.comp_fderiv, e]
  refine ContinuousLinearMap.opNorm_le_bound _ (ContinuousLinearMap.opNorm_nonneg _) fun w => ?_
  show ‖(InnerProductSpace.toDual ℝ (Euc d)).symm (fderiv ℝ (fderiv ℝ χ) x w)‖ ≤ _
  rw [LinearIsometryEquiv.norm_map]
  exact (fderiv ℝ (fderiv ℝ χ) x).le_opNorm w

/-- A `k = 1` thermal corrector yields the data `S45Feat`, with `B = C ‖φ‖`. -/
theorem s45_feat_of_corrector {s a β C normφ : ℝ} {φ χ : Euc d → ℝ}
    (h : IsThermalCorrector d s a β β 1 φ normφ C χ) : S45Feat d s a β φ χ (C * normφ) := by
  obtain ⟨-, h2, hr, hc, -, hb⟩ := h
  have h2' : ContDiff ℝ 2 χ := by
    have e : (((1 : ℕ) : WithTop ℕ∞) + 1) = 2 := by norm_num
    rwa [e] at h2
  have hbd : ∀ y, ‖iteratedFDeriv ℝ 1 χ y‖ + ‖iteratedFDeriv ℝ 2 χ y‖ ≤ C * normφ := fun y => by
    have := hb (fun _ => y)
    simpa [Fin.sum_univ_two] using this
  refine ⟨h2', fun x => ?_, fun x => ?_, hc, hr⟩
  · rw [s45_norm_gradient, ← norm_iteratedFDeriv_one]
    linarith [hbd x, norm_nonneg (iteratedFDeriv ℝ 2 χ x)]
  · refine (s45_norm_fderiv_gradient h2' x).trans ?_
    linarith [hbd x, norm_nonneg (iteratedFDeriv ℝ 1 χ x)]

theorem s45_fderiv_eq_inner (ψ : Euc d → ℝ) (x v : Euc d) : fderiv ℝ ψ x v = ⟪gradient ψ x, v⟫ := by
  unfold gradient
  rw [InnerProductSpace.toDual_symm_apply]

theorem s45_cb_deriv_le {J : ℕ} (hJ : 1 ≤ J) {ψ : Euc d → ℝ} (hψ : MemCb J ψ) (x : Euc d) :
    ‖fderiv ℝ ψ x‖ ≤ cbNorm J ψ := by
  rw [← norm_iteratedFDeriv_one]
  have h1 : ‖iteratedFDeriv ℝ 1 ψ x‖ ≤ ⨆ z : Euc d, ‖iteratedFDeriv ℝ 1 ψ z‖ :=
    le_ciSup (hψ.2 1 hJ) x
  refine h1.trans ?_
  unfold cbNorm
  exact Finset.single_le_sum (f := fun j => ⨆ z : Euc d, ‖iteratedFDeriv ℝ j ψ z‖)
    (fun j _ => Real.iSup_nonneg fun _ => norm_nonneg _) (by simp; omega)

end S45

end
