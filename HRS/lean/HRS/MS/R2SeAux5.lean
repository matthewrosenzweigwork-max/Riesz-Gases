import HRS.MS.R2SeAux4

/-!
# S9.9 `r2_static_edgeworth`, packet 5: the exact Stein identity (E1) in `ℓ² × ℝ`

Worker S99, namespace `S99`.  For a corrector `χ` of a feature `w` (`S46Feat`), a summable feature family `φ`, an extra bounded
feature `b` and a `C¹` test function `Ψ : ℓ² × ℝ → ℝ` with bounded `Ψ, DΨ` (`F = Ψ(W_N, Y_b)`):

`E[Y_w Ψ(W,Y_b)] = E[√N R_w Ψ(W,Y_b)] + ∑_l E[T_{wl} ∂_{e_l}Ψ(W,Y_b)] + E[T_{wb} ∂_yΨ(W,Y_b)]`

with `R_w = s45_Rp ... (commutatorKernel (∇χ_w))`, `T_{wl} = γ⁻¹ μ_N(⟨∇χ_w, ∇φ_l⟩)`.  It is `S46.s46_stein_id` applied to `F = Ψ ∘ Z`,
`Z = (featureVec φ ν, Y_b)`, whose derivative is computed termwise (packet 3).
-/

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace ContDiff

noncomputable section

namespace S99

open S45
open HRS.Whole
open HRS (Euc cbNorm MemCb)

variable {d N : ℕ}

theorem s99_nu_prob {P : Measure (EucConfig d N)} [IsProbabilityMeasure P] (hN : 1 ≤ N) :
    IsProbabilityMeasure (firstMarginal P) := by
  have : firstMarginal P = P.map (fun X : EucConfig d N => X ⟨0, by omega⟩) := by
    unfold firstMarginal; rw [dif_pos (by omega)]
  rw [this]
  constructor
  rw [Measure.map_apply (measurable_pi_apply _) MeasurableSet.univ]
  simp

/-- The pair `Z = (W, Y_b) ∈ ℓ² × ℝ`. -/
def Zq (N : ℕ) (φ : ℕ → Euc d → ℝ) (b : Euc d → ℝ) (ν : Measure (Euc d)) (X : EucConfig d N) :
    SeqL2 × ℝ :=
  (featureVec φ ν X, s45_Yi N b (pair ν b) X)

theorem s99_L_chi (hN : 1 ≤ N) {ψ χ : Euc d → ℝ} (X : EucConfig d N) :
    s45_L N ψ X (fun k => gradient χ (X k)) =
      Real.sqrt N * pair (empirical X) (fun x => ⟪gradient χ x, gradient ψ x⟫) := by
  have hN' : 0 < N := hN
  have hN0 : (N : ℝ) ≠ 0 := by positivity
  rw [s45_L_apply, pair_empirical hN']
  simp_rw [s45_fderiv_eq_inner ψ, real_inner_comm (gradient χ _)]
  field_simp

section Deriv

variable {J : ℕ} {φ : ℕ → Euc d → ℝ} {b : Euc d → ℝ} {ν : Measure (Euc d)} [IsProbabilityMeasure ν]

theorem s99_Z_hasFDerivAt (hN : 1 ≤ N) (hJ : 1 ≤ J) (hφ : IsSummableFeatureFamily J φ)
    (hb : MemCb J b) (X : EucConfig d N) :
    HasFDerivAt (fun X : EucConfig d N => Zq N φ b ν X)
      ((∑' l, (s45_L N (φ l) X).smulRight (s45_e1 l (1 : ℝ))).prod (s45_L N b X)) X := by
  have h1 := s99_W_hasFDerivAt (ν := ν) hN hJ hφ X
  have h2 := s45_Yi_hasFDerivAt hN (hb.1.differentiable (by exact_mod_cast (by omega : J ≠ 0)))
    (pair ν b) X
  exact h1.prodMk h2

theorem s99_Z_contDiff (hN : 1 ≤ N) (hJ : 1 ≤ J) (hφ : IsSummableFeatureFamily J φ)
    (hb : MemCb J b) : ContDiff ℝ 1 (fun X : EucConfig d N => Zq N φ b ν X) :=
  (s99_W_contDiff (ν := ν) hN hJ hφ).prodMk
    (s45_Yi_contDiff hN (hb.1.of_le (by exact_mod_cast hJ)) _)

/-- The derivative of `Ψ ∘ Z` along `u`, termwise. -/
theorem s99_fderivF_apply (hN : 1 ≤ N) (hJ : 1 ≤ J) (hφ : IsSummableFeatureFamily J φ)
    (hb : MemCb J b) {Ψ : SeqL2 × ℝ → ℝ} (hΨ : ContDiff ℝ 1 Ψ) (X : EucConfig d N)
    (u : EucConfig d N) :
    fderiv ℝ (fun X : EucConfig d N => Ψ (Zq N φ b ν X)) X u =
      (∑' l, s45_L N (φ l) X u * fderiv ℝ Ψ (Zq N φ b ν X) (s45_e1 l (1 : ℝ), 0)) +
        s45_L N b X u * fderiv ℝ Ψ (Zq N φ b ν X) (0, 1) := by
  have hZd := s99_Z_hasFDerivAt (ν := ν) hN hJ hφ hb X
  have hΨd : Differentiable ℝ Ψ := hΨ.differentiable one_ne_zero
  have hF := (hΨd (Zq N φ b ν X)).hasFDerivAt.comp X hZd
  have hfd : fderiv ℝ (fun X : EucConfig d N => Ψ (Zq N φ b ν X)) X =
      (fderiv ℝ Ψ (Zq N φ b ν X)).comp
        ((∑' l, (s45_L N (φ l) X).smulRight (s45_e1 l (1 : ℝ))).prod (s45_L N b X)) := hF.fderiv
  rw [hfd]
  set p := Zq N φ b ν X with hp
  set G : SeqL2 →L[ℝ] ℝ := (fderiv ℝ Ψ p).comp (ContinuousLinearMap.inl ℝ SeqL2 ℝ) with hG
  have hsum : Summable fun l => (s45_L N (φ l) X).smulRight (s45_e1 l (1 : ℝ)) :=
    Summable.of_norm_bounded (hφ.2.mul_left (Real.sqrt N))
      (fun l => s99_Wterm_fderiv_norm hN hJ hφ.1 l X)
  have hA := (hsum.hasSum.mapL (ContinuousLinearMap.apply ℝ SeqL2 u)).mapL G
  have hA' : HasSum (fun l => s45_L N (φ l) X u * fderiv ℝ Ψ p (s45_e1 l (1 : ℝ), 0))
      (G ((∑' l, (s45_L N (φ l) X).smulRight (s45_e1 l (1 : ℝ))) u)) := by
    convert hA using 2 with l
    all_goals first | rfl | simp [hG, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.apply]
  have hsplit : ∀ (z : SeqL2) (t : ℝ), fderiv ℝ Ψ p (z, t) = G z + t * fderiv ℝ Ψ p (0, 1) := by
    intro z t
    have : ((z, t) : SeqL2 × ℝ) = (z, 0) + t • ((0, 1) : SeqL2 × ℝ) := by
      ext <;> simp
    rw [this, map_add, map_smul, smul_eq_mul]
    rfl
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply]
  rw [hsplit, hA'.tsum_eq]

end Deriv

end S99

end
