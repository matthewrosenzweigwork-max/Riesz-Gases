import HRS.MH.DualityRdC1b

/-!
# DualityRd packet C2: the pointwise fluctuation identity (Lemma 3.1 on `ℝ^d`)

Port of `HRS.fluc_pointwise` (`DualityProof.lean:31`) and `flucInteraction_eq` (`Duality.lean:1402`).
With `h = -𝒢ψ + β⁻¹Δψ - ∇V·∇ψ = -⟨∇ψ, M∇g*ρ⟩ + Σ_j (∇g*(ρ(Mᵀ∇ψ)_j))_j` (`generatorW_coeff`), the left side is
`⟨μ_X,h⟩ - ⟨ρ,h⟩ + B(μ_X,μ_X) - B(ρ,ρ)`.  The empirical pairings are finite sums, `C1a (2)` gives `B(μ_X,ρ)` and
`B(ρ,μ_X)` at the points `X_i` (the kernel is symmetric), and `C1b (5),(6)` gives `⟨ρ,h⟩ = 2B(ρ,ρ)`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.DualityRd

open HRS.Whole HRS.Whole.AppendixA

variable {d : ℕ}

theorem dc2_matVec_neg (M : Matrix (Fin d) (Fin d) ℝ) (v : Euc d) :
    Torus.matVec M (-v) = -Torus.matVec M v := by
  unfold Torus.matVec
  exact map_neg _ _

/-- The kernel is symmetric (`pairKernelRd` is even under swapping its arguments). -/
theorem dc2_K_symm (D : WholeDyn d) (ψ : Euc d → ℝ) (x y : Euc d) :
    pairKernelRd D ψ x y = pairKernelRd D ψ y x := by
  by_cases h : x = y
  · subst h
    rfl
  · have h' : y ≠ x := fun e => h e.symm
    unfold pairKernelRd
    rw [if_neg h, if_neg h']
    have e1 : gradient ψ y - gradient ψ x = -(gradient ψ x - gradient ψ y) := (neg_sub _ _).symm
    have e2 : rieszKernelGrad d D.s (y - x) = -rieszKernelGrad d D.s (x - y) := by
      rw [← neg_sub x y, HRS.Whole.Q09B.q09b_rkg_neg]
    rw [e1, e2, dc2_matVec_neg, inner_neg_left, inner_neg_right, neg_neg]

/-- The symmetrised pairing as a double integral of the kernel. -/
theorem dc2_B_eq (D : WholeDyn d) (ψ : Euc d → ℝ) (ν ν' : Measure (Euc d)) :
    interactionPairingW D ψ ν ν' = (1 / 2 : ℝ) * ∫ x, ∫ y, pairKernelRd D ψ x y ∂ν' ∂ν := rfl

/-- The empirical pairing is the normalised sum of point values (also for `N = 0`, both sides vanish). -/
theorem dc2_pair_emp {N : ℕ} (X : EucConfig d N) (φ : Euc d → ℝ) :
    Whole.pair (Whole.empirical X) φ = (N : ℝ)⁻¹ * ∑ i, φ (X i) := by
  rcases Nat.eq_zero_or_pos N with h | h
  · subst h
    simp [Whole.pair, Whole.empirical]
  · exact Whole.pair_empirical h X φ

theorem dc2_core (D : WholeDyn d) (hd : 1 ≤ d) (hs0 : 0 ≤ D.s) (hsd : D.s < d) {N : ℕ}
    {ρ : Euc d → ℝ} (hρ : RegSliceRd ρ) {ψ : Euc d → ℝ} (hψ : MemCb 2 ψ) (X : EucConfig d N)
    (h : Euc d → ℝ)
    (hh : ∀ x, h x = -(inner ℝ (gradient ψ x)
        (Torus.matVec D.M (convGradConvW (rieszKernelGrad d D.s) ρ x))) + nlTermRd D ρ ψ x) :
    (Whole.pair (Whole.empirical X) h + interactionPairingW D ψ (Whole.empirical X) (Whole.empirical X))
      - (Whole.pair (Whole.withDensityReal ρ) h
          + interactionPairingW D ψ (Whole.withDensityReal ρ) (Whole.withDensityReal ρ))
      = flucInteractionRd D ψ X ρ := by
  obtain ⟨hA1, hA2, hA3, hA4⟩ := pairing_expansion_rd_proof D hd hs0 hsd hρ hψ
  obtain ⟨hB1, hB2⟩ := self_pairing_rd_proof D hd hs0 hsd hρ hψ
  have hP : Whole.IsProbDensity ρ := by unfold RegSliceRd at hρ; exact hρ.1
  have hρm : Measurable ρ := hP.measurable
  have hρnn : ∀ y, 0 ≤ ρ y := hP.nonneg
  -- the pairing with the empirical measure, and the density
  have hK_int : ∀ i : Fin N, Integrable (fun x => ρ x * pairKernelRd D ψ x (X i)) := fun i =>
    (hA1 (X i)).congr (Filter.Eventually.of_forall fun x => by dsimp only; rw [dc2_K_symm])
  have hval : ∀ i : Fin N, ∫ x, ρ x * pairKernelRd D ψ x (X i)
      = inner ℝ (gradient ψ (X i)) (Torus.matVec D.M (convGradConvW (rieszKernelGrad d D.s) ρ (X i)))
        - nlTermRd D ρ ψ (X i) := fun i => by
    have e := dc1a_integral_withDensity hρm hρnn (fun y => pairKernelRd D ψ (X i) y)
    have e2 : (fun x => ρ x * pairKernelRd D ψ x (X i)) = fun x => ρ x * pairKernelRd D ψ (X i) x :=
      funext fun x => by rw [dc2_K_symm]
    rw [e2, ← e]
    exact hA2 (X i)
  -- (1) the empirical part of the left side
  have hL1 : Whole.pair (Whole.empirical X) h = -((N : ℝ)⁻¹ * ∑ i, (inner ℝ (gradient ψ (X i))
      (Torus.matVec D.M (convGradConvW (rieszKernelGrad d D.s) ρ (X i)))
        - nlTermRd D ρ ψ (X i))) := by
    rw [dc2_pair_emp, ← mul_neg, ← Finset.sum_neg_distrib]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by rw [hh (X i)]; ring
  -- (2) the density part of the left side
  have hL2 : Whole.pair (Whole.withDensityReal ρ) h = -2 * ∫ x, ρ x * inner ℝ (gradient ψ x)
      (Torus.matVec D.M (convGradConvW (rieszKernelGrad d D.s) ρ x)) := by
    show ∫ x, h x ∂(Whole.withDensityReal ρ) = _
    rw [dc1a_integral_withDensity hρm hρnn h]
    have e : ∫ x, ρ x * h x = ∫ x, (-(ρ x * inner ℝ (gradient ψ x)
        (Torus.matVec D.M (convGradConvW (rieszKernelGrad d D.s) ρ x)))
          + ρ x * nlTermRd D ρ ψ x) :=
      integral_congr_ae (Filter.Eventually.of_forall fun x => by dsimp only; rw [hh x]; ring)
    have hA3' : Integrable (fun x => -(ρ x * inner ℝ (gradient ψ x)
        (Torus.matVec D.M (convGradConvW (rieszKernelGrad d D.s) ρ x)))) := hA3.neg
    rw [e, integral_add hA3' hA4, integral_neg, hB2]
    ring
  -- (3) the pairings of the empirical measure with the density
  have hBμν : interactionPairingW D ψ (Whole.empirical X) (Whole.withDensityReal ρ)
      = (1 / 2 : ℝ) * ((N : ℝ)⁻¹ * ∑ i, (inner ℝ (gradient ψ (X i))
          (Torus.matVec D.M (convGradConvW (rieszKernelGrad d D.s) ρ (X i)))
            - nlTermRd D ρ ψ (X i))) := by
    rw [dc2_B_eq]
    congr 1
    have e : ∫ x, (∫ y, pairKernelRd D ψ x y ∂(Whole.withDensityReal ρ)) ∂(Whole.empirical X)
        = ∫ x, (inner ℝ (gradient ψ x) (Torus.matVec D.M (convGradConvW (rieszKernelGrad d D.s) ρ x))
            - nlTermRd D ρ ψ x) ∂(Whole.empirical X) :=
      integral_congr_ae (Filter.Eventually.of_forall fun x => hA2 x)
    rw [e]
    exact dc2_pair_emp X _
  have hBνμ : interactionPairingW D ψ (Whole.withDensityReal ρ) (Whole.empirical X)
      = (1 / 2 : ℝ) * ((N : ℝ)⁻¹ * ∑ i, (inner ℝ (gradient ψ (X i))
          (Torus.matVec D.M (convGradConvW (rieszKernelGrad d D.s) ρ (X i)))
            - nlTermRd D ρ ψ (X i))) := by
    rw [dc2_B_eq]
    congr 1
    have e : ∀ x, (∫ y, pairKernelRd D ψ x y ∂(Whole.empirical X))
        = (N : ℝ)⁻¹ * ∑ i, pairKernelRd D ψ x (X i) := fun x => dc2_pair_emp X _
    simp only [e]
    rw [dc1a_integral_withDensity hρm hρnn]
    calc ∫ x, ρ x * ((N : ℝ)⁻¹ * ∑ i, pairKernelRd D ψ x (X i))
        = ∫ x, ∑ i, (N : ℝ)⁻¹ * (ρ x * pairKernelRd D ψ x (X i)) :=
          integral_congr_ae (Filter.Eventually.of_forall fun x => by
            dsimp only
            rw [Finset.mul_sum, Finset.mul_sum]
            exact Finset.sum_congr rfl fun i _ => by ring)
      _ = ∑ i, ∫ x, (N : ℝ)⁻¹ * (ρ x * pairKernelRd D ψ x (X i)) :=
          integral_finsetSum _ fun i _ => (hK_int i).const_mul _
      _ = ∑ i, (N : ℝ)⁻¹ * ∫ x, ρ x * pairKernelRd D ψ x (X i) :=
          Finset.sum_congr rfl fun i _ => integral_const_mul _ _
      _ = (N : ℝ)⁻¹ * ∑ i, (inner ℝ (gradient ψ (X i))
          (Torus.matVec D.M (convGradConvW (rieszKernelGrad d D.s) ρ (X i)))
            - nlTermRd D ρ ψ (X i)) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => by rw [hval i]
  -- assemble
  unfold flucInteractionRd
  rw [hL1, hL2, hBμν, hBνμ, hB1]
  ring

theorem fluc_pointwise_rd_proof (D : WholeDyn d) (hd : 1 ≤ d) (hs0 : 0 ≤ D.s) (hsd : D.s < d) {N : ℕ}
    (ρ' : ℝ → Euc d → ℝ) {r : ℝ} (hρ : RegSliceRd (ρ' r)) {ψ : Euc d → ℝ} (hψ : MemCb 2 ψ)
    (X : EucConfig d N) :
    (Whole.pair (Whole.empirical X) (fun x => -(generatorW (D.coeff ρ') r ψ x)
        + D.invβ * Laplacian.laplacian ψ x - inner ℝ (gradient D.V x) (gradient ψ x))
      + interactionPairingW D ψ (Whole.empirical X) (Whole.empirical X))
    - (Whole.pair (Whole.withDensityReal (ρ' r)) (fun x => -(generatorW (D.coeff ρ') r ψ x)
        + D.invβ * Laplacian.laplacian ψ x - inner ℝ (gradient D.V x) (gradient ψ x))
      + interactionPairingW D ψ (Whole.withDensityReal (ρ' r)) (Whole.withDensityReal (ρ' r)))
    = flucInteractionRd D ψ X (ρ' r) :=
  dc2_core D hd hs0 hsd hρ hψ X _ fun x => by
    rw [generatorW_coeff, meanFieldDriftW, inner_sub_left,
      real_inner_comm (gradient ψ x) (Torus.matVec D.M (convGradConvW (rieszKernelGrad d D.s) (ρ' r) x))]
    ring

end HRS.MH.DualityRd
