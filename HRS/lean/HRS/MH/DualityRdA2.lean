import HRS.MH.DualityRdDefs
import HRS.MH.DualityRdA1
import HRS.Whole.Q09BAux2

/-!
# DualityRd packet A2: the deterministic drift identity on `(ℝ^d)^N`

Ports `HRS.drift_pointwise` (`HRS/Stochastic/EmpiricalIto.lean:602`) with its ingredients `offdiag_identity` (`:561`),
`interactionPairing_empirical` (`:458`), `sum_fderiv_fderiv_sumLift_liftedNoise` (`:500`) and `fderiv_sumLift_lift_apply` (`:545`),
to the whole space: the configuration space is `EucConfig d N = Fin N → ℝ^d` itself, the Brownian directions are `noiseDir D`,
and the whole-space interaction pairing `interactionPairingW` is written as a finite double sum.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.DualityRd

open HRS.Whole HRS.Whole.AppendixA

variable {d : ℕ}

/-- The off-diagonal kernel of the whole-space interaction pairing (junk `0` on the diagonal). -/
def da2K (D : WholeDyn d) (ψ : Euc d → ℝ) (x y : Euc d) : ℝ :=
  if x = y then 0 else
    inner ℝ (gradient ψ x - gradient ψ y) (Torus.matVec D.M (rieszKernelGrad d D.s (x - y)))

/-- The whole-space interaction pairing of two empirical measures as a finite double sum. -/
theorem da2_interaction_empirical (D : WholeDyn d) (ψ : Euc d → ℝ) {N : ℕ} (hN : 0 < N) (Y : EucConfig d N) :
    interactionPairingW D ψ (Whole.empirical Y) (Whole.empirical Y)
      = (1 / 2 : ℝ) * ((N : ℝ)⁻¹ * ((N : ℝ)⁻¹ * ∑ i, ∑ j, da2K D ψ (Y i) (Y j))) := by
  have h1 : ∀ x : Euc d, ∫ y, (if x = y then (0 : ℝ) else inner ℝ (gradient ψ x - gradient ψ y)
      (Torus.matVec D.M (rieszKernelGrad d D.s (x - y)))) ∂(Whole.empirical Y)
      = (N : ℝ)⁻¹ * ∑ j, da2K D ψ x (Y j) := fun x => Whole.pair_empirical hN Y (da2K D ψ x)
  unfold interactionPairingW
  simp only [h1]
  have h2 : ∫ x, (N : ℝ)⁻¹ * ∑ j, da2K D ψ x (Y j) ∂(Whole.empirical Y)
      = (N : ℝ)⁻¹ * ∑ i, (N : ℝ)⁻¹ * ∑ j, da2K D ψ (Y i) (Y j) :=
    Whole.pair_empirical hN Y (fun x => (N : ℝ)⁻¹ * ∑ j, da2K D ψ x (Y j))
  rw [h2, ← Finset.mul_sum]

theorem da2_fderiv_eq_inner (g : Euc d → ℝ) (x v : Euc d) :
    fderiv ℝ g x v = inner ℝ (gradient g x) v := by
  unfold gradient
  rw [InnerProductSpace.toDual_symm_apply]

/-- The second-order term of the empirical functional along the Brownian directions. -/
theorem da2_sum_fderiv_fderiv (D : WholeDyn d) (hinv : 0 ≤ D.invβ) {N : ℕ} {g : Euc d → ℝ}
    (hg : ContDiff ℝ 2 g) (Y : EucConfig d N) :
    ∑ k : Fin N × Fin d, fderiv ℝ (fderiv ℝ (HRS.sumLift N g)) Y (noiseDir D k) (noiseDir D k)
      = (2 * D.invβ) * ((N : ℝ)⁻¹ * ∑ i : Fin N, ∑ j : Fin d,
          fderiv ℝ (fderiv ℝ g) (Y i) (EuclideanSpace.single j 1) (EuclideanSpace.single j 1)) := by
  have hc : Real.sqrt (2 * D.invβ) ^ 2 = 2 * D.invβ :=
    Real.sq_sqrt (mul_nonneg (by norm_num) hinv)
  have hσ : ∀ (i' : Fin N) (j : Fin d) (i : Fin N), noiseDir D (i', j) i
      = if i = i' then Real.sqrt (2 * D.invβ) • EuclideanSpace.single j 1 else 0 := by
    intro i' j i
    simp [noiseDir, Pi.single_apply]
  simp only [HRS.fderiv_fderiv_sumLift hg, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.sum_apply, HRS.psiComp_apply', Finset.smul_sum]
  have hk : ∀ (i' : Fin N) (j : Fin d),
      ∑ i : Fin N, (N : ℝ)⁻¹ • (fderiv ℝ (fderiv ℝ g) (Y i))
          (noiseDir D (i', j) i) (noiseDir D (i', j) i)
        = (N : ℝ)⁻¹ * (2 * D.invβ) *
          fderiv ℝ (fderiv ℝ g) (Y i') (EuclideanSpace.single j 1) (EuclideanSpace.single j 1) := by
    intro i' j
    rw [Finset.sum_eq_single i']
    · simp only [hσ, if_true, ContinuousLinearMap.map_smul,
        smul_apply, smul_eq_mul]
      linear_combination ((N : ℝ)⁻¹ * fderiv ℝ (fderiv ℝ g) (Y i')
        (EuclideanSpace.single j 1) (EuclideanSpace.single j 1)) * hc
    · intro i _ hi
      simp [hσ, hi]
    · intro h
      exact absurd (Finset.mem_univ _) h
  rw [Fintype.sum_prod_type]
  simp only [hk, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- The label-off-diagonal sum equals the symmetrised off-diagonal kernel sum (needs distinct particles or `M = 0`). -/
theorem da2_offdiag (D : WholeDyn d) (ψ : Euc d → ℝ) {N : ℕ} (Y : EucConfig d N)
    (hcol : Y ∉ eucCollisionSet d N ∨ D.M = 0) :
    ∑ i, ∑ j ∈ Finset.univ.erase i,
        inner ℝ (gradient ψ (Y i)) (Torus.matVec D.M (rieszKernelGrad d D.s (Y i - Y j)))
      = (1 / 2 : ℝ) * ∑ i, ∑ j, da2K D ψ (Y i) (Y j) := by
  rcases hcol with hcol | hM
  · have hodd : ∀ i j, Torus.matVec D.M (rieszKernelGrad d D.s (Y j - Y i))
        = -Torus.matVec D.M (rieszKernelGrad d D.s (Y i - Y j)) := by
      intro i j
      rw [show Y j - Y i = -(Y i - Y j) from (neg_sub _ _).symm, Q09B.q09b_rkg_neg]
      simp only [Torus.matVec, map_neg]
    have hsym : ∑ i, ∑ j ∈ Finset.univ.erase i,
          inner ℝ (gradient ψ (Y i))
            (Torus.matVec D.M (rieszKernelGrad d D.s (Y i - Y j)))
        = (1 / 2 : ℝ) * ∑ i, ∑ j ∈ Finset.univ.erase i,
          inner ℝ (gradient ψ (Y i) - gradient ψ (Y j))
            (Torus.matVec D.M (rieszKernelGrad d D.s (Y i - Y j))) :=
      HRS.sum_inner_offdiag_symm (fun i => gradient ψ (Y i))
        (fun i j => Torus.matVec D.M (rieszKernelGrad d D.s (Y i - Y j)))
        (fun i j => hodd i j)
    have hk : ∀ i, ∑ j, da2K D ψ (Y i) (Y j)
        = ∑ j ∈ Finset.univ.erase i, inner ℝ (gradient ψ (Y i) - gradient ψ (Y j))
            (Torus.matVec D.M (rieszKernelGrad d D.s (Y i - Y j))) := by
      intro i
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
      have h0 : da2K D ψ (Y i) (Y i) = 0 := by simp [da2K]
      rw [h0, zero_add]
      refine Finset.sum_congr rfl fun j hj => ?_
      have hne : Y i ≠ Y j := fun h => hcol ⟨i, j, (Finset.ne_of_mem_erase hj).symm, h⟩
      simp [da2K, hne]
    simp only [hk]
    exact hsym
  · simp [da2K, hM, Torus.matVec]

theorem drift_pointwise_rd_proof {N : ℕ} (hN : 0 < N) (D : WholeDyn d) (hinv : 0 ≤ D.invβ) {t : ℝ} (ht : 0 < t)
    {f ft : ℝ → Euc d → ℝ} (hf : IsC12TestRd t f ft) {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) t) (Y : EucConfig d N)
    (hcol : Y ∉ eucCollisionSet d N ∨ D.M = 0) :
    derivWithin (fun r' => (N : ℝ)⁻¹ * ∑ i, f r' (Y i)) (Set.Icc 0 t) r
      + fderiv ℝ (fun Z : EucConfig d N => (N : ℝ)⁻¹ * ∑ i, f r (Z i)) Y (fun i => particleDriftW D Y i)
      + (1 / 2 : ℝ) * ∑ k : Fin N × Fin d,
          fderiv ℝ (fderiv ℝ (fun Z : EucConfig d N => (N : ℝ)⁻¹ * ∑ i, f r (Z i))) Y (noiseDir D k) (noiseDir D k)
    = Whole.pair (Whole.empirical Y) (driftTestRd D f ft r)
      + interactionPairingW D (f r) (Whole.empirical Y) (Whole.empirical Y) := by
  have hc2 : ContDiff ℝ 2 (f r) := hf.c2 r hr
  have hd1 : Differentiable ℝ (f r) := hc2.differentiable (by norm_num)
  -- time derivative
  have hT : derivWithin (fun r' => (N : ℝ)⁻¹ * ∑ i, f r' (Y i)) (Set.Icc 0 t) r
      = (N : ℝ)⁻¹ * ∑ i, ft r (Y i) := by
    have h1 : HasDerivWithinAt (fun r' => (N : ℝ)⁻¹ * ∑ i, f r' (Y i))
        ((N : ℝ)⁻¹ * ∑ i, ft r (Y i)) (Set.Icc 0 t) r :=
      (HasDerivWithinAt.fun_sum fun i _ => hasDerivWithinAt_Icc_testRd_proof ht hf (Y i) hr).const_mul _
    exact h1.derivWithin (uniqueDiffOn_Icc ht r hr)
  -- first-order term along the particle drift
  have hF1 : fderiv ℝ (fun Z : EucConfig d N => (N : ℝ)⁻¹ * ∑ i, f r (Z i)) Y (fun i => particleDriftW D Y i)
      = (N : ℝ)⁻¹ * ∑ i, inner ℝ (gradient (f r) (Y i)) (particleDriftW D Y i) := by
    rw [show (fun Z : EucConfig d N => (N : ℝ)⁻¹ * ∑ i, f r (Z i)) = HRS.sumLift N (f r) from rfl,
      HRS.fderiv_sumLift_apply hd1 Y (fun i => particleDriftW D Y i)]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    exact da2_fderiv_eq_inner _ _ _
  -- second-order term
  have hF2 : (1 / 2 : ℝ) * ∑ k : Fin N × Fin d,
      fderiv ℝ (fderiv ℝ (fun Z : EucConfig d N => (N : ℝ)⁻¹ * ∑ i, f r (Z i))) Y (noiseDir D k) (noiseDir D k)
      = (1 / 2 : ℝ) * ((2 * D.invβ) * ((N : ℝ)⁻¹ * ∑ i, Laplacian.laplacian (f r) (Y i))) := by
    congr 1
    have hLapsum : ∑ i : Fin N, ∑ j : Fin d,
        fderiv ℝ (fderiv ℝ (f r)) (Y i) (EuclideanSpace.single j 1) (EuclideanSpace.single j 1)
        = ∑ i : Fin N, Laplacian.laplacian (f r) (Y i) :=
      Finset.sum_congr rfl fun i _ => (HRS.laplacian_eq_sum_fderiv (g := f r) (Y i)).symm
    refine (da2_sum_fderiv_fderiv D hinv hc2 Y).trans ?_
    rw [hLapsum]
  -- right-hand side pieces
  have hP : Whole.pair (Whole.empirical Y) (driftTestRd D f ft r)
      = (N : ℝ)⁻¹ * ∑ i, driftTestRd D f ft r (Y i) :=
    Whole.pair_empirical hN Y _
  have hint := da2_interaction_empirical D (f r) hN Y
  have hoff := da2_offdiag D (f r) Y hcol
  -- splitting the first-order term
  have hBi : ∀ i, inner ℝ (gradient (f r) (Y i)) (particleDriftW D Y i)
      = (1 / (N : ℝ)) * ∑ j ∈ Finset.univ.erase i,
          inner ℝ (gradient (f r) (Y i)) (Torus.matVec D.M (rieszKernelGrad d D.s (Y i - Y j)))
        - inner ℝ (gradient (f r) (Y i)) (gradient D.V (Y i)) := by
    intro i
    simp only [particleDriftW, inner_sub_right, inner_smul_right, inner_sum]
  have hsumB : ∑ i, inner ℝ (gradient (f r) (Y i)) (particleDriftW D Y i)
      = (1 / (N : ℝ)) * ∑ i, ∑ j ∈ Finset.univ.erase i,
          inner ℝ (gradient (f r) (Y i)) (Torus.matVec D.M (rieszKernelGrad d D.s (Y i - Y j)))
        - ∑ i, inner ℝ (gradient (f r) (Y i)) (gradient D.V (Y i)) := by
    simp only [hBi]
    rw [Finset.sum_sub_distrib, Finset.mul_sum]
  have hcomm : ∑ i, inner ℝ (gradient (f r) (Y i)) (gradient D.V (Y i))
      = ∑ i, inner ℝ (gradient D.V (Y i)) (gradient (f r) (Y i)) :=
    Finset.sum_congr rfl fun i _ => real_inner_comm (gradient D.V (Y i)) (gradient (f r) (Y i))
  have hsumD : ∑ i, driftTestRd D f ft r (Y i)
      = ∑ i, ft r (Y i) + D.invβ * ∑ i, Laplacian.laplacian (f r) (Y i)
        - ∑ i, inner ℝ (gradient D.V (Y i)) (gradient (f r) (Y i)) := by
    simp only [driftTestRd, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum]
  rw [hT, hF1, hF2, hP, hint]
  linear_combination (N : ℝ)⁻¹ * hsumB - (N : ℝ)⁻¹ * hcomm - (N : ℝ)⁻¹ * hsumD
    + (N : ℝ)⁻¹ * (N : ℝ)⁻¹ * hoff

end HRS.MH.DualityRd
