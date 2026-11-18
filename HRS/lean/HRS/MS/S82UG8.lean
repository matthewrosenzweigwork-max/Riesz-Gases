import HRS.MS.S82UG7

/-!
# S8.2 A04 (S82U), part 8: the three `L²` clauses of `GeneratorClosure`
For `F` that is `C²` off collisions with `|F| + ‖DF‖ + ‖D²F‖ ≤ A (1+‖X‖)^M ∏ (1+‖x_i-x_j‖^{-M})`:
`F`, `particleGenerator F` and every `configGrad F · i` lie in `L²(canonicalP)`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace

namespace HRS.MS.S82U
open HRS HRS.Whole HRS.MS.Phase2S82

section final
variable {d N : ℕ}

lemma u4Tame_of_le {g h : EucConfig d N → ℝ} (hh : u4Tame h)
    (hle : ∀ X : EucConfig d N, X ∉ eucCollisionSet d N → |g X| ≤ |h X|) : u4Tame g := by
  obtain ⟨C, p, q, hC, hp, hq, hb⟩ := hh
  exact ⟨C, p, q, hC, hp, hq, fun X hX => (hle X hX).trans (hb X hX)⟩

theorem u4_L2 (hd : 2 ≤ d) (hN : 0 < N) {a beta : ℝ} (ha : 0 < a) (hbeta : 0 < beta)
    {F : EucConfig d N → ℝ} (hF : ContDiffOn ℝ 2 F (eucCollisionSet d N)ᶜ) {M A : ℝ} (hM : 0 ≤ M) (hA : 0 ≤ A)
    (hb : ∀ X : EucConfig d N, X ∉ eucCollisionSet d N →
      |F X| + ‖fderiv ℝ F X‖ + ‖iteratedFDeriv ℝ 2 F X‖ ≤ A * u4Env M M X) :
    MemLp F 2 (canonicalP d N a beta) ∧
    MemLp (particleGenerator (quadraticGradientDyn d (criticalS d) a beta) F) 2 (canonicalP d N a beta) ∧
    ∀ i, MemLp (fun X => Phase2S82.configGrad F X i) 2 (canonicalP d N a beta) := by
  have hEnv : u4Tame (fun X : EucConfig d N => A * u4Env M M X) := by
    refine ⟨A, M, M, hA, hM, hM, fun X _ => ?_⟩
    rw [abs_of_nonneg (mul_nonneg hA (u4Env_nonneg hM X))]
  have hF0 : ∀ X, X ∉ eucCollisionSet d N → |F X| ≤ A * u4Env M M X := fun X hX => by
    have := hb X hX; have := norm_nonneg (fderiv ℝ F X); have := norm_nonneg (iteratedFDeriv ℝ 2 F X); linarith
  have hF1 : ∀ X, X ∉ eucCollisionSet d N → ‖fderiv ℝ F X‖ ≤ A * u4Env M M X := fun X hX => by
    have := hb X hX; have := abs_nonneg (F X); have := norm_nonneg (iteratedFDeriv ℝ 2 F X); linarith
  have hF2 : ∀ X, X ∉ eucCollisionSet d N → ‖iteratedFDeriv ℝ 2 F X‖ ≤ A * u4Env M M X := fun X hX => by
    have := hb X hX; have := abs_nonneg (F X); have := norm_nonneg (fderiv ℝ F X); linarith
  have hDc : ContinuousOn (fun X => fderiv ℝ F X) (eucCollisionSet d N)ᶜ :=
    hF.continuousOn_fderiv_of_isOpen u4_D_open (by norm_num)
  have hD2c : ContinuousOn (fun X => fderiv ℝ (fderiv ℝ F) X) (eucCollisionSet d N)ᶜ :=
    (hF.fderiv_of_isOpen u4_D_open (m := 1) (by norm_num)).continuousOn_fderiv_of_isOpen u4_D_open le_rfl
  -- gradient rows
  have hGradCont : ∀ i, ContinuousOn (fun X => Phase2S82.configGrad F X i) (eucCollisionSet d N)ᶜ := by
    intro i
    have h1 : ContinuousOn (fun X : EucConfig d N => (InnerProductSpace.toDual ℝ (Euc d)).symm
        ((fderiv ℝ F X).comp (u4L d N i))) (eucCollisionSet d N)ᶜ := by
      refine (InnerProductSpace.toDual ℝ (Euc d)).symm.continuous.comp_continuousOn ?_
      exact (((ContinuousLinearMap.compL ℝ (Euc d) (EucConfig d N) ℝ).flip (u4L d N i)).continuous.comp_continuousOn hDc)
    exact h1.congr fun X hX => u4_configGrad_eq hF hX i
  have hGradTame : ∀ i, u4Tame (fun X => ‖Phase2S82.configGrad F X i‖) := fun i =>
    u4Tame_of_le hEnv fun X hX => by
      rw [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (mul_nonneg hA (u4Env_nonneg hM X))]
      exact (u4_configGrad_norm_le hF hX i).trans (hF1 X hX)
  have hMemGrad : ∀ i, MemLp (fun X => Phase2S82.configGrad F X i) 2 (canonicalP d N a beta) := by
    intro i
    have hgm : AEStronglyMeasurable (fun X => Phase2S82.configGrad F X i) (canonicalP d N a beta) :=
      u4_aesm_of_contOn (d := d) (N := N) (a := a) (beta := beta) hd (hGradCont i)
    refine (memLp_two_iff_integrable_sq_norm hgm).2 ?_
    have hT := hGradTame i
    obtain ⟨C, p, q, hC, hp, hq, hb'⟩ := hT
    refine Integrable.mono' ((u4_env_L2 hd hN ha hbeta hp hq).const_mul (C ^ 2))
      (hgm.norm.pow 2) ?_
    have hae : ∀ᵐ X ∂(canonicalP d N a beta), X ∉ eucCollisionSet d N := by
      rw [ae_iff]; simpa using u4_P_coll hd N a beta
    filter_upwards [hae] with X hX
    have := hb' X hX
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc ‖Phase2S82.configGrad F X i‖ ^ 2 = |‖Phase2S82.configGrad F X i‖| ^ 2 := by rw [abs_of_nonneg (norm_nonneg _)]
      _ ≤ (C * u4Env p q X) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) this 2
      _ = C ^ 2 * u4Env p q X ^ 2 := by ring
  refine ⟨?_, ?_, hMemGrad⟩
  · exact u4Tame_memLp hd hN ha hbeta (u4Tame_of_le hEnv fun X hX => by
      rw [abs_of_nonneg (mul_nonneg hA (u4Env_nonneg hM X))]; exact hF0 X hX)
      (u4_aesm_of_contOn (d := d) (N := N) (a := a) (beta := beta) hd hF.continuousOn)
  · -- generator
    set ν := beta⁻¹ with hν
    have hgen : ∀ X : EucConfig d N, particleGenerator (quadraticGradientDyn d (criticalS d) a beta) F X =
        ν * ∑ i, Laplacian.laplacian (fun y => F (Function.update X i y)) (X i) +
          ∑ i, inner ℝ (particleDriftW (quadraticGradientDyn d (criticalS d) a beta) X i)
            (Phase2S82.configGrad F X i) := fun X => rfl
    have hcont : ContinuousOn (fun X => particleGenerator (quadraticGradientDyn d (criticalS d) a beta) F X)
        (eucCollisionSet d N)ᶜ := by
      simp_rw [hgen]
      refine ContinuousOn.add (ContinuousOn.mul continuousOn_const (continuousOn_finsetSum _ fun i _ => ?_))
        (continuousOn_finsetSum _ fun i _ => ?_)
      · have : ContinuousOn (fun X : EucConfig d N => ∑ k, fderiv ℝ (fderiv ℝ F) X
            (u4L d N i ((stdOrthonormalBasis ℝ (Euc d)) k)) (u4L d N i ((stdOrthonormalBasis ℝ (Euc d)) k)))
            (eucCollisionSet d N)ᶜ :=
          continuousOn_finsetSum _ fun k _ => (hD2c.clm_apply continuousOn_const).clm_apply continuousOn_const
        exact this.congr fun X hX => u4_laplacian_eq hF hX i
      · exact (u4_drift_cont hd a beta i).inner (hGradCont i)
    refine u4Tame_memLp hd hN ha hbeta ?_ (u4_aesm_of_contOn (d := d) (N := N) (a := a) (beta := beta) hd hcont)
    -- tameness of the generator
    set Gb : EucConfig d N → ℝ := fun X => ν * N * d + ∑ i, (∑ j ∈ Finset.univ.erase i,
      HRS.Whole.movtr_sigma (criticalS d) * ‖X i - X j‖ ^ (-(criticalS d + 1)) + a * ‖X‖) with hGb
    have hGbT : u4Tame Gb := by
      refine u4Tame_add (u4Tame_const _) (u4Tame_sum _ _ fun i _ => u4Tame_add (u4Tame_sum _ _ fun j hj => ?_)
        (u4Tame_const_mul a u4Tame_norm))
      exact u4Tame_const_mul _ (u4Tame_pole (Finset.ne_of_mem_erase hj).symm (by linarith [u4_crit_pos hd]))
    have hσ := HRS.MS.S82T.s82t_sigma_nonneg (criticalS d) (u4_crit_pos hd).le
    have hGb0 : ∀ X, 0 ≤ Gb X := fun X => by
      have hν0 : 0 ≤ ν := by positivity
      refine add_nonneg (by positivity) (Finset.sum_nonneg fun i _ => add_nonneg
        (Finset.sum_nonneg fun j _ => mul_nonneg hσ (Real.rpow_nonneg (norm_nonneg _) _))
        (mul_nonneg ha.le (norm_nonneg _)))
    refine u4Tame_of_le (u4Tame_mul hEnv hGbT) fun X hX => ?_
    rw [abs_mul, abs_of_nonneg (mul_nonneg hA (u4Env_nonneg hM X)), abs_of_nonneg (hGb0 X), hgen]
    have hAE : 0 ≤ A * u4Env M M X := mul_nonneg hA (u4Env_nonneg (q := M) hM X)
    have hlap : ∀ i, |Laplacian.laplacian (fun y => F (Function.update X i y)) (X i)| ≤ d * (A * u4Env M M X) :=
      fun i => (u4_laplacian_bound hF hX i).trans (mul_le_mul_of_nonneg_left (hF2 X hX) (Nat.cast_nonneg d))
    have hin : ∀ i, |inner ℝ (particleDriftW (quadraticGradientDyn d (criticalS d) a beta) X i)
        (Phase2S82.configGrad F X i)| ≤
        (∑ j ∈ Finset.univ.erase i, HRS.Whole.movtr_sigma (criticalS d) * ‖X i - X j‖ ^ (-(criticalS d + 1)) +
          a * ‖X‖) * (A * u4Env M M X) := by
      intro i
      refine (abs_real_inner_le_norm _ _).trans ?_
      exact mul_le_mul (u4_drift_norm_le hd hN ha.le beta hX i)
        ((u4_configGrad_norm_le hF hX i).trans (hF1 X hX)) (norm_nonneg _)
        (add_nonneg (Finset.sum_nonneg fun j _ => mul_nonneg hσ (Real.rpow_nonneg (norm_nonneg _) _))
          (mul_nonneg ha.le (norm_nonneg _)))
    have hν0 : 0 ≤ ν := by positivity
    calc |ν * ∑ i, Laplacian.laplacian (fun y => F (Function.update X i y)) (X i) +
          ∑ i, inner ℝ (particleDriftW (quadraticGradientDyn d (criticalS d) a beta) X i) (Phase2S82.configGrad F X i)|
        ≤ |ν * ∑ i, Laplacian.laplacian (fun y => F (Function.update X i y)) (X i)| +
          |∑ i, inner ℝ (particleDriftW (quadraticGradientDyn d (criticalS d) a beta) X i) (Phase2S82.configGrad F X i)| :=
          abs_add_le _ _
      _ ≤ ν * ∑ i : Fin N, d * (A * u4Env M M X) +
          ∑ i : Fin N, (∑ j ∈ Finset.univ.erase i, HRS.Whole.movtr_sigma (criticalS d) * ‖X i - X j‖ ^ (-(criticalS d + 1)) +
            a * ‖X‖) * (A * u4Env M M X) := by
          refine add_le_add ?_ ((Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => hin i))
          rw [abs_mul, abs_of_nonneg hν0]
          exact mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs _ _).trans
            (Finset.sum_le_sum fun i _ => hlap i)) hν0
      _ = (A * u4Env M M X) * Gb X := by
          simp only [hGb, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.sum_mul]
          ring

end final

end HRS.MS.S82U
