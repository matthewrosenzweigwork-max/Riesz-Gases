import HRS.Uniform.Q54cAux53

/-!
# Q54c, part 54: the time integrand of the weak mean-field formulation is bounded
-/

noncomputable section

open MeasureTheory Filter Topology Set

namespace HRS.Uniform.Q54c

open HRS HRS.PDE

variable {d : ℕ}

/-- the time integrand of `IsMeanFieldSolution.weak` -/
def wkG (D : DynData d) (ρ : ℝ → Torus d → ℝ) (ψ : Torus d → ℝ) (r : ℝ) : ℝ :=
  pair (withDensityReal (ρ r)) (fun x => D.invβ * Torus.laplacian ψ x -
      inner ℝ (Torus.grad D.V x) (Torus.grad ψ x)) +
    interactionPairing D ψ (withDensityReal (ρ r)) (withDensityReal (ρ r))

theorem weak_eq_wkG {D : DynData d} {T : ℝ} {ρ : ℝ → Torus d → ℝ} (hmf : IsMeanFieldSolution D T ρ)
    {ψ : Torus d → ℝ} (hψ : Torus.IsCk 2 ψ) {t : ℝ} (ht : t ∈ Icc 0 T) :
    pair (withDensityReal (ρ t)) ψ - pair (withDensityReal (ρ 0)) ψ = ∫ r in Icc 0 t, wkG D ρ ψ r :=
  hmf.weak ψ hψ t ht

theorem pair_wDR {g : Torus d → ℝ} (hg : IsProbDensity g) (ψ : Torus d → ℝ) :
    pair (withDensityReal g) ψ = ∫ x, ψ x * g x := by
  unfold pair
  rw [HRS.PDE.MFPairing.integral_withDensityReal hg.measurable hg.nonneg]
  exact integral_congr_ae (Eventually.of_forall fun x => mul_comm _ _)

theorem isCk_one_of_two {ψ : Torus d → ℝ} (hψ : Torus.IsCk 2 ψ) : Torus.IsCk 1 ψ :=
  ContDiff.of_le hψ (by exact_mod_cast (by norm_num : (1 : ℕ) ≤ 2))

theorem exists_matVec_bound (M : Matrix (Fin d) (Fin d) ℝ) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ v : Euc d, ‖Torus.matVec M v‖ ≤ c * ‖v‖ := by
  refine ⟨‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin M)‖, norm_nonneg _, fun v => ?_⟩
  exact (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin M)).le_opNorm v

theorem norm_le_cbNorm_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {φ : Torus d → E}
    (hφ : Torus.IsCk 0 φ) (x : Torus d) : ‖φ x‖ ≤ Torus.cbNorm 0 φ := by
  have := HRS.KernelGrad.norm_iteratedFDeriv_le_cbNorm (φ := φ) (k := 0) hφ (j := 0) le_rfl (Torus.rep x)
  rw [norm_iteratedFDeriv_zero] at this
  simpa [Torus.lift, Torus.mk_rep] using this

theorem wkG_bound (hd : 1 ≤ d) (D : DynData d) (T Λ : ℝ) (K : ℕ) (hK : 1 ≤ K)
    (hV : Torus.IsCk 1 D.V) (ρ : ℝ → Torus d → ℝ)
    (hρ : ∀ r ∈ Icc 0 T, IsProbDensity (ρ r) ∧ Torus.IsCk K (ρ r) ∧ Torus.cbNorm K (ρ r) ≤ Λ)
    (ψ : Torus d → ℝ) (hψ : Torus.IsCk 2 ψ) : ∃ C : ℝ, ∀ r ∈ Icc 0 T, |wkG D ρ ψ r| ≤ C := by
  have hψ1 := isCk_one_of_two hψ
  have hLc : Continuous (fun x => D.invβ * Torus.laplacian ψ x -
      inner ℝ (Torus.grad D.V x) (Torus.grad ψ x)) := by
    refine (continuous_const.mul (HRS.PDE.MFApriori.continuous_laplacian_of_isCk hψ)).sub ?_
    exact (HRS.PDE.MFLinear.continuous_grad hV).inner (HRS.PDE.MFLinear.continuous_grad hψ1)
  obtain ⟨B1, hB1⟩ := (isCompact_univ (X := Torus d)).exists_bound_of_continuousOn hLc.continuousOn
  have hgc : Continuous (Torus.grad ψ) := HRS.PDE.MFLinear.continuous_grad hψ1
  obtain ⟨B2, hB2⟩ := (isCompact_univ (X := Torus d)).exists_bound_of_continuousOn hgc.continuousOn
  obtain ⟨cM, hcM0, hcM⟩ := exists_matVec_bound D.M
  obtain ⟨Cc, hCc⟩ := HRS.PDE.convGradConv_cbNorm_of_one_le (d := d) (s := D.s) hd D.hs0 D.hsd 0
  refine ⟨B1 + B2 * (cM * (|Cc| * Λ)), fun r hr => ?_⟩
  obtain ⟨hp, hck, hcb⟩ := hρ r hr
  have hρc : Continuous (ρ r) := by
    have : ContDiff ℝ 0 (Torus.lift (ρ r)) := ContDiff.of_le hck (by exact_mod_cast (by omega : (0 : ℕ) ≤ K))
    exact Torus.continuous_of_continuous_lift this.continuous
  have hρint : Integrable (ρ r) := hρc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hρ1 : Torus.IsCk 1 (ρ r) := ContDiff.of_le hck (by exact_mod_cast hK)
  have hρ1' : Torus.IsCk (0 + 1) (ρ r) := hρ1
  have part1 : |pair (withDensityReal (ρ r)) (fun x => D.invβ * Torus.laplacian ψ x -
      inner ℝ (Torus.grad D.V x) (Torus.grad ψ x))| ≤ B1 := by
    rw [pair_wDR hp]
    have h1 : |∫ x, (D.invβ * Torus.laplacian ψ x - inner ℝ (Torus.grad D.V x) (Torus.grad ψ x)) * ρ r x| ≤
        ∫ x, |(D.invβ * Torus.laplacian ψ x - inner ℝ (Torus.grad D.V x) (Torus.grad ψ x)) * ρ r x| := by
      simpa [Real.norm_eq_abs] using norm_integral_le_integral_norm
        (fun x => (D.invβ * Torus.laplacian ψ x - inner ℝ (Torus.grad D.V x) (Torus.grad ψ x)) * ρ r x)
    refine h1.trans ?_
    calc _ ≤ ∫ x, B1 * ρ r x := by
          refine integral_mono ?_ (hρint.const_mul B1) fun x => ?_
          · exact ((hLc.mul hρc).abs).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
          · simp only
            rw [abs_mul, abs_of_nonneg (hp.nonneg x)]
            exact mul_le_mul_of_nonneg_right (by simpa [Real.norm_eq_abs] using hB1 x (mem_univ _)) (hp.nonneg x)
      _ = B1 := by rw [integral_const_mul, hp.integral_one, mul_one]
  have part2 : |interactionPairing D ψ (withDensityReal (ρ r)) (withDensityReal (ρ r))| ≤
      B2 * (cM * (|Cc| * Λ)) := by
    rw [HRS.PDE.MFPairing.interactionPairing_eq_of_isCk hd D (ρ r) hρ1 hp.nonneg ψ hψ]
    have hcc := hCc (ρ r) hρ1'
    generalize hwdef : convGradConv (periodicRieszGrad d D.s) (ρ r) = w at hcc ⊢
    have hw : ∀ x, ‖w x‖ ≤ |Cc| * Λ := by
      intro x
      refine (norm_le_cbNorm_zero hcc.1 x).trans (hcc.2.trans ?_)
      have h1 : Torus.cbNorm 1 (ρ r) ≤ Λ := (HRS.KernelGrad.cbNorm_mono hK).trans hcb
      have h2 := HRS.KernelGrad.cbNorm_nonneg' (ρ r) 1
      calc Cc * Torus.cbNorm (0 + 1) (ρ r) ≤ |Cc| * Torus.cbNorm 1 (ρ r) :=
            mul_le_mul_of_nonneg_right (le_abs_self _) h2
        _ ≤ |Cc| * Λ := mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
    have hwc : Continuous w := Torus.continuous_of_continuous_lift hcc.1.continuous
    have hbd : ∀ x, |ρ r x * inner ℝ (Torus.grad ψ x) (Torus.matVec D.M (w x))| ≤
        B2 * (cM * (|Cc| * Λ)) * ρ r x := by
      intro x
      rw [abs_mul, abs_of_nonneg (hp.nonneg x), mul_comm]
      refine mul_le_mul_of_nonneg_right ?_ (hp.nonneg x)
      refine (abs_real_inner_le_norm _ _).trans ?_
      have h1 : ‖Torus.grad ψ x‖ ≤ B2 := hB2 x (mem_univ _)
      have h2 := hcM (w x)
      have h3 := hw x
      exact mul_le_mul h1 (h2.trans (mul_le_mul_of_nonneg_left h3 hcM0)) (norm_nonneg _)
        ((norm_nonneg _).trans h1)
    have hmc : Continuous (fun x => Torus.matVec D.M (w x)) :=
      (LinearMap.continuous_of_finiteDimensional (Matrix.toEuclideanLin D.M)).comp hwc
    have hFc : Continuous (fun x => ρ r x * inner ℝ (Torus.grad ψ x) (Torus.matVec D.M (w x))) :=
      hρc.mul (hgc.inner hmc)
    have h1 : |∫ x, ρ r x * inner ℝ (Torus.grad ψ x) (Torus.matVec D.M (w x))| ≤
        ∫ x, |ρ r x * inner ℝ (Torus.grad ψ x) (Torus.matVec D.M (w x))| := by
      simpa [Real.norm_eq_abs] using norm_integral_le_integral_norm
        (fun x => ρ r x * inner ℝ (Torus.grad ψ x) (Torus.matVec D.M (w x)))
    refine h1.trans ?_
    calc _ ≤ ∫ x, B2 * (cM * (|Cc| * Λ)) * ρ r x :=
          integral_mono (hFc.abs.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
            (hρint.const_mul _) hbd
      _ = B2 * (cM * (|Cc| * Λ)) := by rw [integral_const_mul, hp.integral_one, mul_one]
  unfold wkG
  exact (abs_add_le _ _).trans (add_le_add part1 part2)

end HRS.Uniform.Q54c
