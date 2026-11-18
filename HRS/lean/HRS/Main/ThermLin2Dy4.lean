import HRS.Main.ThermLin2Dy3

/-!
# THERMLIN 2, packet `Dy`, part 4: facts on the frozen propagator for continuous `H^{j'}` data
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.ThermLin.Plan2

open HRS HRS.Uniform

variable {d : ℕ}

theorem tl2dy_memSob_mono {γ m : ℝ} (hγm : γ ≤ m) {ψ : Torus d → ℝ} (h : MemSobolev m ψ) :
    MemSobolev γ ψ := by
  refine ⟨h.1, ?_⟩
  refine Summable.of_nonneg_of_le (fun k => mul_nonneg (Real.rpow_nonneg (Torus.jp_pos _).le _) (sq_nonneg _))
    (fun k => ?_) h.2
  exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le (Torus.jp_ge_one _) (by linarith))
    (sq_nonneg _)

theorem tl2dy_sobNorm_mono {γ m : ℝ} (hγm : γ ≤ m) {ψ : Torus d → ℝ} (h : MemSobolev m ψ) :
    sobolevNorm γ ψ ≤ sobolevNorm m ψ := by
  unfold sobolevNorm
  refine Real.sqrt_le_sqrt (add_le_add le_rfl ?_)
  exact (tl2dy_memSob_mono hγm h).2.tsum_le_tsum (fun k =>
    mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le (Torus.jp_ge_one _) (by linarith))
      (sq_nonneg _)) h.2

open HRS.PDE HRS.PDE.MFAdjoint in
/-- Facts on the frozen propagator `U^β_{u,r}ψ` for continuous `ψ ∈ H^{j'}`, `u < r`: its coefficients are
`frozenCoeff`, it lies in `H^{j'}`, with a growth bound with an exponent independent of `ψ, u, r`. -/
theorem tl2dy_frozen_facts (S : HRS.Main.PreparedData d) {ρβ : Torus d → ℝ}
    (h : IsThermalDensity (periodicRiesz d S.s) S.V S.β ρβ) (j' : ℕ) (hj' : PDE.mStar d ≤ j') :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ {ψ : Torus d → ℝ}, Continuous ψ → MemSobolev (j' : ℝ) ψ → ∀ {u r : ℝ}, 0 ≤ u → u < r →
      coeffOf (tl2Ub S ρβ u r ψ) = frozenCoeff S.dyn ρβ j' (coeffOf ψ) (r - u) ∧
      MemSobolev (j' : ℝ) (tl2Ub S ρβ u r ψ) ∧
      sobolevNorm (j' : ℝ) (tl2Ub S ρβ u r ψ) ≤ Real.exp (L * (r - u)) * sobolevNorm (j' : ℝ) ψ := by
  obtain ⟨hsm, hpos⟩ := HRS.ThermLin.thermlin_thermal_smooth_pos S h
  have hd1 : 1 ≤ d := by have := S.hd; omega
  have hprob : IsProbDensity ρβ := h.1
  have h3 : 3 ≤ PDE.mStar d := PDE.ClassicalPart.three_le_mStar d
  have hj1 : 1 ≤ j' := by omega
  obtain ⟨R, MB, Λ, VB, hA⟩ :=
    PDE.MFSemigroup.adjointData_frozen S.s S.hs0 S.hsd S.β S.hβ S.V S.hV ρβ hprob hsm hpos j'
  obtain ⟨C, Cs, -, -, hmain⟩ :=
    PDE.adjoint_torus_classical hd1 S.s S.hs0 S.hsd j' hj' R MB Λ VB
  obtain ⟨C1, hC1, hspec⟩ := PDE.propagatorCoeff_spec hd1 S.s S.hs0 S.hsd j' hj1 R MB Λ VB
  refine ⟨|R.lambdaM (Cs j') 0 (PDE.thetaOrder d S.s)|, abs_nonneg _, fun {ψ} hψc hψS {u r} hu hlt => ?_⟩
  have hr : 0 < r - u := sub_pos.2 hlt
  have hmj : (PDE.mStar d : ℝ) ≤ j' := by exact_mod_cast hj'
  obtain ⟨hcls, hpe, hbd, -⟩ := hmain S.dyn 0 (r - u) (fun _ => ρβ) (hA 0 (r - u) hr) (r - u)
    ⟨hr, le_rfl⟩ ψ hψc hψS
  have hshift := tl2dy_shift_gen S h hψc (tl2dy_memSob_mono hmj hψS) hu hlt
  have hfun : tl2Ub S ρβ u r ψ =
      fun x => PDE.toFun (frozenCoeff S.dyn ρβ j' (coeffOf ψ) (r - u)) x := by
    rw [hshift]
    have := hpe 0 ⟨le_rfl, hr.le⟩
    simpa [tl2Ub, frozenCoeff] using this
  have hcm : PDE.MemHs (j' : ℝ) (coeffOf ψ) := (PDE.hsNormSq_coeffOf _ ψ hψS).1
  have hre : PDE.IsRealCoeff (coeffOf ψ) :=
    PDE.isRealCoeff_coeffOf ψ (PDE.ClassicalAux.integrable_of_continuous hψc)
  have hreal := PDE.ClassicalPart.propagatorCoeff_real hd1 S.s S.hs0 S.hsd j' hj1 R MB Λ VB S.dyn 0 (r - u)
    (fun _ => ρβ) (hA 0 (r - u) hr) (r - u) ⟨hr, le_rfl⟩ (coeffOf ψ) hcm hre (r - u) ⟨hr.le, le_rfl⟩
  obtain ⟨-, hw, -⟩ := hspec S.dyn 0 (r - u) (fun _ => ρβ) (hA 0 (r - u) hr) (r - u) ⟨hr, le_rfl⟩ (coeffOf ψ) hcm
  have hmem := hw.1 (r - u) ⟨hr.le, le_rfl⟩
  have hjd : (d : ℝ) / 2 < j' := by
    have hfl := Nat.lt_floor_add_one ((d : ℝ) / 2)
    have : (PDE.mStar d : ℝ) = (⌊(d : ℝ) / 2⌋₊ : ℝ) + 3 := by unfold PDE.mStar; push_cast; ring
    linarith
  have hsum := PDE.summable_norm_of_memHs (j' : ℝ) hjd _ hmem
  refine ⟨?_, ?_, ?_⟩
  · rw [hfun]
    exact PDE.coeffOf_toFun _ hreal hsum
  · rw [hshift]
    exact (hbd j' hj1 le_rfl 0 ⟨le_rfl, hr.le⟩).1
  · rw [hshift]
    refine ((hbd j' hj1 le_rfl 0 ⟨le_rfl, hr.le⟩).2).trans ?_
    refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 ?_) (Real.sqrt_nonneg _)
    rw [sub_zero]
    exact mul_le_mul_of_nonneg_right (le_abs_self _) hr.le

open HRS.PDE HRS.PDE.MFAdjoint in
/-- Facts on the moving propagator `f_r = U^{r,t}φ` and on `ψ_r = (𝓛_r - 𝓛_β) f_r`, `φ` smooth, level `j = j' + 2`. -/
theorem tl2dy_moving_facts (S : HRS.Main.PreparedData d) {ρβ : Torus d → ℝ}
    (h : IsThermalDensity (periodicRiesz d S.s) S.V S.β ρβ) (j' : ℕ) (hj' : PDE.mStar d ≤ j')
    (hjd : (d : ℝ) / 2 + 2 < j') {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ) {t : ℝ} (ht : 0 < t) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ r ∈ Set.Icc (0 : ℝ) t,
      coeffOf (propagator S.dyn S.ρ r t φ) =
        propagatorCoeff S.dyn S.ρ ((j' + 2 : ℕ) : ℝ) t (coeffOf φ) (t - r) ∧
      Torus.IsCk 2 (propagator S.dyn S.ρ r t φ) ∧
      MemSobolev ((j' + 2 : ℕ) : ℝ) (propagator S.dyn S.ρ r t φ) ∧
      Continuous (tl2Delta S ρβ r (propagator S.dyn S.ρ r t φ)) ∧
      coeffOf (tl2Delta S ρβ r (propagator S.dyn S.ρ r t φ)) =
        forwardGen S.dyn (S.ρ r) (propagatorCoeff S.dyn S.ρ ((j' + 2 : ℕ) : ℝ) t (coeffOf φ) (t - r)) -
          forwardGen S.dyn ρβ (propagatorCoeff S.dyn S.ρ ((j' + 2 : ℕ) : ℝ) t (coeffOf φ) (t - r)) ∧
      MemSobolev (j' : ℝ) (tl2Delta S ρβ r (propagator S.dyn S.ρ r t φ)) ∧
      sobolevNorm (j' : ℝ) (tl2Delta S ρβ r (propagator S.dyn S.ρ r t φ)) ≤ B := by
  obtain ⟨hsm, hpos⟩ := HRS.ThermLin.thermlin_thermal_smooth_pos S h
  have hd1 : 1 ≤ d := by have := S.hd; omega
  have hprob : IsProbDensity ρβ := h.1
  have h3 : 3 ≤ PDE.mStar d := PDE.ClassicalPart.three_le_mStar d
  set j : ℕ := j' + 2 with hjdef
  have hj : (d : ℝ) / 2 + 4 < (j : ℝ) := by rw [hjdef]; push_cast; linarith
  have hj1 : 1 ≤ j' := by omega
  have hj1' : 1 ≤ j := by omega
  have hjms : PDE.mStar d ≤ j := by omega
  obtain ⟨R, Λ, hAtAll⟩ := tl2dy_moving S h j hj
  have hAt := hAtAll t ht
  obtain ⟨R', MB', Λ', VB', hAfAll⟩ :=
    PDE.MFSemigroup.adjointData_frozen S.s S.hs0 S.hsd S.β S.hβ S.V S.hV ρβ hprob hsm hpos j'
  have hAf := hAfAll 0 t ht
  obtain ⟨C, Cs, -, -, hmain⟩ :=
    PDE.adjoint_torus_classical hd1 S.s S.hs0 S.hsd j hjms R 1 Λ (Torus.cbNorm (j + 3) S.V)
  have hφc : Continuous φ := PDE.MFAux.continuous_of_isCk (PDE.MFSemigroup.isCk_nat_of_isSmooth hφ 1)
  have hφS : MemSobolev (j : ℝ) φ := PDE.MFSemigroup.memSobolev_of_isSmooth hφ _
  have hcm : MemHs (j : ℝ) (coeffOf φ) := (PDE.hsNormSq_coeffOf _ φ hφS).1
  have hre : IsRealCoeff (coeffOf φ) := isRealCoeff_coeffOf φ (PDE.ClassicalAux.integrable_of_continuous hφc)
  obtain ⟨hcls, hpe, hbd, -⟩ := hmain S.dyn S.β⁻¹ t S.ρ hAt t ⟨ht, le_rfl⟩ φ hφc hφS
  obtain ⟨C1, hC1, hspec⟩ := propagatorCoeff_spec hd1 S.s S.hs0 S.hsd j hj1' R 1 Λ (Torus.cbNorm (j + 3) S.V)
  obtain ⟨-, hw, hb⟩ := hspec S.dyn S.β⁻¹ t S.ρ hAt t ⟨ht, le_rfl⟩ (coeffOf φ) hcm
  have hreal := PDE.ClassicalPart.propagatorCoeff_real hd1 S.s S.hs0 S.hsd j hj1' R 1 Λ
    (Torus.cbNorm (j + 3) S.V) S.dyn S.β⁻¹ t S.ρ hAt t ⟨ht, le_rfl⟩ (coeffOf φ) hcm hre
  have hAμm := PDE.StabAux.adjointData_mono (by omega : j' ≤ j) hAt
  obtain ⟨c1, hc1, hgen1⟩ := forwardGen_hsNorm_le hd1 S.hs0 S.hsd j' 1 Λ (Torus.cbNorm (j + 3) S.V) S.dyn
    hAt.hs hAt.hM hAμm.hV
  obtain ⟨c2, hc2, hgen2⟩ := forwardGen_hsNorm_le hd1 S.hs0 S.hsd j' MB' Λ' VB' S.dyn hAf.hs hAf.hM hAf.hV
  have hr0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) t := ⟨le_rfl, ht.le⟩
  set lam := R.lambdaM C1 S.β⁻¹ (PDE.thetaOrder d S.s) with hlam
  set B0 : ℝ := Real.exp (|lam| * t) * PDE.hsNorm (j : ℝ) (coeffOf φ) with hB0def
  have hB0 : ∀ σ ∈ Set.Icc (0 : ℝ) t,
      PDE.hsNorm (j : ℝ) (propagatorCoeff S.dyn S.ρ (j : ℝ) t (coeffOf φ) σ) ≤ B0 := by
    intro σ hσ
    refine (hb σ hσ).trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 ?_) (hsNorm_nonneg' _ _))
    have h3 := le_abs_self lam
    have h4 := abs_nonneg lam
    nlinarith [hσ.1, hσ.2]
  have hB0nn : 0 ≤ B0 := mul_nonneg (Real.exp_pos _).le (hsNorm_nonneg' _ _)
  refine ⟨(c1 + c2) * B0, mul_nonneg (add_nonneg hc1 hc2) hB0nn, fun r hr => ?_⟩
  have hσ : t - r ∈ Set.Icc (0 : ℝ) t := PDE.ClassicalAux.mem_Icc_sub t hr
  have hMem := hw.1 (t - r) hσ
  have hjd2 : (d : ℝ) / 2 < (j : ℝ) := by linarith
  have e1 : coeffOf (propagator S.dyn S.ρ r t φ) =
      propagatorCoeff S.dyn S.ρ (j : ℝ) t (coeffOf φ) (t - r) := by
    rw [hpe r hr]
    exact PDE.coeffOf_toFun _ (hreal _ hσ) (PDE.summable_norm_of_memHs _ hjd2 _ hMem)
  have hC2 : Torus.IsCk 2 (propagator S.dyn S.ρ r t φ) := by
    rw [hpe r hr]
    exact hcls.c2 r hr
  have hK := PDE.ClassicalAux.convKernelFacts hd1 S.dyn
  have hV1 : Torus.IsCk 1 S.dyn.V :=
    PDE.ClassicalAux.isCk_of_le (by exact_mod_cast (by omega : 1 ≤ j + 3)) hAt.hV.1
  have hρ1 : Torus.IsCk 1 (S.ρ r) :=
    PDE.ClassicalAux.isCk_of_le (by exact_mod_cast (by omega : 1 ≤ j + 3)) (hAt.hμ.smooth r hr)
  have hρβ1 : Torus.IsCk 1 ρβ := PDE.MFSemigroup.isCk_nat_of_isSmooth hsm 1
  have hb1 := PDE.MFSemigroup.continuous_backwardGenerator S.dyn hK hV1 hρ1 hC2
  have hb2 := PDE.MFSemigroup.continuous_backwardGenerator S.dyn hK hV1 hρβ1 hC2
  have hΔc : Continuous (tl2Delta S ρβ r (propagator S.dyn S.ρ r t φ)) := hb1.sub hb2
  have e2 : coeffOf (tl2Delta S ρβ r (propagator S.dyn S.ρ r t φ)) =
      forwardGen S.dyn (S.ρ r) (propagatorCoeff S.dyn S.ρ (j : ℝ) t (coeffOf φ) (t - r)) -
        forwardGen S.dyn ρβ (propagatorCoeff S.dyn S.ρ (j : ℝ) t (coeffOf φ) (t - r)) := by
    show coeffOf (fun x => backwardGenerator S.dyn (S.ρ r) (propagator S.dyn S.ρ r t φ) x -
      backwardGenerator S.dyn ρβ (propagator S.dyn S.ρ r t φ) x) = _
    rw [PDE.ET.coeffOf_sub_fun hb1 hb2, PDE.ClassicalAux.coeffOf_backwardGenerator S.dyn hK hV1 hρ1 hC2,
      PDE.ClassicalAux.coeffOf_backwardGenerator S.dyn hK hV1 hρβ1 hC2, e1]
  have hMem2 : MemHs ((j' + 2 : ℕ) : ℝ) (propagatorCoeff S.dyn S.ρ (j : ℝ) t (coeffOf φ) (t - r)) := hMem
  have hgm1 := hgen1 (S.ρ r) (hAμm.hμ.prob r hr) (hAμm.hμ.smooth r hr) (hAμm.hμ.bound r hr) _ hMem2
  have hgm2 := hgen2 ρβ (hAf.hμ.prob 0 hr0) (hAf.hμ.smooth 0 hr0) (hAf.hμ.bound 0 hr0) _ hMem2
  have hEm := memHs_sub hgm1.1 hgm2.1
  have hEn := (hsNorm_sub_le_add hgm1.1 hgm2.1).trans (add_le_add
    (hgm1.2.trans (mul_le_mul_of_nonneg_left (hB0 _ hσ) hc1))
    (hgm2.2.trans (mul_le_mul_of_nonneg_left (hB0 _ hσ) hc2)))
  have hΔS : MemSobolev (j' : ℝ) (tl2Delta S ρβ r (propagator S.dyn S.ρ r t φ)) :=
    memSobolev_of_memHs _ _ (PDE.ClassicalAux.memLp_two_of_continuous hΔc) (by rw [e2]; exact hEm)
  refine ⟨e1, hC2, (hbd j hj1' le_rfl r hr).1, hΔc, e2, hΔS, ?_⟩
  have hsq := (PDE.hsNormSq_coeffOf _ _ hΔS).2
  have hnn : 0 ≤ sobolevNorm (j' : ℝ) (tl2Delta S ρβ r (propagator S.dyn S.ρ r t φ)) := Real.sqrt_nonneg _
  have heq : PDE.hsNorm (j' : ℝ) (coeffOf (tl2Delta S ρβ r (propagator S.dyn S.ρ r t φ))) =
      sobolevNorm (j' : ℝ) (tl2Delta S ρβ r (propagator S.dyn S.ρ r t φ)) := by
    unfold PDE.hsNorm
    rw [hsq, Real.sqrt_sq hnn]
  rw [← heq, e2]
  calc _ ≤ c1 * B0 + c2 * B0 := hEn
    _ = (c1 + c2) * B0 := by ring

end HRS.ThermLin.Plan2
