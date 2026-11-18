import HRS.Main.ThermLin2Dy5

/-!
# THERMLIN 2, packet `Dy`, part 6: `tl2_Delta_bound` (plan statement B2)

`‖(𝓛_r - 𝓛_β)ψ‖_{H^{m-a₀}} ≤ C e^{-κ r} ‖ψ‖_{H^m}` for smooth `ψ`, from `exists_forwardGen_diff`
(`i = m`, `r₀ = d/2 + m + 1`) and the relaxation `ρ^r → ρβ` in `H^{r₀}` (`finite_reg_decay`).  Uses no plan statement.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.ThermLin.Plan2

open HRS HRS.Uniform

variable {d : ℕ}

open HRS.PDE HRS.PDE.MFAdjoint in
/-- Relaxation `ρ^t → ρβ` in `H^r` for the coefficients of the density `S.ρ t` (copy of `thermlin_rho_decay`
with the identification `coeffOf (S.ρ t) = ρc t` and `C¹` regularity of `S.ρ t`). -/
theorem tl2dy_rho_decay (S : HRS.Main.PreparedData d) {ρβ : Torus d → ℝ}
    (h : IsThermalDensity (periodicRiesz d S.s) S.V S.β ρβ) (r : ℝ) (hr : 0 ≤ r) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ t : ℝ, 0 ≤ t →
      Torus.IsCk 1 (S.ρ t) ∧ MemHs r (coeffOf (S.ρ t)) ∧ MemHs r (coeffOf (S.ρ t) - coeffOf ρβ) ∧
        PDE.hsNorm r (coeffOf (S.ρ t) - coeffOf ρβ) ≤ C * Real.exp (-c * t) := by
  obtain ⟨hsm, hpos⟩ := HRS.ThermLin.thermlin_thermal_smooth_pos S h
  have hd2 : 2 ≤ d := S.hd
  obtain ⟨K, hK⟩ : ∃ K : ℕ, max r ((d : ℝ) / 2 + 6) < K := exists_nat_gt _
  have hK6 : (d : ℝ) / 2 + 6 < K := lt_of_le_of_lt (le_max_right _ _) hK
  have hKr : r < K := lt_of_le_of_lt (le_max_left _ _) hK
  obtain ⟨ρc, hρc, hρ⟩ := S.hρ K hK6
  have htr := HRS.T25.t25_traj S
  have H := Q40b.q40b_finiteRegHyp htr hK6
  obtain ⟨C, c, hC, hc, hdec⟩ := PDE.finite_reg_decay (by omega) S.s S.β S.β K S.V S.ρ0 H r hr hKr
  have hreal := PDE.MFGlobal.isRealCoeff_of_isMFSolutionHK (by omega) S.s S.β S.β K S.V S.ρ0 H S.β
    ⟨le_rfl, le_rfl⟩ ρc hρc
  have hKd : (d : ℝ) / 2 < K := by linarith
  refine ⟨C, c, hC, hc, fun t ht => ?_⟩
  have hMemK : MemHs (K : ℝ) (ρc t) := hρc.cont.1 t ht
  have hco : coeffOf (S.ρ t) = ρc t := by
    rw [← hρ]
    exact coeffOf_toFun _ (hreal t ht) (summable_norm_of_memHs (K : ℝ) hKd _ hMemK)
  have hdd := hdec S.β ⟨le_rfl, le_rfl⟩ ρc hρc ρβ h (HRS.StaticLimitAux.continuous_of_smooth hsm) hpos
    (PDE.MFSemigroup.memSobolev_of_isSmooth hsm K) t ht
  obtain ⟨Cn, hCn⟩ := toFun_isCk_le (d := d) 1 (K : ℝ) (by push_cast; linarith)
  have hCk : Torus.IsCk 1 (S.ρ t) := by
    rw [← hρ]
    exact (hCn _ hMemK (hreal t ht)).1
  rw [hco]
  exact ⟨hCk, MemHs.mono hKr.le hMemK, hdd.1, hdd.2⟩

open HRS.PDE HRS.PDE.MFAdjoint in
/-- (B2) `P:eq:Gaussian-forcing` on smooth tests. -/
theorem tl2_Delta_bound_proof (S : HRS.Main.PreparedData d) {ρβ : Torus d → ℝ}
    (h : IsThermalDensity (periodicRiesz d S.s) S.V S.β ρβ) (m : ℝ) (hm : (d : ℝ) + 2 < m) :
    ∃ C κ : ℝ, 0 ≤ C ∧ 0 < κ ∧ ∀ r : ℝ, 0 ≤ r → ∀ ψ : Torus d → ℝ, Torus.IsSmooth ψ →
      MemSobolev (m - PDE.MFAdjoint.aExp d S.s) (tl2Delta S ρβ r ψ) ∧
      sobolevNorm (m - PDE.MFAdjoint.aExp d S.s) (tl2Delta S ρβ r ψ) ≤
        C * Real.exp (-κ * r) * sobolevNorm m ψ := by
  obtain ⟨hsm, hpos⟩ := HRS.ThermLin.thermlin_thermal_smooth_pos S h
  have hd1 : 1 ≤ d := by have := S.hd; omega
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hm1 : (1 : ℝ) ≤ m := by linarith
  set r0 : ℝ := (d : ℝ) / 2 + m + 1 with hr0def
  have hr0 : (d : ℝ) / 2 + m < r0 := by rw [hr0def]; linarith
  have hr0nn : 0 ≤ r0 := by rw [hr0def]; linarith
  obtain ⟨Cd, hCd, hdiff⟩ := exists_forwardGen_diff hd1 S.s S.hs0 S.hsd m r0 hm1 hr0
  obtain ⟨Cρ, cρ, hCρ, hcρ, hρd⟩ := tl2dy_rho_decay S h r0 hr0nn
  refine ⟨Cd * Cρ, cρ, mul_nonneg hCd hCρ.le, hcρ, fun r hr ψ hψ => ?_⟩
  obtain ⟨hC1, hM, hMd, hN⟩ := hρd r hr
  have hρβM : MemHs r0 (coeffOf ρβ) := (hsNormSq_coeffOf r0 ρβ (PDE.MFSemigroup.memSobolev_of_isSmooth hsm r0)).1
  have hψS : MemSobolev m ψ := PDE.MFSemigroup.memSobolev_of_isSmooth hψ m
  have hψC2 : Torus.IsCk 2 ψ := PDE.MFSemigroup.isCk_nat_of_isSmooth hψ 2
  have hK := PDE.ClassicalAux.convKernelFacts hd1 S.dyn
  have hV1 : Torus.IsCk 1 S.dyn.V := PDE.MFSemigroup.isCk_nat_of_isSmooth S.hV 1
  have hρβ1 : Torus.IsCk 1 ρβ := PDE.MFSemigroup.isCk_nat_of_isSmooth hsm 1
  have hb1 := PDE.MFSemigroup.continuous_backwardGenerator S.dyn hK hV1 hC1 hψC2
  have hb2 := PDE.MFSemigroup.continuous_backwardGenerator S.dyn hK hV1 hρβ1 hψC2
  have hΔc : Continuous (tl2Delta S ρβ r ψ) := hb1.sub hb2
  have e2 : coeffOf (tl2Delta S ρβ r ψ) =
      forwardGen S.dyn (S.ρ r) (coeffOf ψ) - forwardGen S.dyn ρβ (coeffOf ψ) := by
    show coeffOf (fun x => backwardGenerator S.dyn (S.ρ r) ψ x - backwardGenerator S.dyn ρβ ψ x) = _
    rw [PDE.ET.coeffOf_sub_fun hb1 hb2, PDE.ClassicalAux.coeffOf_backwardGenerator S.dyn hK hV1 hC1 hψC2,
      PDE.ClassicalAux.coeffOf_backwardGenerator S.dyn hK hV1 hρβ1 hψC2]
  have hcm : MemHs m (coeffOf ψ) := (hsNormSq_coeffOf m ψ hψS).1
  obtain ⟨hmem, hnorm⟩ := hdiff S.dyn rfl rfl (S.ρ r) ρβ (PDE.MFAux.continuous_of_isCk hC1)
    (PDE.MFAux.continuous_of_isCk hρβ1) hM hρβM (coeffOf ψ) hcm
  have hΔS : MemSobolev (m - PDE.MFAdjoint.aExp d S.s) (tl2Delta S ρβ r ψ) :=
    memSobolev_of_memHs _ _ (PDE.ClassicalAux.memLp_two_of_continuous hΔc) (by rw [e2]; exact hmem)
  refine ⟨hΔS, ?_⟩
  have hnn : 0 ≤ sobolevNorm (m - PDE.MFAdjoint.aExp d S.s) (tl2Delta S ρβ r ψ) := Real.sqrt_nonneg _
  have heq : PDE.hsNorm (m - PDE.MFAdjoint.aExp d S.s) (coeffOf (tl2Delta S ρβ r ψ)) =
      sobolevNorm (m - PDE.MFAdjoint.aExp d S.s) (tl2Delta S ρβ r ψ) := by
    unfold PDE.hsNorm
    rw [(hsNormSq_coeffOf _ _ hΔS).2, Real.sqrt_sq hnn]
  have heqψ : PDE.hsNorm m (coeffOf ψ) = sobolevNorm m ψ := by
    have hnnψ : 0 ≤ sobolevNorm m ψ := Real.sqrt_nonneg _
    unfold PDE.hsNorm
    rw [(hsNormSq_coeffOf _ _ hψS).2, Real.sqrt_sq hnnψ]
  rw [← heq, e2]
  refine hnorm.trans ?_
  rw [heqψ]
  have hψn : 0 ≤ sobolevNorm m ψ := Real.sqrt_nonneg _
  calc Cd * PDE.hsNorm r0 (coeffOf (S.ρ r) - coeffOf ρβ) * sobolevNorm m ψ
      ≤ Cd * (Cρ * Real.exp (-cρ * r)) * sobolevNorm m ψ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hN hCd) hψn
    _ = Cd * Cρ * Real.exp (-cρ * r) * sobolevNorm m ψ := by ring

example := (@tl2_Delta_bound_proof : type_of% @tl2_Delta_bound)

end HRS.ThermLin.Plan2
