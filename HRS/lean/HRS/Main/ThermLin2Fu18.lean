import HRS.Main.ThermLin2Fu17

/-!
# THERMLIN2 Fu18: the `H^{m-a₀}` bound of `ψ_r = Δ_r U^{r,t} φ` with decay in both `t-r` and `r`
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.ThermLin.Plan2

open HRS HRS.Uniform HRS.GF HRS.AdjK HRS.T25P HRS.Uniform.Q54c

variable {d : ℕ}

/-- Combination of the zero-mean reduction (`Δ_r` kills constants), the bound of `Δ_r` (hypothesis `hB2`, an
instance of `tl2_Delta_bound`) and the dual decay of `U^{r,t}`. -/
theorem tl2fu_psi_shift (S : HRS.Main.PreparedData d) {ρβ : Torus d → ℝ}
    (h : IsThermalDensity (periodicRiesz d S.s) S.V S.β ρβ) (m : ℝ)
    (Vev : ℝ → ℝ → NegSobolev d m →L[ℝ] NegSobolev d m) (hVd : IsDualEvolution S.dyn S.ρ m Vev)
    {K c T' : ℝ} (hK : 0 ≤ K)
    (hdec : ∀ u t : ℝ, 0 ≤ u → u ≤ t → t ≤ T' → ‖Vev t u‖ ≤ K * Real.exp (-c * (t - u)))
    {C κ : ℝ} (hC : 0 ≤ C)
    {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ) {t : ℝ} (ht : 0 < t) (htT : t ≤ T') {r : ℝ}
    (hr : r ∈ Set.Icc (0 : ℝ) t)
    (hB2 : ∀ ψ : Torus d → ℝ, Torus.IsSmooth ψ →
      MemSobolev (m - PDE.MFAdjoint.aExp d S.s) (tl2Delta S ρβ r ψ) ∧
        sobolevNorm (m - PDE.MFAdjoint.aExp d S.s) (tl2Delta S ρβ r ψ) ≤
          C * Real.exp (-κ * r) * sobolevNorm m ψ) :
    MemSobolev (m - PDE.MFAdjoint.aExp d S.s) (tl2Delta S ρβ r (propagator S.dyn S.ρ r t φ)) ∧
      sobolevNorm (m - PDE.MFAdjoint.aExp d S.s) (tl2Delta S ρβ r (propagator S.dyn S.ρ r t φ)) ≤
        C * Real.exp (-κ * r) * (K * Real.exp (-c * (t - r)) * ‖lpFun m φ‖) := by
  set f := propagator S.dyn S.ρ r t φ with hf
  have hfs : Torus.IsSmooth f := tl2fu_prop_smooth S h hφ ht hr
  have hfc : Continuous f := tl2fu_continuous_of_smooth hfs
  have hfm : MemSobolev m f := PDE.MFSemigroup.memSobolev_of_isSmooth hfs m
  have hC2 : Torus.IsCk 2 f := by simpa using PDE.MFSemigroup.isCk_nat_of_isSmooth hfs 2
  set g : Torus d → ℝ := fun x => f x - Torus.mean f with hg
  have hgs : Torus.IsSmooth g := tl2fu_isSmooth_sub_const hfs _
  have hgm : MemSobolev m g := tl2fu_memSob_sub_const hfc hfm _
  have hΔ : tl2Delta S ρβ r g = tl2Delta S ρβ r f := by
    unfold tl2Delta
    rw [hg, tl2fu_bgen_sub_const S.dyn (S.ρ r) hC2, tl2fu_bgen_sub_const S.dyn ρβ hC2]
  obtain ⟨hmem, hnorm⟩ := hB2 g hgs
  rw [hΔ] at hmem hnorm
  refine ⟨hmem, hnorm.trans ?_⟩
  have hs : sobolevNorm m g = ‖lpFun m f‖ := by
    rw [tl2fu_sobolevNorm_zero_mean hgm (tl2fu_mean_sub_mean hfc), hg, tl2fu_lpFun_sub_const hfc hfm]
  rw [hs]
  have hd := tl2fu_dual_decay S h m Vev hVd hK hdec hφ ht htT hr
  exact mul_le_mul_of_nonneg_left hd (mul_nonneg hC (Real.exp_pos _).le)

end HRS.ThermLin.Plan2
