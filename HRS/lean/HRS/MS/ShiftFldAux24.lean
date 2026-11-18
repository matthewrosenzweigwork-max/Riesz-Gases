import HRS.MS.ShiftFldAux23

/-!
# S79P: the fundamental theorem of calculus for `r ↦ C(u_r, v_r)` along backward classical solutions
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Metric Set
open scoped ENNReal NNReal BigOperators RealInnerProductSpace

namespace HRS.MS.S79G

open HRS.Whole HRS.MS.UniqT3 HRS.MS.S21 HRS.MH.DualityRd
open HRS (Euc)

variable {d : ℕ}

theorem s79g_U_eq_Pc {ν : Measure (Euc d)} [IsProbabilityMeasure ν] {f : Euc d → ℝ}
    (hf : MemLp f 2 ν) : S45.s45_U f hf = HRS.Whole.Q34.Pc ν (hf.toLp f) := by
  refine Lp.ext ?_
  rw [HRS.Whole.Q34.Pc_apply, HRS.Whole.Q34.inner_one2]
  filter_upwards [S45.s45_U_ae hf, MemLp.coeFn_toLp hf,
    Lp.coeFn_sub (hf.toLp f) ((∫ x, (hf.toLp f : Euc d → ℝ) x ∂ν) • HRS.Whole.Q34.one2 ν),
    Lp.coeFn_smul (∫ x, (hf.toLp f : Euc d → ℝ) x ∂ν) (HRS.Whole.Q34.one2 ν),
    HRS.Whole.Q34.one2_ae (ν := ν)] with x h1 h2 h3 h4 h5
  rw [h3, Pi.sub_apply, h4, Pi.smul_apply, h5, h1]
  unfold HRS.Whole.projMean HRS.Whole.pair
  rw [integral_congr_ae (MemLp.coeFn_toLp hf)]
  simp [h2]

theorem s79g_cov_neg_left {ν : Measure (Euc d)} [IsProbabilityMeasure ν] {g : Euc d → ℝ}
    {K : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν} (hK : S45.IsKData ν g K) {β : ℝ} (hβ : 0 < β)
    {f ψ : Euc d → ℝ} (hf : MemLp f 2 ν) (hψ : MemLp ψ 2 ν) :
    HRS.Whole.susceptibilityCov g ν β (fun x => -f x) ψ = -HRS.Whole.susceptibilityCov g ν β f ψ := by
  have hf' : MemLp (fun x => (-1 : ℝ) * f x) 2 ν := hf.const_mul (-1)
  have e : (fun x => -f x) = fun x => (-1 : ℝ) * f x := by funext x; ring
  rw [e, S45.s45_susceptibilityCov_eq hK hβ hf' hψ, S45.s45_susceptibilityCov_eq hK hβ hf hψ,
    S45.s45_U_smul hf (-1), real_inner_smul_left]
  ring

theorem s79g_cov_neg_right {ν : Measure (Euc d)} [IsProbabilityMeasure ν] {g : Euc d → ℝ}
    {K : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν} (hK : S45.IsKData ν g K) {β : ℝ} (hβ : 0 < β)
    {f ψ : Euc d → ℝ} (hf : MemLp f 2 ν) (hψ : MemLp ψ 2 ν) :
    HRS.Whole.susceptibilityCov g ν β f (fun x => -ψ x) = -HRS.Whole.susceptibilityCov g ν β f ψ := by
  have hψ' : MemLp (fun x => (-1 : ℝ) * ψ x) 2 ν := hψ.const_mul (-1)
  have e : (fun x => -ψ x) = fun x => (-1 : ℝ) * ψ x := by funext x; ring
  rw [e, S45.s45_susceptibilityCov_eq hK hβ hf hψ', S45.s45_susceptibilityCov_eq hK hβ hf hψ,
    S45.s45_U_smul hψ (-1), map_smul, real_inner_smul_right]
  ring

end HRS.MS.S79G
