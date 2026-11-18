import HRS.MS.SA16SHw3

/-!
# S.A.16 (SA16S) Hw4: the weak heat identity for the gain operator (packet P5b)

`sa16sw_heat_weak`: for `ν > 0`, `ψ ∈ C_c^∞` (with `Δψ ∈ C_c^∞`), `y ∈ WmpSpace d k p`, `s > 0`:
`ℓ_ψ(Γ_{νs} y) = ℓ_ψ(y) + ∫_0^s ν ℓ_{Δψ}(Γ_{νσ} y) dσ`.  `sa16sw_heatWeak`: the predicate `SA16RHeatWeak` with `χ = sa16r_lap ψ`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer

section Hw4
variable {d : ℕ} {p : ℝ} [Fact (2 ≤ p)]

/-- the derivative of `a ↦ ∫ (g_a ⋆ φ) ψ` -/
lemma sa16sw_F_hasDerivAt {a0 : ℝ} (ha0 : 0 < a0) {φ ψ : Euc d → ℝ} (hφ : IsCcInfty φ)
    (hψ : IsCcInfty ψ) :
    HasDerivAt (fun a => ∫ x, sa16r_cv (sa16r_g d a) φ x * ψ x)
      (∫ x, sa16r_cv (sa16r_g d a0) φ x * sa16r_lap ψ x) a0 := by
  have h := sa16sw_outer_hasDerivAt ha0 hφ hψ
  have e : ∫ x, sa16r_cv (sa16r_g d a0) (sa16r_lap φ) x * ψ x =
      ∫ x, sa16r_cv (sa16r_g d a0) φ x * sa16r_lap ψ x := by
    rw [← sa16sw_lap_cv ha0 hφ]
    exact sa16sw_green (sa16r_cv_contDiff ha0 hφ) hψ
  rwa [e] at h

lemma sa16sw_ell_GamT_cc {ν : ℝ} {σ : ℝ} (hνσ : 0 < ν * σ) (k : ℕ) {φ : Euc d → ℝ} (hφ : IsCcInfty φ)
    {ψ : Euc d → ℝ} (hψ : IsCcInfty ψ) :
    sa16r_ell d (k + 1) p hψ (sa16r_GamT d k p ν σ (sa16r_cc_elt hφ k)) =
      ∫ x, sa16r_cv (sa16r_g d (ν * σ)) φ x * ψ x := by
  rw [sa16r_ell_apply]
  refine integral_congr_ae ?_
  filter_upwards [sa16r_Gam_cc (p := p) hνσ k hφ] with x hx
  rw [show sa16r_GamT d k p ν σ = sa16r_Gam d k p (ν * σ) from rfl, hx]

lemma sa16sw_ell_cc {k : ℕ} {φ : Euc d → ℝ} (hφ : IsCcInfty φ) {ψ : Euc d → ℝ} (hψ : IsCcInfty ψ) :
    sa16r_ell d k p hψ (sa16r_cc_elt hφ k) = ∫ x, φ x * ψ x := by
  rw [sa16r_ell_apply]
  refine integral_congr_ae ?_
  filter_upwards [sa16r_cc_elt_wrep (p := p) hφ k] with x hx
  rw [hx]

/-- the weak heat identity on jets of `C_c^∞` -/
theorem sa16sw_weak_cc {ν : ℝ} (hν : 0 < ν) (k : ℕ) {φ : Euc d → ℝ} (hφ : IsCcInfty φ) {ψ : Euc d → ℝ}
    (hψ : IsCcInfty ψ) (hχ : IsCcInfty (sa16r_lap ψ)) {s : ℝ} (hs : 0 < s) :
    sa16r_ell d (k + 1) p hψ (sa16r_GamT d k p ν s (sa16r_cc_elt hφ k)) =
      sa16r_ell d k p hψ (sa16r_cc_elt hφ k) +
        ∫ σ in (0 : ℝ)..s, ν * sa16r_ell d (k + 1) p hχ (sa16r_GamT d k p ν σ (sa16r_cc_elt hφ k)) := by
  set y : WmpSpace d k p := sa16r_cc_elt hφ k with hy
  set G : ℝ → ℝ := fun σ => sa16r_ell d (k + 1) p hψ (sa16r_GamT d k p ν σ y) with hG
  set f : ℝ → ℝ := fun σ => ν * sa16r_ell d (k + 1) p hχ (sa16r_GamT d k p ν σ y) with hf
  -- derivative
  have hderiv : ∀ σ : ℝ, 0 < σ → HasDerivAt G (f σ) σ := by
    intro σ hσ
    have hνσ : 0 < ν * σ := mul_pos hν hσ
    have h1 := sa16sw_F_hasDerivAt hνσ hφ hψ
    have h2 : HasDerivAt (fun σ : ℝ => ν * σ) ν σ := by simpa using (hasDerivAt_id σ).const_mul ν
    have h3 := h1.scomp σ h2
    have e1 : G =ᶠ[𝓝 σ] fun σ => ∫ x, sa16r_cv (sa16r_g d (ν * σ)) φ x * ψ x := by
      filter_upwards [Ioi_mem_nhds hσ] with τ hτ
      exact sa16sw_ell_GamT_cc (mul_pos hν hτ) k hφ hψ
    have e2 : f σ = ν • ∫ x, sa16r_cv (sa16r_g d (ν * σ)) φ x * sa16r_lap ψ x := by
      simp only [hf, smul_eq_mul]
      rw [sa16sw_ell_GamT_cc hνσ k hφ hχ]
    refine HasDerivAt.congr_of_eventuallyEq ?_ e1
    rw [e2]
    simpa [Function.comp_def, mul_comm] using h3
  -- limit of G at 0+
  have hlim : Tendsto G (𝓝[>] 0) (𝓝 (sa16r_ell d k p hψ y)) := by
    have hH := sa16r_H_tendsto_cc (p := p) k ⟨φ, hφ⟩
    have hν' : Tendsto (fun ε : ℝ => ν * ε) (𝓝[>] 0) (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
      · have h := (Continuous.tendsto (f := fun ε : ℝ => ν * ε) (by fun_prop) 0)
        rw [mul_zero] at h
        exact h.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with ε hε
        exact mul_pos hν hε
    have h2 := ((sa16r_ell d (k + 1) p hψ).continuous.tendsto _).comp (hH.comp hν')
    have hGe : ∀ ε : ℝ, G ε = (sa16r_ell d (k + 1) p hψ) (sa16r_H d k p (ν * ε)
        (sa16r_Jcc d (k + 1) p ⟨φ, hφ⟩)) := by
      intro ε
      simp only [hG, sa16r_H, ContinuousLinearMap.comp_apply, sa16r_GamT]
      rw [sa16r_iota_Jcc, sa16r_Jcc_eq]
    have hval : sa16r_ell d (k + 1) p hψ (sa16r_Jcc d (k + 1) p ⟨φ, hφ⟩) = sa16r_ell d k p hψ y := by
      rw [sa16r_Jcc_eq, hy, sa16sw_ell_cc hφ hψ, sa16sw_ell_cc hφ hψ]
    rw [hval] at h2
    refine h2.congr (fun ε => ?_)
    simp only [Function.comp_apply]
    exact (hGe ε).symm
  -- FTC on [ε, s]
  have hii := sa16sw_f_ii hν hχ k y hs
  have hftc : ∀ ε : ℝ, 0 < ε → ε ≤ s → ∫ σ in ε..s, f σ = G s - G ε := by
    intro ε hε hεs
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt (fun σ hσ => ?_) ?_
    · rw [uIcc_of_le hεs] at hσ
      exact hderiv σ (lt_of_lt_of_le hε hσ.1)
    · refine hii.mono_set ?_
      rw [uIcc_of_le hεs, uIcc_of_le hs.le]
      exact Icc_subset_Icc hε.le le_rfl
  have hT1 : Tendsto (fun ε : ℝ => ∫ σ in ε..s, f σ) (𝓝[>] 0) (𝓝 (G s - sa16r_ell d k p hψ y)) := by
    have : Tendsto (fun ε : ℝ => G s - G ε) (𝓝[>] 0) (𝓝 (G s - sa16r_ell d k p hψ y)) :=
      tendsto_const_nhds.sub hlim
    refine this.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT hs] with ε hε
    exact (hftc ε hε.1 hε.2.le).symm
  have hT2 : Tendsto (fun ε : ℝ => ∫ σ in ε..s, f σ) (𝓝[>] 0) (𝓝 (∫ σ in (0 : ℝ)..s, f σ)) := by
    have hc := intervalIntegral.continuousOn_primitive_interval' hii (a := 0) (by simp [uIcc_of_le hs.le, hs.le])
    have h0 : Tendsto (fun ε : ℝ => ∫ σ in (0 : ℝ)..ε, f σ) (𝓝[>] 0) (𝓝 0) := by
      have h1 : ContinuousWithinAt (fun ε : ℝ => ∫ σ in (0 : ℝ)..ε, f σ) (Icc 0 s) 0 := by
        have := hc 0 (by simp [uIcc_of_le hs.le, hs.le])
        rwa [uIcc_of_le hs.le] at this
      have h2 := h1.tendsto
      simp only [intervalIntegral.integral_same] at h2
      exact h2.mono_left (nhdsWithin_le_iff.2 (Icc_mem_nhdsGT hs))
    have : Tendsto (fun ε : ℝ => (∫ σ in (0 : ℝ)..s, f σ) - ∫ σ in (0 : ℝ)..ε, f σ) (𝓝[>] 0)
        (𝓝 ((∫ σ in (0 : ℝ)..s, f σ) - 0)) := tendsto_const_nhds.sub h0
    rw [sub_zero] at this
    refine this.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT hs] with ε hε
    rw [intervalIntegral.integral_interval_sub_left hii (hii.mono_set (by
      rw [uIcc_of_le hs.le, uIcc_of_le hε.1.le]; exact Icc_subset_Icc le_rfl hε.2.le))]
  have := tendsto_nhds_unique hT1 hT2
  linarith

/-- **The weak heat identity for the gain operator** (packet P5b) -/
theorem sa16sw_heat_weak {ν : ℝ} (hν : 0 < ν) (k : ℕ) {ψ : Euc d → ℝ}
    (hψ : IsCcInfty ψ) (hχ : IsCcInfty (sa16r_lap ψ)) {s : ℝ} (hs : 0 < s) (y : WmpSpace d k p) :
    sa16r_ell d (k + 1) p hψ (sa16r_GamT d k p ν s y) =
      sa16r_ell d k p hψ y +
        ∫ σ in (0 : ℝ)..s, ν * sa16r_ell d (k + 1) p hχ (sa16r_GamT d k p ν σ y) := by
  refine (sa16r_Jcc_dense d k p).induction_on y (isClosed_eq ?_ ?_) (fun φ => ?_)
  · exact (sa16r_ell d (k + 1) p hψ).continuous.comp (sa16r_GamT d k p ν s).continuous
  · exact ((sa16r_ell d k p hψ).continuous).add (sa16sw_int_cont hν hχ k hs)
  · rw [sa16r_Jcc_eq]
    exact sa16sw_weak_cc hν k φ.2 hψ hχ hs

/-- the predicate `SA16RHeatWeak` holds for `χ = Δψ` -/
theorem sa16sw_heatWeak {ν : ℝ} (hν : 0 < ν) (T : ℝ) (k : ℕ) {ψ : Euc d → ℝ} (hψ : IsCcInfty ψ) :
    SA16RHeatWeak d k p ν T hψ (sa16sw_cc_lap hψ) :=
  SA16RHeatWeak.of_first k hψ (sa16sw_cc_lap hψ)
    (fun y s hs => sa16sw_heat_weak hν k hψ (sa16sw_cc_lap hψ) hs.1 y)

end Hw4

end HRS.Whole.AppendixA.Phase2SA16R
