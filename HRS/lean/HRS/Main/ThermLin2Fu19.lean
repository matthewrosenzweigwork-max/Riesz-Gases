import HRS.Main.ThermLin2Fu18

/-!
# THERMLIN2 Fu19: the pairing bound `|⟨Zs^t - Zw^t, φ⟩| ≤ ...` for each fixed `t` and smooth `φ` (almost surely)

Uses `tl2_dyson_fubini_proof` (B4, Fu14) and, through `tl2fu_psi_shift`, the bound `tl2_Delta_bound` (B2) as an
explicit hypothesis `hB2`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.ThermLin.Plan2

open HRS HRS.Uniform HRS.GF HRS.AdjK HRS.T25P HRS.Uniform.Q54c

variable {d : ℕ}

theorem tl2fu_eval_sub {m : ℝ} (a b : NegSobolev d m) {φ : Torus d → ℝ} (hφ : MemSobolev m φ) :
    NegSobolev.eval (a - b) φ = NegSobolev.eval a φ - NegSobolev.eval b φ := by
  rw [eval_lpFun _ hφ, eval_lpFun _ hφ, eval_lpFun _ hφ, inner_sub_left]

theorem tl2fu_pairing_bound (S : HRS.Main.PreparedData d) {ρβ : Torus d → ℝ}
    (h : IsThermalDensity (periodicRiesz d S.s) S.V S.β ρβ) (m : ℝ) (hm : (d : ℝ) + 2 < m)
    {C κ : ℝ} (hC : 0 ≤ C)
    (hB2 : ∀ r : ℝ, 0 ≤ r → ∀ ψ : Torus d → ℝ, Torus.IsSmooth ψ →
      MemSobolev (m - PDE.MFAdjoint.aExp d S.s) (tl2Delta S ρβ r ψ) ∧
        sobolevNorm (m - PDE.MFAdjoint.aExp d S.s) (tl2Delta S ρβ r ψ) ≤
          C * Real.exp (-κ * r) * sobolevNorm m ψ)
    {T' : ℝ} (hT' : 0 < T') {K c : ℝ} (hK : 0 ≤ K) (hc : 0 < c)
    (Vev Wev : ℝ → ℝ → NegSobolev d m →L[ℝ] NegSobolev d m)
    (hVd : IsDualEvolution S.dyn S.ρ m Vev) (hVp : IsPlainEvolution Vev T')
    (hdec : ∀ u t : ℝ, 0 ≤ u → u ≤ t → t ≤ T' → ‖Vev t u‖ ≤ K * Real.exp (-c * (t - u)))
    (hWd : IsDualEvolution S.dyn (fun _ => ρβ) m Wev) (hWp : IsPlainEvolution Wev T')
    (hWb : ∀ r t : ℝ, 0 ≤ r → r ≤ t → t ≤ T' → ‖Wev t r‖ ≤ K)
    {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ}
    (G : ℝ → Ω → NegSobolev d m)
    (hG : IsHilbertMartingaleWithCovariation P ℱ T' G (fun r _ => covDensT m S.β⁻¹ T' S.ρ r))
    (hGc : ∀ ω, Continuous fun s => G s ω) (hGz : ∀ ω, G 0 ω = 0)
    (Zs Zw : ℝ → Ω → NegSobolev d m)
    (hZs : ∀ t ∈ Set.Icc (0 : ℝ) T', IsStochConv P Vev (ContinuousLinearMap.id ℝ (NegSobolev d m)) G 0 t (Zs t))
    (hZw : ∀ t ∈ Set.Icc (0 : ℝ) T', IsStochConv P Wev (ContinuousLinearMap.id ℝ (NegSobolev d m)) G 0 t (Zw t))
    (hZsm : ∀ t, Measurable (Zs t)) (hZwm : ∀ t, Measurable (Zw t))
    (hZwc : ∀ᵐ ω ∂P, ContinuousOn (fun t => Zw t ω) (Set.Icc 0 T'))
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T') {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ) :
    ∀ᵐ ω ∂P, ENNReal.ofReal |NegSobolev.eval (Zs t ω - Zw t ω) φ| ≤
      ENNReal.ofReal ‖lpFun m φ‖ * (ENNReal.ofReal (C * K) *
        ∫⁻ r in Set.Icc (0 : ℝ) t, ENNReal.ofReal (Real.exp (-c * (t - r)) * Real.exp (-κ * r)) *
          tl2NormShift m (PDE.MFAdjoint.aExp d S.s) (Zw r ω)) := by
  have hVb : ∀ r t : ℝ, 0 ≤ r → r ≤ t → t ≤ T' → ‖Vev t r‖ ≤ K := fun r t hr hrt htT =>
    (hdec r t hr hrt htT).trans (mul_le_of_le_one_right hK (Real.exp_le_one_iff.2
      (by nlinarith [hc, sub_nonneg.2 hrt])))
  have hφm : MemSobolev m φ := PDE.MFSemigroup.memSobolev_of_isSmooth hφ m
  filter_upwards [tl2_dyson_fubini_proof S h m hm hT' hK Vev Wev hVd hVp hVb hWd hWp hWb P G hG hGc hGz Zs Zw
    hZs hZw hZsm hZwm hZwc ht hφ] with ω hω
  rw [tl2fu_eval_sub _ _ hφm, hω]
  rcases ht.1.eq_or_lt with h0 | hpos
  · obtain rfl : t = 0 := h0.symm
    simp
  · set N : ℝ → ℝ≥0∞ := fun r => tl2NormShift m (PDE.MFAdjoint.aExp d S.s) (Zw r ω) with hN
    have hpt : ∀ r ∈ Set.Icc (0 : ℝ) t,
        ‖NegSobolev.eval (Zw r ω) (tl2Delta S ρβ r (propagator S.dyn S.ρ r t φ))‖ₑ ≤
          ENNReal.ofReal ‖lpFun m φ‖ * (ENNReal.ofReal (C * K) *
            (ENNReal.ofReal (Real.exp (-c * (t - r)) * Real.exp (-κ * r)) * N r)) := by
      intro r hr
      obtain ⟨hmem, hnorm⟩ := tl2fu_psi_shift S h m Vev hVd hK hdec hC hφ hpos ht.2 hr (hB2 r hr.1)
      rw [Real.enorm_eq_ofReal_abs]
      refine (tl2fu_eval_le_shift _ _ hmem).trans ?_
      have h1 : N r * ENNReal.ofReal (sobolevNorm (m - PDE.MFAdjoint.aExp d S.s)
          (tl2Delta S ρβ r (propagator S.dyn S.ρ r t φ))) ≤
          N r * ENNReal.ofReal (C * Real.exp (-κ * r) * (K * Real.exp (-c * (t - r)) * ‖lpFun m φ‖)) :=
        by gcongr
      refine h1.trans (le_of_eq ?_)
      have e : C * Real.exp (-κ * r) * (K * Real.exp (-c * (t - r)) * ‖lpFun m φ‖) =
          ‖lpFun m φ‖ * ((C * K) * (Real.exp (-c * (t - r)) * Real.exp (-κ * r))) := by ring
      have hexp : 0 ≤ Real.exp (-c * (t - r)) * Real.exp (-κ * r) := by positivity
      rw [e, ENNReal.ofReal_mul (norm_nonneg _), ENNReal.ofReal_mul (mul_nonneg hC hK)]
      ring
    calc ENNReal.ofReal |∫ r in (0 : ℝ)..t, NegSobolev.eval (Zw r ω)
            (tl2Delta S ρβ r (propagator S.dyn S.ρ r t φ))|
        = ‖∫ r in Set.Ioc (0 : ℝ) t, NegSobolev.eval (Zw r ω)
            (tl2Delta S ρβ r (propagator S.dyn S.ρ r t φ))‖ₑ := by
          rw [intervalIntegral.integral_of_le ht.1, Real.enorm_eq_ofReal_abs]
      _ ≤ ∫⁻ r in Set.Ioc (0 : ℝ) t, ‖NegSobolev.eval (Zw r ω)
            (tl2Delta S ρβ r (propagator S.dyn S.ρ r t φ))‖ₑ := enorm_integral_le_lintegral_enorm _
      _ ≤ ∫⁻ r in Set.Icc (0 : ℝ) t, ‖NegSobolev.eval (Zw r ω)
            (tl2Delta S ρβ r (propagator S.dyn S.ρ r t φ))‖ₑ :=
          lintegral_mono_set Set.Ioc_subset_Icc_self
      _ ≤ ∫⁻ r in Set.Icc (0 : ℝ) t, ENNReal.ofReal ‖lpFun m φ‖ * (ENNReal.ofReal (C * K) *
            (ENNReal.ofReal (Real.exp (-c * (t - r)) * Real.exp (-κ * r)) * N r)) :=
          setLIntegral_mono' measurableSet_Icc hpt
      _ = _ := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

end HRS.ThermLin.Plan2
