import HRS.MS.MovAdjNlAux3

/-!
# S6.7 nonlinear row, package A, packet N1 (part 4): the Volterra identity `s67a_volterra`

Namespace `HRS.MS.MovAdjNl`, helpers `s67a_`.  Infrastructure for the supplement row `S:W:lem:r2mov-global-adjoint`; not a manuscript row.

**`s67a_volterra`** (weak Volterra identity with source): for a classical adjoint solution `f` of the coefficient `coeff ρ^u` (terminal datum `φ`
at `t`), `0 ≤ r ≤ t`, and `v₀ ∈ L²_0` in the Schwartz core:
`∫ f_r √ρ₀ v₀ = ∫ φ √ρ₀ T(t-r) v₀ + ∫_0^{t-r} (∫ (R_{r+σ} f_{r+σ}) √ρ₀ T(σ) v₀) dσ`,  `R = s67aR` = (generator along `ρ^u`) - (stationary generator).
Proof: `g(σ) = ⟨f_{r+σ}√ρ₀, T(σ)v₀⟩` is continuous with right derivative `-k(σ)` (`s67a_gdv`), `k` bounded (`s67a_k_bound`), and
`measurable_derivWithin_Ici` gives measurability; `integral_eq_sub_of_hasDeriv_right_of_le`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MovAdjNl

open HRS HRS.Whole HRS.MH.DualityRd HRS.MS.MovLin HRS.MS.Mov63 HRS.MS.MovAdj

variable {d : ℕ} {s β q : ℝ} {ρ : Euc d → ℝ}

local notation "𝓢R" => SchwartzMap (Euc d) ℝ

set_option maxHeartbeats 3200000 in
theorem s67a_volterra (H : Mov2dTh d s β q ρ) (ψ0 : 𝓢R) (hψ0 : (⇑ψ0 : Euc d → ℝ) = fun x => Real.sqrt (ρ x))
    {ρt : ℝ → Euc d → ℝ} {t : ℝ} {φ : Euc d → ℝ} {f : ℝ → Euc d → ℝ}
    (hf : IsClassicalAdjointW ((quadraticGradientDyn d s q β).coeff ρt) t φ f)
    {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) t) {φ₀ : 𝓢R} {v₀ : MovL2Zero ρ}
    (hv : ∀ᵐ x ∂(volume : Measure (Euc d)), movFun v₀ x = φ₀ x) :
    ∫ x, f r x * (Real.sqrt (ρ x) * movFun v₀ x) =
      (∫ x, φ x * (Real.sqrt (ρ x) * movFun (mov2d_T H ψ0 hψ0 (t - r) v₀) x)) +
      ∫ σ in (0 : ℝ)..(t - r), ∫ x, s67aR d s q β ρ ρt (r + σ) (f (r + σ)) x *
        (Real.sqrt (ρ x) * movFun (mov2d_T H ψ0 hψ0 σ v₀) x) := by
  have ht : 0 ≤ t := hr.1.trans hr.2
  have hTs := mov2d_isSemigroup H ψ0 hψ0
  rcases eq_or_lt_of_le hr.2 with hrt | hrt
  · subst hrt
    simp only [sub_self, intervalIntegral.integral_same, add_zero]
    rw [mov2d_T_zero H ψ0 hψ0, hf.terminal]
    rfl
  have hgL : MemLp (fun x => Real.sqrt (ρ x)) 2 (volume : Measure (Euc d)) := by
    rw [← hψ0]; exact ψ0.memLp 2
  have hρ := mnb_rhoData H
  have hσ1 : (0 : ℝ) < t - r := sub_pos.2 hrt
  set g : ℝ → ℝ := fun τ => inner ℝ ((s67a_memLp hf ht r hgL τ).toLp (s67a f ρ r t τ))
      ((mov2d_T H ψ0 hψ0 τ v₀ : MovL2Zero ρ) : Lp ℝ 2 (volume : Measure (Euc d))) with hg
  have hAc := (s67a_cont hf ht r hgL hρ.smooth.continuous).mono (Set.subset_univ (Set.Icc 0 (t - r)))
  have hbc : ContinuousOn (fun τ => ((mov2d_T H ψ0 hψ0 τ v₀ : MovL2Zero ρ) : Lp ℝ 2 (volume : Measure (Euc d))))
      (Set.Icc 0 (t - r)) := by
    have h := (mov2d_T_cont H ψ0 hψ0 v₀).mono (fun τ (hτ : τ ∈ Set.Icc (0 : ℝ) (t - r)) => hτ.1)
    exact continuous_subtype_val.comp_continuousOn h
  have hgc : ContinuousOn g (Set.Icc 0 (t - r)) := hAc.inner hbc
  obtain ⟨w₀, hw₀⟩ := s67a_Tgen H ψ0 hψ0 hv
  obtain ⟨BU, hBU⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := t - r)).exists_bound_of_continuousOn hbc
  have hwc : ContinuousOn (fun τ => ((mov2d_T H ψ0 hψ0 τ w₀ : MovL2Zero ρ) : Lp ℝ 2 (volume : Measure (Euc d))))
      (Set.Icc 0 (t - r)) := by
    have h := (mov2d_T_cont H ψ0 hψ0 w₀).mono (fun τ (hτ : τ ∈ Set.Icc (0 : ℝ) (t - r)) => hτ.1)
    exact continuous_subtype_val.comp_continuousOn h
  obtain ⟨Bw, hBw⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := t - r)).exists_bound_of_continuousOn hwc
  obtain ⟨Bk, hBk⟩ := s67a_k_bound H ψ0 hψ0 hf ht hr hv hgL hw₀ hBU hBw
  set k : ℝ → ℝ := fun σ => ∫ x, s67aR d s q β ρ ρt (r + σ) (f (r + σ)) x *
        (Real.sqrt (ρ x) * movFun (mov2d_T H ψ0 hψ0 σ v₀) x) with hk
  have hderI : ∀ σ ∈ Set.Ioo (0 : ℝ) (t - r), HasDerivWithinAt g (-k σ) (Set.Ici σ) σ :=
    fun σ hσ => s67a_gdv H ψ0 hψ0 hf ht hr hv hgL hσ
  have hder : ∀ σ ∈ Set.Ioo (0 : ℝ) (t - r), HasDerivWithinAt g (-k σ) (Set.Ioi σ) σ :=
    fun σ hσ => (hderI σ hσ).mono Set.Ioi_subset_Ici_self
  have hmeas : Measurable (fun σ => derivWithin g (Set.Ici σ) σ) := measurable_derivWithin_Ici g
  have hdw : ∀ σ ∈ Set.Ioo (0 : ℝ) (t - r), derivWithin g (Set.Ici σ) σ = -k σ :=
    fun σ hσ => (hderI σ hσ).derivWithin (uniqueDiffWithinAt_Ici σ)
  have hm2 : AEStronglyMeasurable (fun σ => -k σ) (volume.restrict (Set.Ioo (0 : ℝ) (t - r))) := by
    refine (hmeas.aestronglyMeasurable (μ := volume.restrict (Set.Ioo (0 : ℝ) (t - r)))).congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with σ hσ
    exact hdw σ hσ
  have hint : IntervalIntegrable (fun σ => -k σ) volume 0 (t - r) := by
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hσ1.le]
    refine Integrable.of_bound (μ := volume.restrict (Set.Ioo (0 : ℝ) (t - r))) hm2 Bk ?_
    refine (ae_restrict_iff' measurableSet_Ioo).2 (Filter.Eventually.of_forall fun σ hσ => ?_)
    rw [norm_neg, Real.norm_eq_abs]
    exact hBk σ hσ
  have hftc := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hσ1.le hgc hder hint
  rw [intervalIntegral.integral_neg] at hftc
  have hg0 : g 0 = ∫ x, f r x * (Real.sqrt (ρ x) * movFun v₀ x) := by
    show inner ℝ ((s67a_memLp hf ht r hgL 0).toLp (s67a f ρ r t 0))
      ((mov2d_T H ψ0 hψ0 0 v₀ : MovL2Zero ρ) : Lp ℝ 2 (volume : Measure (Euc d))) = _
    rw [s67_inner_toLp_left]
    have hcl0 : s67clamp r t 0 = r := by
      rw [s67clamp_eq (by simpa using hr.1) (by simpa using hr.2)]; ring
    rw [mov2d_T_zero H ψ0 hψ0]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    unfold s67a
    rw [hcl0]
    show f r x * Real.sqrt (ρ x) * ((v₀ : MovL2Zero ρ) : Lp ℝ 2 (volume : Measure (Euc d))) x = _
    unfold movFun
    ring
  have hgt : g (t - r) = ∫ x, φ x * (Real.sqrt (ρ x) * movFun (mov2d_T H ψ0 hψ0 (t - r) v₀) x) := by
    show inner ℝ ((s67a_memLp hf ht r hgL (t - r)).toLp (s67a f ρ r t (t - r)))
      ((mov2d_T H ψ0 hψ0 (t - r) v₀ : MovL2Zero ρ) : Lp ℝ 2 (volume : Measure (Euc d))) = _
    rw [s67_inner_toLp_left]
    have hclt : s67clamp r t (t - r) = t := by
      rw [s67clamp_eq (by linarith) (by linarith)]; ring
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    unfold s67a
    rw [hclt, hf.terminal]
    unfold movFun
    ring
  have key : g 0 = g (t - r) + ∫ σ in (0 : ℝ)..(t - r), k σ := by linarith [hftc]
  calc ∫ x, f r x * (Real.sqrt (ρ x) * movFun v₀ x) = g 0 := hg0.symm
    _ = g (t - r) + ∫ σ in (0 : ℝ)..(t - r), k σ := key
    _ = _ := by rw [hgt] <;> rfl

end HRS.MS.MovAdjNl
