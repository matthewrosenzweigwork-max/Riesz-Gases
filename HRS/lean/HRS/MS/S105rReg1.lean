import HRS.MS.S104bNL7

/-!
# S10.5 (nonlinear), packet S105R-1: `S105nReg`, the mean-field regularity `IsRegularMFRd s 3 Λ T ρ` of the resulting solutions

For `2 ≤ d`, `0 ≤ s < d`, `a, β > 0` and every `ε_*, c₁, C₁`: every resulting solution `ρ` (`IsResultingSolution`) of a thermal
equilibrium `ρ_β` satisfies `IsRegularMFRd s 3 Λ T ρ` for every horizon `T`, with `Λ` independent of `T`.

Route: `ρ^t = ρ_β + √ρ_β v_t`, `v_t = (ρ^t - ρ_β)/√ρ_β ∈ Σ^{102d+1020} ∩ C^0` with `‖v_t‖_{Σ^m} ≤ C₁ε_*`.
`mn_force_bound` (Sobolev embedding) gives `v_t ∈ C^3` with `‖D^k v_t‖_∞ ≤ C‖v_t‖_{Σ^m}`; `ρ_β`, `√ρ_β` have Gaussian derivative bounds
(`mv0_hgauss_gapref`, `mv0_sqrt_gauss`); Leibniz gives Gaussian bounds `‖D^k ρ^t(x)‖ ≤ K e^{-c|x|²}` (`k ≤ 3`) uniformly in `t ≥ 0`, which
gives `MemCb 3`, the `⟨x⟩^{d+3}`-weighted bound and the `C_b^3` norm.  The singular force bound is read off the `velocity` clause and the
Euler equation of `ρ_β`: `∇g*ρ^t = u^t - β⁻¹∇log(ρ^t/ρ_β) + ∇g*ρ_β` with `‖u^t‖_∞, ‖∇log(ρ^t/ρ_β)‖_∞ ≤ C₁ε_*` and `∇g*ρ_β = -β⁻¹ B`
bounded (`GapRef`).  No linearity of the cancellation convolution is needed.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S105r

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MS.S104b

variable {d : ℕ}

/-- Gaussian weighted derivative bounds up to order `3` give `MemCb 3`, the weighted sup norm and the `C_b^3` norm. -/
theorem s105r_gauss_reg {c : ℝ} (hc : 0 < c) :
    ∃ P : ℝ, 0 ≤ P ∧ ∀ (f : Euc d → ℝ) (K : ℝ), 0 ≤ K → ContDiff ℝ ((3 : ℕ) : WithTop ℕ∞) f →
      (∀ k ≤ 3, ∀ x : Euc d, ‖iteratedFDeriv ℝ k f x‖ ≤ K * Real.exp (-c * ‖x‖ ^ 2)) →
      HRS.MemCb 3 f ∧ weightedSupE 3 ((d : ℝ) + 3) f ≤ ENNReal.ofReal (P * K) ∧ HRS.cbNorm 3 f ≤ 4 * K := by
  obtain ⟨P, hP0, hP⟩ := HRS.MS.Thm.rege_poly_gauss_bdd hc (d + 3)
  have hexp : ∀ x : Euc d, Real.exp (-c * ‖x‖ ^ 2) ≤ 1 := fun x => by
    rw [Real.exp_le_one_iff]; nlinarith [sq_nonneg ‖x‖]
  refine ⟨P, hP0.le, fun f K hK hf hb => ⟨⟨hf, fun j hj => ⟨K, ?_⟩⟩, ?_, ?_⟩⟩
  · rintro _ ⟨x, rfl⟩
    refine (hb j hj x).trans ?_
    have := hexp x
    nlinarith
  · unfold weightedSupE derivSupE
    refine iSup_le fun j => iSup_le fun I => iSup_le fun x => ENNReal.ofReal_le_ofReal ?_
    have hj : (j : ℕ) ≤ 3 := Nat.lt_succ_iff.mp j.2
    have h1 : jbracket x ^ ((d : ℝ) + 3) ≤ (1 + ‖x‖) ^ (d + 3) := by
      have : ((d : ℝ) + 3) = ((d + 3 : ℕ) : ℝ) := by push_cast; ring
      rw [this, Real.rpow_natCast]
      exact pow_le_pow_left₀ (u2_jb_pos x).le (u2_jb_le x) _
    have h2 : |partialDeriv I f x| ≤ K * Real.exp (-c * ‖x‖ ^ 2) :=
      (HRS.MS.Lc.lc4_partial_le (j : ℕ) I x).trans (hb j hj x)
    have h3 := hP ‖x‖ (norm_nonneg _)
    calc jbracket x ^ ((d : ℝ) + 3) * |partialDeriv I f x|
        ≤ (1 + ‖x‖) ^ (d + 3) * (K * Real.exp (-c * ‖x‖ ^ 2)) :=
          mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
      _ = K * ((1 + ‖x‖) ^ (d + 3) * Real.exp (-c * ‖x‖ ^ 2)) := by ring
      _ ≤ K * P := mul_le_mul_of_nonneg_left h3 hK
      _ = P * K := mul_comm _ _
  · unfold HRS.cbNorm
    calc ∑ j ∈ Finset.range (3 + 1), ⨆ z : Euc d, ‖iteratedFDeriv ℝ j f z‖
        ≤ ∑ _j ∈ Finset.range (3 + 1), K := by
          refine Finset.sum_le_sum fun j hj => ?_
          have hj3 : j ≤ 3 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
          refine ciSup_le fun z => (hb j hj3 z).trans ?_
          have := hexp z
          nlinarith
      _ = 4 * K := by simp

/-- `ofReal ‖v x‖ ≤ cbNormVecE K v` (the zeroth term). -/
theorem s105r_cbvec_zero (K : ℕ) (v : Euc d → Euc d) (x : Euc d) :
    ENNReal.ofReal ‖v x‖ ≤ cbNormVecE K v := by
  unfold cbNormVecE
  calc ENNReal.ofReal ‖v x‖ = ENNReal.ofReal ‖iteratedFDeriv ℝ 0 v x‖ := by rw [norm_iteratedFDeriv_zero]
    _ ≤ ⨆ y : Euc d, ENNReal.ofReal ‖iteratedFDeriv ℝ 0 v y‖ := le_iSup (fun y : Euc d => ENNReal.ofReal ‖iteratedFDeriv ℝ 0 v y‖) x
    _ ≤ _ := Finset.single_le_sum (f := fun j => ⨆ y : Euc d, ENNReal.ofReal ‖iteratedFDeriv ℝ j v y‖)
          (fun j _ => bot_le) (Finset.mem_range.2 (Nat.succ_pos K))

/-- `ρ^0` is a probability density, so `C₁ > 0` (from `C₁⁻¹ρ_β ≤ ρ^0 ≤ C₁ρ_β`). -/
theorem s105r_C1_pos {s a β : ℝ} {ρβ : Euc d → ℝ} (hρβ : IsThermalEquilibrium d s a β ρβ) {εstar ε c₁ C₁ : ℝ}
    {ψ : Euc d → ℝ} {ρ : ℝ → Euc d → ℝ} (hres : IsResultingSolution d s a β ρβ εstar ε ψ c₁ C₁ ρ) : 0 < C₁ := by
  by_contra hC
  push_neg at hC
  have hd0 := (hres.global 0).density 0 (Set.mem_Icc.2 ⟨le_rfl, le_rfl⟩)
  have hle : ∀ x, ρ 0 x ≤ 0 := fun x => by
    have h1 := (hres.ratio 0 le_rfl x).2
    have h2 : 0 < ρβ x := HRS.Whole.u4_thermal_pos hρβ x
    nlinarith
  have hz : ρ 0 = fun _ => 0 := funext fun x => le_antisymm (hle x) (hd0.nonneg x)
  have h1 := hd0.integral_one
  rw [hz] at h1
  simp at h1

end HRS.MS.S105r
