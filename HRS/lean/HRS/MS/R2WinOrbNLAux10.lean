import HRS.MS.R2WinOrbNLAux9

/-!
# S10.3 (nonlinear branch), part 10: the weighted `Σ^N` norm of `√ρ_β Πg` from the bounded jets of `g`

Prefix `s103n_`, namespace `HRS.MS.R2WinOrbNL`.  `s103n_psi_of_jets`: for `g ∈ Bd N A` (jets up to order `N` bounded by `A`) the function
`s67psi ρ_β g = √ρ_β (g - ∫ g ρ_β)` lies in `Σ^N` with norm `≤ C A`, `C = C(N,d,s,a,β)`.  This is the finite-smoothness replacement of the
multiplier theorem `mo_mult_cb` (which needs `C^∞`): `√ρ_β` has Gaussian-bounded derivatives, Leibniz gives Gaussian-bounded jets of the product,
and `s67bd_gaussian_osc` (S6.7nl.05) converts these into the oscillator norm.
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace

namespace HRS.MS.R2WinOrbNL

open HRS HRS.Whole HRS.MS.BreakdownS67 HRS.MS.MovLin HRS.MS.MovAdj HRS.MS.MovOsc

variable {d : ℕ}

theorem s103n_const_sub_jets {g : Euc d → ℝ} {N : ℕ} (hg : ContDiff ℝ (N : WithTop ℕ∞) g) (c0 : ℝ)
    (k : ℕ) (hk : k ≤ N) (x : Euc d) :
    ‖iteratedFDeriv ℝ k (fun y => g y - c0) x‖ ≤ ‖iteratedFDeriv ℝ k g x‖ + |c0| := by
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · rw [norm_iteratedFDeriv_zero, norm_iteratedFDeriv_zero]
    calc ‖g x - c0‖ ≤ ‖g x‖ + ‖c0‖ := norm_sub_le _ _
      _ = ‖g x‖ + |c0| := by rw [Real.norm_eq_abs c0]
  · have hcd : ContDiffAt ℝ (k : ℕ) g x := (hg.of_le (by exact_mod_cast hk)).contDiffAt
    have hcc : ContDiffAt ℝ (k : ℕ) (fun _ : Euc d => c0) x := contDiffAt_const
    have hsub : (fun y => g y - c0) = g - fun _ : Euc d => c0 := rfl
    rw [hsub, iteratedFDeriv_sub_apply hcd hcc, iteratedFDeriv_const_of_ne (by omega), Pi.zero_apply,
      sub_zero]
    exact le_add_of_nonneg_right (abs_nonneg _)

theorem s103n_psi_of_jets {s q β : ℝ} {ρβ : Euc d → ℝ} (H : Mov2dTh d s β q ρβ) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (A : ℝ) (g : Euc d → ℝ), Bd N A g →
      MemOsc (N : ℝ) (s67psi ρβ g) ∧ oscNorm (N : ℝ) (s67psi ρβ g) ≤ C * A := by
  obtain ⟨hws, -, c, hc, hk⟩ := HRS.MS.Mov0.mv0_sqrt_gauss_thermal H.hd H.hs0 H.hsd H.hq H.hβ H.hρ
  obtain ⟨Bq, -, hR, -⟩ := HRS.MS.Mov0.mv0_gapref H.hd H.hs0 H.hsd H.hq H.hβ H.hρ
  choose Cw hCw using hk
  set Cs : ℝ := ∑ k ∈ Finset.range (N + 1), |Cw k| with hCs
  have hCs0 : 0 ≤ Cs := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hwb : ∀ k ≤ N, ∀ x, ‖iteratedFDeriv ℝ k (fun y => Real.sqrt (ρβ y)) x‖ ≤
      Cs * Real.exp (-c * ‖x‖ ^ 2) := by
    intro k hk x
    have hle : |Cw k| ≤ Cs :=
      Finset.single_le_sum (f := fun k => |Cw k|) (fun _ _ => abs_nonneg _)
        (Finset.mem_range.2 (by omega))
    exact (hCw k x).trans (mul_le_mul_of_nonneg_right ((le_abs_self _).trans hle) (Real.exp_pos _).le)
  obtain ⟨C, hC0, hC⟩ := s67bd_gaussian_osc d N c hc
  refine ⟨C * (2 ^ N * Cs * 2), by positivity, fun A g hg => ?_⟩
  have hA := hg.nonneg
  set c0 : ℝ := ∫ y, g y * ρβ y with hc0
  have hc0b : |c0| ≤ A := by
    rw [hc0, ← Real.norm_eq_abs]
    have hint : Integrable (fun y => A * ρβ y) := hR.integrable.const_mul A
    calc ‖∫ y, g y * ρβ y‖ ≤ ∫ y, A * ρβ y := by
          refine norm_integral_le_of_norm_le hint (Eventually.of_forall fun y => ?_)
          rw [norm_mul, Real.norm_eq_abs, Real.norm_of_nonneg (hR.pos y).le]
          refine mul_le_mul_of_nonneg_right ?_ (hR.pos y).le
          have := hg.2 0 (Nat.zero_le _) y
          rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
      _ = A := by rw [integral_const_mul, hR.integral_one, mul_one]
  have hθ : ContDiff ℝ (N : WithTop ℕ∞) (fun y => g y - c0) := hg.1.sub contDiff_const
  have hθb : ∀ k ≤ N, ∀ x, ‖iteratedFDeriv ℝ k (fun y => g y - c0) x‖ ≤ 2 * A := fun k hk x =>
    (s103n_const_sub_jets hg.1 c0 k hk x).trans (by linarith [hg.2 k hk x])
  have hw : ContDiff ℝ (N : WithTop ℕ∞) (fun y => Real.sqrt (ρβ y)) := hws.of_le (by exact_mod_cast le_top)
  have hpsi : s67psi ρβ g = fun y => Real.sqrt (ρβ y) * (g y - c0) := rfl
  have hjet : ∀ k ≤ N, ∀ x, ‖iteratedFDeriv ℝ k (fun y => Real.sqrt (ρβ y) * (g y - c0)) x‖ ≤
      (2 ^ N * Cs * (2 * A)) * Real.exp (-c * ‖x‖ ^ 2) := by
    intro k hk x
    refine (norm_iteratedFDeriv_mul_le (𝕜 := ℝ) hw hθ x (n := k) (by exact_mod_cast hk)).trans ?_
    have hE := (Real.exp_pos (-c * ‖x‖ ^ 2)).le
    have hterm : ∀ l ∈ Finset.range (k + 1),
        (k.choose l : ℝ) * ‖iteratedFDeriv ℝ l (fun y => Real.sqrt (ρβ y)) x‖ *
          ‖iteratedFDeriv ℝ (k - l) (fun y => g y - c0) x‖ ≤
          (k.choose l : ℝ) * (Cs * Real.exp (-c * ‖x‖ ^ 2) * (2 * A)) := by
      intro l hl
      have hl' : l ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hl)
      rw [mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      exact mul_le_mul (hwb l (by omega) x) (hθb (k - l) (by omega) x) (norm_nonneg _)
        (mul_nonneg hCs0 hE)
    calc _ ≤ ∑ l ∈ Finset.range (k + 1), (k.choose l : ℝ) * (Cs * Real.exp (-c * ‖x‖ ^ 2) * (2 * A)) :=
          Finset.sum_le_sum hterm
      _ = (2 : ℝ) ^ k * (Cs * Real.exp (-c * ‖x‖ ^ 2) * (2 * A)) := by
          rw [← Finset.sum_mul]
          congr 1
          exact_mod_cast Nat.sum_range_choose k
      _ ≤ (2 : ℝ) ^ N * (Cs * Real.exp (-c * ‖x‖ ^ 2) * (2 * A)) :=
          mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hk) (by positivity)
      _ = _ := by ring
  rw [hpsi]
  obtain ⟨h1, h2⟩ := hC (2 ^ N * Cs * (2 * A)) (by positivity) _ (hw.mul hθ) hjet
  exact ⟨h1, h2.trans (le_of_eq (by ring))⟩

end HRS.MS.R2WinOrbNL

end
