import HRS.MS.S104eReg1

/-!
# S10.4 (nonlinear), packet S104E-2: `s104e_regMF`, `IsRegularMFRd s n Λ T0 ρ` of the resulting solutions at order `n ≤ 100d + 1000`

`s104e_reg_first`: the density clause (`MemCb n`, weighted `⟨x⟩^{d+3}` bound, `C_b^n` norm) with `Λ` independent of `t`.
`s104e_regMF`: `IsRegularMFRd s n Λ T0 ρ` for every horizon (the singular force clause is read from `s105r_reg`, order 3).
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S104e

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MS.S104b HRS.MS.Mov63 HRS.MS.S105r

variable {d : ℕ}

theorem s104e_reg_first (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {a β : ℝ} (ha : 0 < a) (hβ : 0 < β)
    (εstar c₁ C₁ : ℝ) (n : ℕ) (hn : n ≤ 100 * d + 1000) {ρβ : Euc d → ℝ} (hρβ : IsThermalEquilibrium d s a β ρβ)
    {ε : ℝ} {ψ : Euc d → ℝ} {ρ : ℝ → Euc d → ℝ}
    (hres : IsResultingSolution d s a β ρβ εstar ε ψ c₁ C₁ ρ) :
    ∃ Λ : ℝ, ∀ t : ℝ, 0 ≤ t → ContDiff ℝ (n : WithTop ℕ∞) (ρ t) ∧ HRS.MemCb n (ρ t) ∧
      weightedSupE n ((d : ℝ) + 3) (ρ t) < ⊤ ∧
      HRS.cbNorm n (ρ t) + (weightedSupE n ((d : ℝ) + 3) (ρ t)).toReal ≤ Λ := by
  obtain ⟨B, hBdef, hR, -⟩ := HRS.MS.Mov0.mv0_gapref hd hs0 hsd ha hβ hρβ
  have hq : 0 < β * a := mul_pos hβ ha
  have hpos : ∀ x, 0 < ρβ x := hR.pos
  have hρβc : Continuous ρβ := hR.smooth.continuous
  obtain ⟨m, hm⟩ : ∃ m : ℕ, m = 102 * d + 1020 := ⟨_, rfl⟩
  have hmR : (m : ℝ) = 102 * (d : ℝ) + 1020 := by rw [hm]; push_cast; ring
  have hm1 : (d : ℝ) / 2 + (n : ℝ) + 2 < m := by
    rw [hmR]
    have h1 : (n : ℝ) ≤ 100 * (d : ℝ) + 1000 := by exact_mod_cast hn
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  obtain ⟨Cv, hCv0, hCv⟩ := mn_force_bound hd hs0 hsd β a hβ ha ρβ hρβ n m hm1
  set E : ℝ := |C₁| * |εstar| with hEdef
  have hE0 : 0 ≤ E := by positivity
  obtain ⟨c, K, hc, hK0, hKb⟩ := s104e_leibniz hq hR n Cv E hCv0 hE0
  obtain ⟨P, hP0, hP⟩ := s104e_gauss_reg (d := d) hc n
  refine ⟨((n : ℝ) + 1) * K + P * K, fun t ht => ?_⟩
  have hdec : ρ t = fun x => ρβ x + Real.sqrt (ρβ x) * ((ρ t x - ρβ x) / Real.sqrt (ρβ x)) := by
    funext x
    have hsq : 0 < Real.sqrt (ρβ x) := Real.sqrt_pos.2 (hpos x)
    field_simp
    ring
  have hvc : Continuous (fun x => (ρ t x - ρβ x) / Real.sqrt (ρβ x)) :=
    ((hres.regular t ht).sub hρβc).div hρβc.sqrt (fun x => (Real.sqrt_pos.2 (hpos x)).ne')
  have hvm : MemOsc (m : ℝ) (fun x => (ρ t x - ρβ x) / Real.sqrt (ρβ x)) := by
    rw [hmR]; exact (hres.weighted t ht).1
  have hvn : oscNorm (m : ℝ) (fun x => (ρ t x - ρβ x) / Real.sqrt (ρβ x)) ≤ E := by
    rw [hmR]
    refine ((hres.weighted t ht).2).trans ?_
    have h1 : Real.exp (-c₁ * t) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have := hres.cpos
      nlinarith
    have h2 : 0 ≤ Real.exp (-c₁ * t) := (Real.exp_pos _).le
    calc C₁ * εstar * Real.exp (-c₁ * t) ≤ |C₁ * εstar| * Real.exp (-c₁ * t) :=
          mul_le_mul_of_nonneg_right (le_abs_self _) h2
      _ ≤ |C₁ * εstar| * 1 := mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
      _ = E := by rw [mul_one, abs_mul]
  obtain ⟨hvn2, hvb, -⟩ := hCv _ hvc hvm
  have hv' : ContDiff ℝ (n : WithTop ℕ∞) (fun x => (ρ t x - ρβ x) / Real.sqrt (ρβ x)) :=
    hvn2.of_le (by exact_mod_cast (by omega : n ≤ n + 2))
  have hvb' : ∀ k ≤ n, ∀ x : Euc d, ‖iteratedFDeriv ℝ k (fun x => (ρ t x - ρβ x) / Real.sqrt (ρβ x)) x‖ ≤
      Cv * E := fun k hk x => (hvb k (by omega) x).trans (mul_le_mul_of_nonneg_left hvn hCv0)
  obtain ⟨hcd, hKb'⟩ := hKb _ hv' hvb'
  rw [← hdec] at hcd hKb'
  obtain ⟨hmc, hws, hcb⟩ := hP (ρ t) K hK0 hcd hKb'
  refine ⟨hcd, hmc, lt_of_le_of_lt hws ENNReal.ofReal_lt_top, ?_⟩
  have h1 : (weightedSupE n ((d : ℝ) + 3) (ρ t)).toReal ≤ P * K := by
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hws
    rwa [ENNReal.toReal_ofReal (by positivity)] at this
  exact add_le_add hcb h1

/-- `IsRegularMFRd s n Λ T0 ρ` for every resulting solution, every `n ≤ 100d + 1000`, every horizon. -/
theorem s104e_regMF (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {a β : ℝ} (ha : 0 < a) (hβ : 0 < β)
    (εstar c₁ C₁ : ℝ) (n : ℕ) (hn : n ≤ 100 * d + 1000) {ρβ : Euc d → ℝ} (hρβ : IsThermalEquilibrium d s a β ρβ)
    {ε : ℝ} {ψ : Euc d → ℝ} {ρ : ℝ → Euc d → ℝ} (hadm : IsAdmissiblePerturbation ρβ εstar ε ψ)
    (hres : IsResultingSolution d s a β ρβ εstar ε ψ c₁ C₁ ρ) (T0 : ℝ) (hT0 : 0 ≤ T0) :
    ∃ Λ : ℝ, IsRegularMFRd s n Λ T0 ρ := by
  obtain ⟨Λn, hΛn⟩ := s104e_reg_first hd hs0 hsd ha hβ εstar c₁ C₁ n hn hρβ hres
  obtain ⟨Λ3, hΛ3⟩ := s105r_reg hd hs0 hsd ha hβ εstar c₁ C₁ ρβ hρβ ε ψ ρ hadm hres T0 hT0
  refine ⟨max Λn Λ3, fun t ht => ?_, fun hs t ht x => ?_⟩
  · obtain ⟨-, hmc, hfin, hle⟩ := hΛn t ht.1
    exact ⟨hmc, hfin, hle.trans (le_max_left _ _)⟩
  · exact (hΛ3.2 hs t ht x).trans (le_max_right _ _)

end HRS.MS.S104e
