import HRS.MS.S67NlBDTie
import HRS.MS.R2WinOrbAux15

/-!
# S10.3 (nonlinear branch), part 1: the class constants, `R2ClassExists`, and the bridge `IsResultingSolution -> MovInSmallClass`

Prefix `s103n_`, namespace `HRS.MS.R2WinOrbNL`.

* `s103n_small_class`: a solution `ρ` of `IsResultingSolution` (constants `ε_*, c₁, C₁`) with `C₁ ε_* ≤ r` is in the S6.3 uniqueness class
  `MovInSmallClass` (index `m = 102d+1020`, radius `r`, rate `c₁`, `f⁰ = εψ`).
* `s103n_resulting_of_conclusion`: from `MovNonlinearConclusion` (indices `100d+1000`, `102d+1020`) every admissible perturbation
  with smallness `ε_* ≤ ε_*'` has a resulting solution (`R2ClassExists` at the thermal equilibrium).
* `s103n_setup`: the constants of the nonlinear branch, chosen from the uniform gradient estimate of S6.7 (`s67bd_uniform_gradient`)
  and the shrinking theorem (`s67bd_shrink_nonlinear`), and the gradient estimate for every trajectory of the class.
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R2WinOrbNL

open HRS HRS.Whole HRS.MS.BreakdownS67 HRS.MS.Mov63 HRS.MS.MovLin HRS.MS.MovAdj

variable {d : ℕ}

theorem s103n_cast_m : (((102 * d + 1020 : ℕ)) : ℝ) = 102 * (d : ℝ) + 1020 := by
  push_cast; ring

theorem s103n_small_class {s a β : ℝ} {ρβ : Euc d → ℝ} {εstar ε : ℝ} {ψ : Euc d → ℝ} {c₁ C₁ : ℝ}
    {ρ : ℝ → Euc d → ℝ} (h : IsResultingSolution d s a β ρβ εstar ε ψ c₁ C₁ ρ) {r : ℝ}
    (hr : C₁ * εstar ≤ r) :
    MovInSmallClass d s a β ρβ (102 * d + 1020) r c₁ (fun x => ε * ψ x) ρ := by
  refine ⟨h.global, fun x => ?_, fun t ht => ?_, ?_, h.regular⟩
  · have := congrFun h.init x
    simp only [perturbedDensity] at this
    rw [this]; ring
  · rw [s103n_cast_m]
    obtain ⟨h1, h2⟩ := h.weighted t ht
    refine ⟨h1, h2.trans ?_⟩
    exact mul_le_mul_of_nonneg_right hr (Real.exp_pos _).le
  · rw [s103n_cast_m]
    exact h.cont

theorem s103n_initial_class {s a β : ℝ} {ρβ : Euc d → ℝ} (H : Mov2dTh d s β a ρβ) {εstar εs' ε : ℝ}
    {ψ : Euc d → ℝ} (hε : εstar ≤ εs') (hψ : IsAdmissiblePerturbation ρβ εstar ε ψ) :
    MovInitialClass ρβ (100 * d + 1000) (102 * d + 1020) εs' (fun x => ε * ψ x) := by
  refine ⟨?_, mnh_osc_smul H hψ.smooth hψ.compactSupport ε, ?_, ?_⟩
  · exact mnh_cb_smul hψ.smooth hψ.compactSupport (100 * d + 1000 + 1) ε
  · have e : (fun x => ε * ψ x * ρβ x) = fun x => ε * (ψ x * ρβ x) := by funext x; ring
    rw [e, integral_const_mul, hψ.meanZero, mul_zero]
  · have hs := hψ.small
    have e1 : (fun x => ε * Real.sqrt (ρβ x) * ψ x) = fun x => Real.sqrt (ρβ x) * (ε * ψ x) := by
      funext x; ring
    rw [e1, show (102 * (d : ℝ) + 1020) = (((102 * d + 1020 : ℕ)) : ℝ) from s103n_cast_m.symm] at hs
    have e2 : (100 * d + 1001 : ℕ) = 100 * d + 1000 + 1 := rfl
    rw [e2] at hs
    exact hs.trans hε

theorem s103n_resulting_of_conclusion {s a β : ℝ} {ρβ : Euc d → ℝ} (H : Mov2dTh d s β a ρβ)
    {εs' r c C' εstar : ℝ} (hc : 0 < c) (hC : 0 < C')
    (hconc : MovNonlinearConclusion d s a β ρβ (100 * d + 1000) (102 * d + 1020) εs' r c c C')
    (hε : εstar ≤ εs') {ε : ℝ} {ψ : Euc d → ℝ} (hψ : IsAdmissiblePerturbation ρβ εstar ε ψ) :
    ∃ ρ : ℝ → Euc d → ℝ, IsResultingSolution d s a β ρβ εstar ε ψ c C' ρ := by
  have hI := s103n_initial_class H hε hψ
  obtain ⟨ρ, hcls, -, hrat, -, hdec, -, -⟩ := hconc _ hI
  have hK : movInitialNorm ρβ (100 * d + 1000) (102 * d + 1020) (fun x => ε * ψ x) ≤ εstar := by
    have hs := hψ.small
    have e1 : (fun x => ε * Real.sqrt (ρβ x) * ψ x) = fun x => Real.sqrt (ρβ x) * (ε * ψ x) := by
      funext x; ring
    rw [e1, show (102 * (d : ℝ) + 1020) = (((102 * d + 1020 : ℕ)) : ℝ) from s103n_cast_m.symm] at hs
    exact hs
  have hC' : ∀ t : ℝ, 0 ≤ t → C' * movInitialNorm ρβ (100 * d + 1000) (102 * d + 1020) (fun x => ε * ψ x) *
      Real.exp (-c * t) ≤ C' * εstar * Real.exp (-c * t) := by
    intro t ht
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hK hC.le) (Real.exp_pos _).le
  refine ⟨ρ, ⟨hc, hcls.solution, ?_, hrat, ?_, ?_, ?_, hcls.regular⟩⟩
  · funext x
    have := hcls.init x
    simp only [perturbedDensity]
    rw [this]; ring
  · intro t ht
    obtain ⟨⟨h1, h2⟩, -⟩ := hdec t ht
    rw [s103n_cast_m] at h1 h2
    exact ⟨h1, h2.trans (hC' t ht)⟩
  · intro t ht
    obtain ⟨-, -, -, h5⟩ := hdec t ht
    exact h5.trans (ENNReal.ofReal_le_ofReal (hC' t ht))
  · have := hcls.cont
    rwa [s103n_cast_m] at this

/-- The constants of the nonlinear branch.  `ε_*, c₁, C₁` (with the S6.3 radius `r ≤ 1`, `C₁ε_* ≤ r`) are fixed first; every admissible
perturbation has a resulting solution; and for every `ρ` in the small class `MovInSmallClass` (index `102d+1020`, radius `r`, rate `c₁`)
the gradient estimate of S6.7 with the orders `k = 4d+42`, `M = 8d+80` holds with constants `Cg, cg` independent of everything else. -/
theorem s103n_setup {s a β : ℝ} {ρβ : Euc d → ℝ} (H : Mov2dTh d s β a ρβ) (Rs : ℝ) (hRs : 0 < Rs) :
    ∃ εstar c₁ C₁ r : ℝ, 0 < εstar ∧ 0 < c₁ ∧ 0 < C₁ ∧ 0 < r ∧ r ≤ 1 ∧ r ≤ Rs ∧ C₁ * εstar ≤ r ∧
      (∀ (ε : ℝ) (ψ : Euc d → ℝ), IsAdmissiblePerturbation ρβ εstar ε ψ →
        ∃ ρ : ℝ → Euc d → ℝ, IsResultingSolution d s a β ρβ εstar ε ψ c₁ C₁ ρ) ∧
      ∃ Cg cg : ℝ, 1 ≤ Cg ∧ 0 < cg ∧ ∀ (f0 : Euc d → ℝ) (ρ : ℝ → Euc d → ℝ),
        MovInSmallClass d s a β ρβ (102 * d + 1020) r c₁ f0 ρ →
        ∀ (T : ℝ) (φ : Euc d → ℝ) (f : ℝ → Euc d → ℝ), 0 ≤ T →
          IsClassicalAdjointW ((quadraticGradientDyn d s a β).coeff ρ) T φ f →
          ContDiff ℝ ((4 * d + 42 : ℕ) + 1) φ → MemOsc ((8 * d + 80 : ℕ) : ℝ) (s67psi ρβ φ) →
          ∀ r' ∈ Icc (0 : ℝ) T,
            ContDiff ℝ (4 * d + 42 : ℕ) (fun x => gradient (f r') x) ∧
            cbNormVecE (4 * d + 42) (fun x => gradient (f r') x) ≤
              ENNReal.ofReal (Cg * Real.exp (-cg * (T - r'))) *
                (cbNormVecE (4 * d + 42) (fun x => gradient φ x) +
                  ENNReal.ofReal (oscNorm ((8 * d + 80 : ℕ) : ℝ) (s67psi ρβ φ))) := by
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hM : (d : ℝ) / 2 + ((4 * d + 42 : ℕ) : ℝ) + 5 < ((8 * d + 80 : ℕ) : ℝ) := by
    push_cast; linarith
  have hj' : 1 ≤ 100 * d + 1000 := by omega
  have hm : (d : ℝ) / 2 + ((100 * d + 1000 : ℕ) : ℝ) + 6 < ((102 * d + 1020 : ℕ) : ℝ) := by
    push_cast; linarith
  have hmM : ((8 * d + 80 : ℕ) : ℝ) + 4 < ((102 * d + 1020 : ℕ) : ℝ) := by
    push_cast; linarith
  obtain ⟨Rstar, Cg, cg, hRstar, hCg, hcg, hbound⟩ :=
    s67bd_uniform_gradient H (4 * d + 42) (8 * d + 80) hM (100 * d + 1000) (102 * d + 1020) hj' hm hmM
  obtain ⟨εs', r, c', C', hε', hr, hc', hC', hrR, hconc⟩ :=
    s67bd_shrink_nonlinear H (100 * d + 1000) (102 * d + 1020) hj' hm (min (min Rstar 1) Rs) (lt_min (lt_min hRstar one_pos) hRs)
  have hεpos : 0 < min εs' (r / C') := lt_min hε' (div_pos hr hC')
  have hCε : C' * min εs' (r / C') ≤ r := by
    calc C' * min εs' (r / C') ≤ C' * (r / C') := mul_le_mul_of_nonneg_left (min_le_right _ _) hC'.le
      _ = r := by field_simp
  refine ⟨min εs' (r / C'), c', C', r, hεpos, hc', hC', hr, (hrR.trans (min_le_left _ _)).trans (min_le_right _ _), hrR.trans (min_le_right _ _), hCε, ?_,
    Cg, cg, hCg, hcg, ?_⟩
  · intro ε ψ hψ
    exact s103n_resulting_of_conclusion H hc' hC' hconc (min_le_left _ _) hψ
  · intro f0 ρ hρ T φ f hT hf hφ hosc r' hr'
    exact hbound r c' hr.le ((hrR.trans (min_le_left _ _)).trans (min_le_left _ _)) hc'.le f0 ρ hρ T φ f hT hf hφ hosc r' hr'

end HRS.MS.R2WinOrbNL

end
