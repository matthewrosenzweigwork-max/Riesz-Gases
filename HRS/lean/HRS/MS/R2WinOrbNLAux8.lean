import HRS.MS.R2WinOrbNLAux7
import HRS.MS.MovSchTie

/-!
# S10.3 (nonlinear branch), part 8: the constants of the nonlinear branch with the Schwartz-time bounds of S6.4

Prefix `s103n_`, namespace `HRS.MS.R2WinOrbNL`.  `s103n_setup2`: as `s103n_setup`, but with the class constants `(c₁, C₁)` GIVEN (repair D2/ED14: universally quantified before `εstar`) and only `εstar` chosen, with the other constants chosen from `mov_schwartz` (Corollary S6.4,
index `K`) and, for every `L`, a constant `CKL` such that for every resulting solution `ρ` of an admissible perturbation there is the right
time derivative `ρ'` and `ρ_t`, `ρ'_t` are `C^K` with `⟨x⟩^L (‖D^k(ρ_t - ρ_β)(x)‖ + ‖D^kρ'_t(x)‖) ≤ CKL` (`k ≤ K`, `t ≥ 0`).  The transfer from
the constructed solution of S6.3 to `ρ` is the uniqueness clause of `MovNonlinearConclusion` (`MovNonlinearConclusion.exists_unique`).
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace

namespace HRS.MS.R2WinOrbNL

open HRS HRS.Whole HRS.MS.BreakdownS67 HRS.MS.Mov63 HRS.MS.MovLin HRS.MS.MovAdj HRS.MS.MovOsc

variable {d : ℕ}

set_option maxHeartbeats 1600000 in
theorem s103n_setup2 {s a β : ℝ} {ρβ : Euc d → ℝ} (H : Mov2dTh d s β a ρβ) (Rs : ℝ) (hRs : 0 < Rs)
    (K : ℕ) (hK : (K : ℝ) + d / 2 + 4 < ((102 * d + 1020 : ℕ) : ℝ)) (c₁ C₁ : ℝ) (hc₁ : 0 < c₁) :
    ∃ εstar r : ℝ, 0 < εstar ∧ 0 < r ∧ r ≤ 1 ∧ r ≤ Rs ∧ C₁ * εstar ≤ r ∧
      (∃ Cg cg : ℝ, 1 ≤ Cg ∧ 0 < cg ∧ ∀ (f0 : Euc d → ℝ) (ρ : ℝ → Euc d → ℝ),
        MovInSmallClass d s a β ρβ (102 * d + 1020) r c₁ f0 ρ → S103nGrad d s a β ρβ ρ Cg cg) ∧
      ∀ L : ℕ, ∃ CKL : ℝ, ∀ (ε : ℝ) (ψ : Euc d → ℝ) (ρ : ℝ → Euc d → ℝ),
        IsAdmissiblePerturbation ρβ εstar ε ψ → IsResultingSolution d s a β ρβ εstar ε ψ c₁ C₁ ρ →
        ∃ ρ' : ℝ → Euc d → ℝ,
          (∀ t : ℝ, 0 ≤ t → ∀ x, HasDerivWithinAt (fun τ => ρ τ x) (ρ' t x) (Set.Ici t) t) ∧
          ∀ t : ℝ, 0 ≤ t → ContDiff ℝ K (ρ t) ∧ ContDiff ℝ K (ρ' t) ∧
            ∀ k : ℕ, k ≤ K → ∀ x : Euc d,
              movBracket x ^ L * (‖iteratedFDeriv ℝ k (fun y => ρ t y - ρβ y) x‖ +
                ‖iteratedFDeriv ℝ k (ρ' t) x‖) ≤ CKL := by
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hM : (d : ℝ) / 2 + ((4 * d + 42 : ℕ) : ℝ) + 5 < ((8 * d + 80 : ℕ) : ℝ) := by
    push_cast; linarith
  have hj' : 1 ≤ 100 * d + 1000 := by omega
  have hm : (d : ℝ) / 2 + ((100 * d + 1000 : ℕ) : ℝ) + 6 < ((102 * d + 1020 : ℕ) : ℝ) := by
    push_cast; linarith
  have hmM : ((8 * d + 80 : ℕ) : ℝ) + 4 < ((102 * d + 1020 : ℕ) : ℝ) := by
    push_cast; linarith
  have hKm : (K : ℝ) + d / 2 + 4 < ((102 * d + 1020 : ℕ) : ℝ) := hK
  obtain ⟨Rstar, Cg, cg, hRstar, hCg, hcg, hbound⟩ :=
    s67bd_uniform_gradient H (4 * d + 42) (8 * d + 80) hM (100 * d + 1000) (102 * d + 1020) hj' hm hmM
  obtain ⟨εS, rS, c0S, cS, CS, hεS, hrS, hc0S, hcS, hCS, hconcS, hSch⟩ :=
    HRS.MS.MovSch.mov_schwartz_proof (d := d) (s := s) H.hd H.hs0 H.hsd β a H.hβ H.hq K (100 * d + 1000)
      (102 * d + 1020) hj' hm hKm ρβ H.hρ
  have hr' : 0 < min (min rS (min Rstar 1)) Rs :=
    lt_min (lt_min hrS (lt_min hRstar one_pos)) hRs
  obtain ⟨ε', hε', hε'S, hconc⟩ := s67_shrink hconcS hCS hεS hr' ((min_le_left _ _).trans (min_le_left _ _))
  set r' := min (min rS (min Rstar 1)) Rs with hr'def
  have hr'1 : r' ≤ 1 := (min_le_left _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hr'S : r' ≤ rS := (min_le_left _ _).trans (min_le_left _ _)
  have hr'R : r' ≤ Rstar :=
    (min_le_left _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  set K₁ : ℝ := max C₁ 1 with hK₁
  have hK₁0 : 0 < K₁ := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hεpos : 0 < min ε' (r' / K₁) := lt_min hε' (div_pos hr' hK₁0)
  have hCε : C₁ * min ε' (r' / K₁) ≤ r' := by
    calc C₁ * min ε' (r' / K₁) ≤ K₁ * min ε' (r' / K₁) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hεpos.le
      _ ≤ K₁ * (r' / K₁) := mul_le_mul_of_nonneg_left (min_le_right _ _) hK₁0.le
      _ = r' := by field_simp
  have hεS' : min ε' (r' / K₁) ≤ εS := (min_le_left _ _).trans hε'S
  refine ⟨min ε' (r' / K₁), r', hεpos, hr', hr'1, (min_le_right _ _), hCε, ?_, ?_⟩
  · refine ⟨Cg, cg, hCg, hcg, fun f0 ρ hρ T φ f hT hf hφ hosc r'' hr'' => ?_⟩
    exact hbound r' c₁ (hr'.le) hr'R hc₁.le f0 ρ hρ T φ f hT hf hφ hosc r'' hr''
  · intro L
    obtain ⟨CKL, hCKL⟩ := hSch L
    refine ⟨|CKL| * εS, fun ε ψ ρ hψ hres => ?_⟩
    have hsm := s103n_small_class hres hCε
    have hI := s103n_initial_class H hεS' hψ
    obtain ⟨ρc, hρc, hu⟩ := hconcS.exists_unique hI
    have hρρc : ∀ t : ℝ, 0 ≤ t → ρ t = ρc t := fun t ht =>
      hu r' c₁ hr'S hc₁.le ρ hsm t ht
    obtain ⟨ρ', hd', hb'⟩ := hCKL _ hI ρc hρc
    refine ⟨ρ', fun t ht x => ?_, fun t ht => ?_⟩
    · refine (hd' t ht x).congr_of_mem (fun τ hτ => ?_) (Set.mem_Ici.2 le_rfl)
      exact congrFun (hρρc τ (ht.trans hτ)) x ▸ rfl
    · obtain ⟨h1, h2, h3⟩ := hb' t ht
      rw [hρρc t ht]
      refine ⟨h1, h2, fun k hk x => (h3 k hk x).trans ?_⟩
      have hex : Real.exp (-cS * t) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
      have hεS0 : 0 ≤ εS := hεS.le
      calc CKL * εS * Real.exp (-cS * t) ≤ |CKL| * εS * Real.exp (-cS * t) := by
            gcongr; exact le_abs_self _
        _ ≤ |CKL| * εS * 1 := mul_le_mul_of_nonneg_left hex (by positivity)
        _ = _ := mul_one _

end HRS.MS.R2WinOrbNL

end
