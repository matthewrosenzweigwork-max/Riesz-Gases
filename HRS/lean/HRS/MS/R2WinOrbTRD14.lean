import HRS.MS.R2WinOrbTRD13

/-!
# S10.3 packet [E], part 2: the helper lemmas of the assembly

Prefix `s103c_`, namespace `HRS.MS.R2WinOrbNL`.

* `s103c_adm_mono`, `s103c_res_mono`: admissible perturbations and resulting solutions for `ε_*` are admissible/resulting for every larger `ε_*`.
* `s103c_contOn_of_uc`: the weighted continuity of `t ↦ ρ'_t` implies the pointwise continuity.
* `S103cRhoPrimeUC`: the one extra input on the trajectory, the continuity of `t ↦ ρ'_t` into the weighted `C^K` norm (true for the solutions of the PDE; not part
  of the frozen `mov_schwartz`, which only gives the right derivative with Schwartz-time bounds).
* `s103c_timereg`: a classical adjoint solution with a datum of the class is continuous in time in `Bd N0` (from `s103b_gen_bd` and the iterated-difference average).
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory Metric
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace

namespace HRS.MS.R2WinOrbNL

open HRS HRS.Whole HRS.MS.Wad HRS.MS.Ul HRS.MS.Who HRS.MS.BreakdownS67 HRS.MS.MovLin HRS.MS.R2WinOrb

variable {d : ℕ}

theorem s103c_adm_mono {ρβ : Euc d → ℝ} {e1 e2 ε : ℝ} {ψ : Euc d → ℝ}
    (h : IsAdmissiblePerturbation ρβ e1 ε ψ) (he : e1 ≤ e2) : IsAdmissiblePerturbation ρβ e2 ε ψ :=
  { h with small := h.small.trans he }

theorem s103c_C₁_nonneg {s a β : ℝ} {ρβ : Euc d → ℝ} {e ε c₁ C₁ : ℝ} {ψ : Euc d → ℝ} {ρ : ℝ → Euc d → ℝ}
    (hres : IsResultingSolution d s a β ρβ e ε ψ c₁ C₁ ρ) (he : 0 < e) : 0 ≤ C₁ := by
  have h := (hres.weighted 0 le_rfl).2
  have h0 : 0 ≤ oscNorm (102 * (d : ℝ) + 1020) (fun x => (ρ 0 x - ρβ x) / Real.sqrt (ρβ x)) := by
    unfold oscNorm; exact Real.sqrt_nonneg _
  have h1 : 0 ≤ C₁ * e * Real.exp (-c₁ * 0) := h0.trans h
  simp only [mul_zero, Real.exp_zero, mul_one] at h1
  by_contra hC
  push_neg at hC
  nlinarith

theorem s103c_res_mono {s a β : ℝ} {ρβ : Euc d → ℝ} {e1 e2 ε c₁ C₁ : ℝ} {ψ : Euc d → ℝ} {ρ : ℝ → Euc d → ℝ}
    (hres : IsResultingSolution d s a β ρβ e1 ε ψ c₁ C₁ ρ) (he1 : 0 < e1) (he : e1 ≤ e2) :
    IsResultingSolution d s a β ρβ e2 ε ψ c₁ C₁ ρ := by
  have hC := s103c_C₁_nonneg hres he1
  have hm : ∀ t : ℝ, C₁ * e1 * Real.exp (-c₁ * t) ≤ C₁ * e2 * Real.exp (-c₁ * t) := fun t =>
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left he hC) (Real.exp_pos _).le
  exact { hres with
    weighted := fun t ht => ⟨(hres.weighted t ht).1, (hres.weighted t ht).2.trans (hm t)⟩
    velocity := fun t ht => (hres.velocity t ht).trans (ENNReal.ofReal_le_ofReal (hm t)) }

/-- The weighted continuity of `t ↦ ρ'_t` (hypothesis on the trajectory). -/
def S103cRhoPrimeUC (d : ℕ) (s a β : ℝ) (ρβ : Euc d → ℝ) (εstar c₁ C₁ : ℝ) (K L : ℕ) : Prop :=
  ∀ (ε : ℝ) (ψ : Euc d → ℝ) (ρ ρ' : ℝ → Euc d → ℝ), IsAdmissiblePerturbation ρβ εstar ε ψ →
    IsResultingSolution d s a β ρβ εstar ε ψ c₁ C₁ ρ →
    (∀ t : ℝ, 0 ≤ t → ∀ x, HasDerivWithinAt (fun τ => ρ τ x) (ρ' t x) (Set.Ici t) t) →
    (∃ A : ℝ, ∀ t : ℝ, 0 ≤ t → U2Dec K (L : ℝ) A (ρ' t)) →
    ∀ t : ℝ, 0 ≤ t → ∀ ε' : ℝ, 0 < ε' → ∃ η : ℝ, 0 < η ∧ ∀ σ : ℝ, 0 ≤ σ → |σ - t| < η →
      U2Dec K (L : ℝ) ε' (fun y => ρ' σ y - ρ' t y)

theorem s103c_contOn_of_uc {ρ' : ℝ → Euc d → ℝ} {K L : ℕ}
    (hUC : ∀ t : ℝ, 0 ≤ t → ∀ ε' : ℝ, 0 < ε' → ∃ η : ℝ, 0 < η ∧ ∀ σ : ℝ, 0 ≤ σ → |σ - t| < η →
      U2Dec K (L : ℝ) ε' (fun y => ρ' σ y - ρ' t y)) (x : Euc d) :
    ContinuousOn (fun σ => ρ' σ x) (Set.Ici 0) := by
  intro t ht
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  obtain ⟨η, hη, h⟩ := hUC t ht (ε / 2) (by positivity)
  refine ⟨η, hη, fun σ hσ hd => ?_⟩
  have h1 := (h σ hσ (by rwa [Real.dist_eq] at hd)).2 0 (Nat.zero_le _) x
  rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at h1
  have hw : u2Wt (L : ℝ) x ≤ 1 := by
    unfold u2Wt
    exact Real.rpow_le_one_of_one_le_of_nonpos (by linarith [norm_nonneg x]) (by
      have : (0 : ℝ) ≤ L := Nat.cast_nonneg L
      linarith)
  rw [Real.dist_eq]
  calc |ρ' σ x - ρ' t x| ≤ ε / 2 * u2Wt (L : ℝ) x := h1
    _ ≤ ε / 2 * 1 := mul_le_mul_of_nonneg_left hw (by positivity)
    _ < ε := by linarith

theorem s103c_timereg {s : ℝ} (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (a β : ℝ) (ha : 0 < a) (hβ : 0 < β)
    (N0 : ℕ) {L : ℝ} (hL : (d : ℝ) + ((N0 + 1 : ℕ) : ℝ) + s + 3 < L) (T : ℝ) (hT : 0 ≤ T) :
    ∃ Kt : ℝ, 0 ≤ Kt ∧ ∀ (ρ : ℝ → Euc d → ℝ) (Ah : ℝ), 0 ≤ Ah →
      (∀ τ ∈ Set.Icc (0 : ℝ) T, U2Dec (N0 + 1 + 1) L Ah (ρ τ)) →
      ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ (g : Euc d → ℝ) (Ag G : ℝ) (u : ℝ → Euc d → ℝ),
        IsClassicalAdjointW ((quadraticGradientDyn d s a β).coeff ρ) t g u →
        ContDiff ℝ ((N0 + 1 : ℕ) : WithTop ℕ∞) g →
        (∀ i, 1 ≤ i → i ≤ N0 + 1 → ∀ y, ‖iteratedFDeriv ℝ i g y‖ ≤ Ag * (1 + ‖y‖)⁻¹) →
        (∀ τ ∈ Set.Icc (0 : ℝ) t, ContDiff ℝ ((N0 + 1 + 2 : ℕ) : WithTop ℕ∞) (u τ) ∧
          ∀ i, 1 ≤ i → i ≤ N0 + 1 + 2 → ∀ y, ‖iteratedFDeriv ℝ i (u τ) y‖ ≤ G) →
        ∀ τ ∈ Set.Icc (0 : ℝ) t,
          Bd N0 (Kt * (Ag + (1 + Ah) * G) * (t - τ)) (fun y => u τ y - u t y) := by
  obtain ⟨KB, hKB0, hKB⟩ := s103b_gen_bd hd hs0 hsd a β ha hβ N0 hL T hT
  refine ⟨(max 1 (d : ℝ)) ^ N0 * KB, by positivity, ?_⟩
  intro ρ Ah hAh hU t ht g Ag G u hu hgC hgd hub τ hτ
  have hAg : 0 ≤ Ag := by
    have := hgd 1 le_rfl (by omega) 0
    simpa using (norm_nonneg _).trans this
  have hG : 0 ≤ G := by
    have := (hub τ hτ).2 1 le_rfl (by omega) 0
    exact (norm_nonneg _).trans this
  have hgen := hKB ρ Ah hAh hU t ht g u Ag G hu hgC hgd hub
  have hsub : ∀ σ ∈ Set.Icc τ t, σ ∈ Set.Icc (0 : ℝ) t := fun σ hσ => ⟨hτ.1.trans hσ.1, hσ.2⟩
  have hB0 : 0 ≤ KB * (Ag + (1 + Ah) * G) := by positivity
  have hcd : ContDiff ℝ (N0 : WithTop ℕ∞) (fun y => u τ y - u t y) :=
    (((hub τ hτ).1.of_le (by exact_mod_cast (by omega : N0 ≤ N0 + 1 + 2))).sub
      ((hub t ⟨ht.1, le_rfl⟩).1.of_le (by exact_mod_cast (by omega : N0 ≤ N0 + 1 + 2))))
  have := s103c_avg_bd (N := N0) hτ.2 hB0 (g := fun σ y => generatorW ((quadraticGradientDyn d s a β).coeff ρ) σ (u σ) y)
    (fun y => (s103c_ftc hu hτ.1 hτ.2 le_rfl y).2)
    (fun σ hσ => hgen σ (hsub σ hσ)) hcd (fun y => (s103c_ftc hu hτ.1 hτ.2 le_rfl y).1)
  refine this.mono_A (le_of_eq ?_)
  ring

end HRS.MS.R2WinOrbNL

end
