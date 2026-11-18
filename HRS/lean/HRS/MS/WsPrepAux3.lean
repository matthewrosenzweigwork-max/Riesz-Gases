import HRS.MS.WsPrepAux1

/-!
# S21R packet 3: a resulting solution of S2.1 (ii) lies in the S6.3 uniqueness class

`s21p_resulting_in_class`: let `hconc : MovNonlinearConclusion d s a β ρβ j m ε63 r c₀ c C₆₃` be the S6.3 conclusion at the frozen indices
`j + 1 = 100d + 1001`, `m = 102d + 1020` (the indices of `IsAdmissiblePerturbation` / `IsResultingSolution`).  If `ρβ > 0`, `εstar ≤ ε63`,
`C₁ εstar ≤ r`, `ε ψ` is `εstar`-admissible and `ρ` is a resulting solution with constants `(c₁, C₁)`, then
* `f0 = εψ` lies in the initial class `MovInitialClass ρβ j m ε63` (the memberships in `C_b^{j+1}` and `Σ^m` come from the compact support and
  from the `t = 0` weighted bound of `IsResultingSolution`; `IsAdmissiblePerturbation.small` alone does not give `MemOsc` since `oscNorm`
  is a `tsum`), and
* `ρ` lies in the small class `MovInSmallClass d s a β ρβ m r c₀ f0` of S6.3: it is in the class of radius `C₁εstar` and exponent `c₁`
  (`IsResultingSolution` gives exactly that class), hence equals the S6.3 solution on `[0,∞)` by the uniqueness clause
  (`MovNonlinearConclusion.exists_unique`), which is in the class of radius `r` and exponent `c₀`.

`s21p_C₁_pos`: a resulting solution has `C₁ > 0` (otherwise the ratio bound contradicts `∫ρ 0 = 1`).
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace HRS.Whole

variable {d : ℕ}

theorem s21p_C₁_pos {s a β : ℝ} {ρβ : Euc d → ℝ} (hρβpos : ∀ x, 0 < ρβ x) {εstar ε : ℝ}
    {ψ : Euc d → ℝ} {c₁ C₁ : ℝ} {ρ : ℝ → Euc d → ℝ}
    (hres : IsResultingSolution d s a β ρβ εstar ε ψ c₁ C₁ ρ) : 0 < C₁ := by
  by_contra hC
  rw [not_lt] at hC
  have hd0 := ((hres.global 0).density 0 ⟨le_rfl, le_rfl⟩)
  have hz : ∀ x, ρ 0 x = 0 := fun x => by
    have h1 := (hres.ratio 0 le_rfl x).2
    have h2 : C₁ * ρβ x ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hC (hρβpos x).le
    exact le_antisymm (h1.trans h2) (hd0.nonneg x)
  have hint := hd0.integral_one
  simp only [hz, integral_zero] at hint
  exact zero_ne_one hint

theorem s21p_resulting_in_class {s a β : ℝ} {ρβ : Euc d → ℝ} (hρβpos : ∀ x, 0 < ρβ x)
    {j m : ℕ} (hj : j + 1 = 100 * d + 1001) (hm : (m : ℝ) = 102 * (d : ℝ) + 1020)
    {ε63 r c₀ c C₆₃ : ℝ} (hconc : MovNonlinearConclusion d s a β ρβ j m ε63 r c₀ c C₆₃)
    {εstar ε : ℝ} {ψ : Euc d → ℝ} {c₁ C₁ : ℝ} {ρ : ℝ → Euc d → ℝ}
    (hε63 : εstar ≤ ε63) (hr : C₁ * εstar ≤ r)
    (hadm : IsAdmissiblePerturbation ρβ εstar ε ψ)
    (hres : IsResultingSolution d s a β ρβ εstar ε ψ c₁ C₁ ρ) :
    MovInitialClass ρβ j m ε63 (fun x => ε * ψ x) ∧
      MovInSmallClass d s a β ρβ m r c₀ (fun x => ε * ψ x) ρ := by
  have hC₁ := s21p_C₁_pos hρβpos hres
  have hρ0 : ∀ x, ρ 0 x = ρβ x * (1 + ε * ψ x) := fun x => by
    have := congrFun hres.init x
    rw [this]; unfold perturbedDensity; ring
  have hv0 : (fun x => (ρ 0 x - ρβ x) / Real.sqrt (ρβ x)) =
      fun x => Real.sqrt (ρβ x) * (ε * ψ x) := by
    funext x
    rw [hρ0 x]
    have h1 : ρβ x * (1 + ε * ψ x) - ρβ x = ρβ x * (ε * ψ x) := by ring
    rw [h1, mul_div_right_comm, Real.div_sqrt]
  have hcs : HasCompactSupport (fun x => ε * ψ x) :=
    hadm.compactSupport.comp_left (g := fun y => ε * y) (by simp)
  have hsm : ContDiff ℝ ∞ (fun x => ε * ψ x) := contDiff_const.mul hadm.smooth
  -- the initial class
  have hf0 : MovInitialClass ρβ j m ε63 (fun x => ε * ψ x) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · refine ⟨hsm.of_le (by exact_mod_cast le_top), fun i _ => ?_⟩
      exact ((hsm.continuous_iteratedFDeriv (m := i) (by exact_mod_cast le_top)).norm
        ).bddAbove_range_of_hasCompactSupport (hcs.iteratedFDeriv i).norm
    · have := (hres.weighted 0 le_rfl).1
      rw [hv0] at this
      rw [hm]
      exact this
    · calc ∫ x, ε * ψ x * ρβ x = ε * ∫ x, ψ x * ρβ x := by
            rw [← integral_const_mul]; congr 1; funext x; ring
        _ = 0 := by rw [hadm.meanZero, mul_zero]
    · have h1 := hadm.small
      have e : (fun x => ε * Real.sqrt (ρβ x) * ψ x) = fun x => Real.sqrt (ρβ x) * (ε * ψ x) := by
        funext x; ring
      rw [e] at h1
      rw [hj, hm]
      exact h1.trans hε63
  refine ⟨hf0, ?_⟩
  -- `ρ` is in the class of radius `C₁ εstar` and exponent `c₁`
  have hcls : MovInSmallClass d s a β ρβ m (C₁ * εstar) c₁ (fun x => ε * ψ x) ρ := by
    refine ⟨hres.global, fun x => hρ0 x, fun t ht => ?_, ?_, hres.regular⟩
    · have h := hres.weighted t ht
      rw [hm]
      exact ⟨h.1, h.2⟩
    · rw [hm]; exact hres.cont
  obtain ⟨ρ', hρ', huniq⟩ := hconc.exists_unique hf0
  have heq : ∀ t : ℝ, 0 ≤ t → ρ t = ρ' t := fun t ht =>
    huniq (C₁ * εstar) c₁ hr hres.cpos.le ρ hcls t ht
  have hmv : ∀ t : ℝ, 0 ≤ t → movV ρβ ρ t = movV ρβ ρ' t := fun t ht => by
    funext x; simp only [movV, heq t ht]
  refine ⟨hres.global, fun x => hρ0 x, fun t ht => ?_, ?_, hres.regular⟩
  · rw [hmv t ht]; exact hρ'.weighted t ht
  · refine (hρ'.cont).congr fun t ht => ?_
    simp only [hmv t ht]

end HRS.Whole
