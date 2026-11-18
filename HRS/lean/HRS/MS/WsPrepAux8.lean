import HRS.MS.WsPrepAux7

/-!
# S21R packet 8: a resulting solution lies in the S6.3 small class at LOW indices

`s21p_resulting_in_class_low`: as `s21p_resulting_in_class` (WsPrepAux3), but for S6.3 conclusions at indices `(j, m)` BELOW the frozen
indices of `IsAdmissiblePerturbation` / `IsResultingSolution` (`j + 1 ≤ 100d + 1001`, `m ≤ 102d + 1020`).  The `C_b^{j+1}` and `Σ^m` norms
are monotone in the index (WsPrepAux7), and the continuity of `t ↦ v_t` into `Σ^{102d+1020}` gives the continuity into `Σ^m`.
This is the form used with the proved conditional S6.6 (`mov_entropy_of_diss`, which works at `j = 1`, `m = d/2 + 8`).
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace HRS.Whole

variable {d : ℕ}

theorem s21p_resulting_in_class_low {s a β : ℝ} {ρβ : Euc d → ℝ}
    {j m : ℕ} (hj : j + 1 ≤ 100 * d + 1001) (hm : (m : ℝ) ≤ 102 * (d : ℝ) + 1020)
    {ε63 r c₀ c C₆₃ : ℝ} (hconc : MovNonlinearConclusion d s a β ρβ j m ε63 r c₀ c C₆₃)
    {εstar ε : ℝ} {ψ : Euc d → ℝ} {c₁ C₁ : ℝ} {ρ : ℝ → Euc d → ℝ}
    (hε63 : εstar ≤ ε63) (hr : C₁ * εstar ≤ r)
    (hadm : IsAdmissiblePerturbation ρβ εstar ε ψ)
    (hres : IsResultingSolution d s a β ρβ εstar ε ψ c₁ C₁ ρ) :
    MovInitialClass ρβ j m ε63 (fun x => ε * ψ x) ∧
      MovInSmallClass d s a β ρβ m r c₀ (fun x => ε * ψ x) ρ := by
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
  have hosc_hi : MemOsc (102 * (d : ℝ) + 1020) (fun x => Real.sqrt (ρβ x) * (ε * ψ x)) := by
    have := (hres.weighted 0 le_rfl).1
    rw [hv0] at this
    exact this
  -- the initial class
  have hf0 : MovInitialClass ρβ j m ε63 (fun x => ε * ψ x) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · refine ⟨hsm.of_le (by exact_mod_cast le_top), fun i _ => ?_⟩
      exact ((hsm.continuous_iteratedFDeriv (m := i) (by exact_mod_cast le_top)).norm
        ).bddAbove_range_of_hasCompactSupport (hcs.iteratedFDeriv i).norm
    · exact s21p_memOsc_mono hm hosc_hi
    · calc ∫ x, ε * ψ x * ρβ x = ε * ∫ x, ψ x * ρβ x := by
            rw [← integral_const_mul]; congr 1; funext x; ring
        _ = 0 := by rw [hadm.meanZero, mul_zero]
    · have h1 := hadm.small
      have e : (fun x => ε * Real.sqrt (ρβ x) * ψ x) = fun x => Real.sqrt (ρβ x) * (ε * ψ x) := by
        funext x; ring
      rw [e] at h1
      refine le_trans ?_ (h1.trans hε63)
      exact add_le_add (s21p_cbNorm_mono_k hj _) (s21p_oscNorm_mono hm hosc_hi)
  refine ⟨hf0, ?_⟩
  -- `ρ` is in the class of radius `C₁ εstar` and exponent `c₁`, at the index `m`
  have hcls : MovInSmallClass d s a β ρβ m (C₁ * εstar) c₁ (fun x => ε * ψ x) ρ := by
    refine ⟨hres.global, fun x => hρ0 x, fun t ht => ?_, ?_, hres.regular⟩
    · have h := hres.weighted t ht
      refine ⟨s21p_memOsc_mono hm h.1, ?_⟩
      exact (s21p_oscNorm_mono hm h.1).trans h.2
    · exact s21p_continuousOn_ofFun_mono hm (fun t ht => (hres.weighted t ht).1) hres.cont
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
