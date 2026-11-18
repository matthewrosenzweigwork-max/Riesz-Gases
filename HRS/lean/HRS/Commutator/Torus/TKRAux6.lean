import HRS.Commutator.Torus.TKRAux5

/-!
# T-KR helpers, part 6: summation by parts for the symbol of `∇g_{>}` (lattice differences of
`(1-χ(ηξ)) ξ_i |ξ|^{s-d}`)
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform ContDiff

namespace HRS.Commutator.TorusNote

open HRS HRS.KernelGrad HRS.PDE.Kern

variable {d : ℕ} {s η : ℝ}

/-- the symbol `‖ξ‖^{s-d}(1-χ(2ξ)) · ξ_i · (1-χ(ρξ))` -/
def tkrGn (d : ℕ) (s ρ : ℝ) (i : Fin d) (ξ : Euc d) : ℝ :=
  (‖ξ‖ ^ (s - d) * (1 - Whole.chi ((2 : ℝ) • ξ))) *
    inner ℝ (EuclideanSpace.single i (1 : ℝ)) ξ * (1 - Whole.chi (ρ • ξ))

lemma tkr_chi_props : ContDiff ℝ ∞ (Whole.chi : Euc d → ℝ) ∧ (∀ ξ : Euc d, ‖ξ‖ ≤ 1 → Whole.chi ξ = 1) ∧
    (∀ ξ : Euc d, 2 ≤ ‖ξ‖ → Whole.chi ξ = 0) :=
  ⟨Whole.cmxFB_chi_contDiff, fun _ h => Whole.cmxFB_chi_one h, fun _ h => Whole.cmxFB_chi_zero h⟩

lemma contDiff_tkrGn (s ρ : ℝ) (i : Fin d) : ContDiff ℝ ∞ (tkrGn d s ρ i) := by
  obtain ⟨hs, h1, h2⟩ := tkr_chi_props (d := d)
  have hT1 := cutHyp_one_sub hs h1 h2
  have hQ := contDiff_Q (s - d) hT1 (fun ζ hζ => by simp [h1 ζ hζ])
  have hW : ContDiff ℝ ∞ (fun ξ : Euc d => 1 - Whole.chi (ρ • ξ)) :=
    contDiff_const.sub (hs.comp (contDiff_id.const_smul ρ))
  exact (hQ.mul (innerSL ℝ (EuclideanSpace.single i (1 : ℝ))).contDiff).mul hW

lemma tkrGn_symb (s : ℝ) : ∃ B : ℕ → ℝ, ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 → ∀ i : Fin d,
    HRS.Symb (-(s - d + 1)) B (tkrGn d s ρ i) := by
  obtain ⟨hs, h1, h2⟩ := tkr_chi_props (d := d)
  have hT1 := cutHyp_one_sub hs h1 h2
  obtain ⟨BQ, hBQ⟩ := exists_symb_Q (s - d) hT1 (fun ζ hζ => by simp [h1 ζ hζ])
    (fun ζ hζ => by simp [h2 ζ hζ])
  obtain ⟨BW, hBW⟩ := hT1.symb
  set B1 : ℕ → ℝ := fun m => ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * BQ i * Bl (m - i) with hB1
  set B2 : ℕ → ℝ := fun m => ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * B1 i * BW (m - i) with hB2
  refine ⟨B2, fun ρ hρ hρ1 i => ?_⟩
  have hQ := contDiff_Q (s - d) hT1 (fun ζ hζ => by simp [h1 ζ hζ])
  have hW : ContDiff ℝ ∞ (fun ξ : Euc d => 1 - Whole.chi (ρ • ξ)) :=
    contDiff_const.sub (hs.comp (contDiff_id.const_smul ρ))
  have hv : ‖(EuclideanSpace.single i (1 : ℝ) : Euc d)‖ ≤ 1 := by simp
  have s1 := Symb.mul hQ (innerSL ℝ (EuclideanSpace.single i (1 : ℝ))).contDiff hBQ (symb_inner _ hv)
  have s2 := Symb.mul (hQ.mul (innerSL ℝ (EuclideanSpace.single i (1 : ℝ))).contDiff) hW s1
    (hBW ρ hρ hρ1)
  have e : -(s - (d : ℝ)) + -1 + 0 = -(s - d + 1) := by ring
  rw [e] at s2
  exact s2

lemma tkrGn_eq_zero (s ρ : ℝ) (hρ : 0 < ρ) (i : Fin d) (ξ : Euc d) (hξ : ‖ξ‖ < 1 / ρ) :
    tkrGn d s ρ i ξ = 0 := by
  obtain ⟨-, h1, -⟩ := tkr_chi_props (d := d)
  have : Whole.chi (ρ • ξ) = 1 := by
    apply h1
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hρ]
    rw [lt_div_iff₀ hρ] at hξ
    nlinarith
  simp [tkrGn, this]

lemma tkrGn_eq (s ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (i : Fin d) (ξ : Euc d) :
    tkrGn d s ρ i ξ = ‖ξ‖ ^ (s - d) * inner ℝ (EuclideanSpace.single i (1 : ℝ)) ξ *
      (1 - Whole.chi (ρ • ξ)) := by
  obtain ⟨-, h1, h2⟩ := tkr_chi_props (d := d)
  by_cases hχ : Whole.chi (ρ • ξ) = 1
  · simp [tkrGn, hχ]
  · have hn : 1 < ρ * ‖ξ‖ := by
      by_contra hle
      push Not at hle
      apply hχ
      apply h1
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hρ]
      exact hle
    have hξ : 1 ≤ ‖ξ‖ := by nlinarith [norm_nonneg ξ]
    have : Whole.chi ((2 : ℝ) • ξ) = 0 := by
      apply h2
      rw [norm_smul]; norm_num; linarith
    simp [tkrGn, this]

lemma tkrGn_fdiffs_bound (s : ℝ) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 → ∀ i j : Fin d, ∀ ξ : Euc d,
      ‖fdiffs (List.replicate N (EuclideanSpace.single j (1 : ℝ))) (tkrGn d s ρ i) ξ‖ ≤
        C * (1 + ‖ξ‖) ^ (s - d + 1 - N) ∧
      (‖ξ‖ < 1 / ρ - N → fdiffs (List.replicate N (EuclideanSpace.single j (1 : ℝ)))
        (tkrGn d s ρ i) ξ = 0) := by
  obtain ⟨B, hB⟩ := tkrGn_symb (d := d) s
  refine ⟨|BIter N (-(s - d + 1)) B 0|, abs_nonneg _, fun ρ hρ hρ1 i j ξ => ?_⟩
  have hL : ∀ w ∈ List.replicate N (EuclideanSpace.single j (1 : ℝ) : Euc d), ‖w‖ ≤ 1 := by
    intro w hw
    rw [List.eq_of_mem_replicate hw]
    simp
  have hsy := Symb.fdiffs (List.replicate N (EuclideanSpace.single j (1 : ℝ) : Euc d))
    (contDiff_tkrGn s ρ i) (hB ρ hρ hρ1 i) hL
  refine ⟨?_, fun hξ => ?_⟩
  · have := hsy 0 ξ
    rw [norm_iteratedFDeriv_zero, List.length_replicate] at this
    have e : -(-(s - (d : ℝ) + 1) + (N : ℝ)) - ((0 : ℕ) : ℝ) = s - d + 1 - N := by push_cast; ring
    rw [e] at this
    refine this.trans ?_
    exact mul_le_mul_of_nonneg_right (le_abs_self _) (Real.rpow_nonneg (by positivity) _)
  · refine fdiffs_eq_zero (List.replicate N (EuclideanSpace.single j (1 : ℝ) : Euc d))
      (fun η hη => tkrGn_eq_zero s ρ hρ i η hη) hL ξ ?_
    rwa [List.length_replicate]

end HRS.Commutator.TorusNote
