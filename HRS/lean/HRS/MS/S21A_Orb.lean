import HRS.MS.S21A_Mono
import HRS.MS.WsPrepI4

/-!
# S21A packet 3: the orbit input `S21iOrbClass` of INIT from S10.3 and the terminal-time regularity

`s21a_cont_of_diff`: the initial-time orbit `τ ↦ U(0,τ)φ(x)` is continuous on `[0,T₀]` as soon as the difference quotients in `C_b²` converge
(`S104nOrbit.diff01` at `r = 0`).
`s21a_orbClass`: `S21iOrbClass d s a β T εstar c₁ C₁ Corb` from the window-test clause of S10.3 (`r2_window_orbits`, last clause) for the class at
a larger smallness `ε₃ ≥ εstar` and `S104nAllOrb` (existence of the adjoint solutions of the oscillator tests and continuity of the orbit).
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S21A

open HRS.Whole HRS.MS.R2WinErr HRS.MS.S21
open HRS (Euc cbNorm MemCb)

variable {d : ℕ}

theorem s21a_cont_of_diff {C : WholeCoeff d} {φ : Euc d → ℝ} {T0 : ℝ} (hT0 : 0 ≤ T0) (h : S104nOrbit C φ T0)
    (x : Euc d) : ContinuousOn (fun τ : ℝ => propagatorW C 0 τ φ x) (Icc 0 T0) := by
  have hd := h.diff01 0 ⟨le_rfl, hT0⟩
  simp only [zero_add, sub_zero] at hd
  intro τ hτ
  obtain ⟨δ, hδ, hq⟩ := hd τ hτ 1 one_pos
  set G' : ℝ := (propagatorW C 0 τ (generatorW C τ φ)) x with hG'
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  set K : ℝ := 1 + |G'| with hK
  have hK0 : 0 < K := by positivity
  refine ⟨min δ (ε / K), lt_min hδ (div_pos hε hK0), fun τ' hτ' hdist => ?_⟩
  by_cases hh : τ' = τ
  · subst hh; simpa using hε
  have hne : τ' - τ ≠ 0 := sub_ne_zero.2 hh
  have hlt : |τ' - τ| < min δ (ε / K) := by simpa [Real.dist_eq] using hdist
  have h1 := hq (τ' - τ) hne (lt_of_lt_of_le hlt (min_le_left _ _)) (by simpa using hτ') 0 (by norm_num) x
  rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at h1
  simp only [add_sub_cancel] at h1
  set D : ℝ := propagatorW C 0 τ' φ x - propagatorW C 0 τ φ x with hD
  have h2 : |(τ' - τ)⁻¹ * D| ≤ K := by
    have : |(τ' - τ)⁻¹ * D| ≤ |(τ' - τ)⁻¹ * D - G'| + |G'| := by
      have := abs_sub_abs_le_abs_sub ((τ' - τ)⁻¹ * D) G'
      linarith
    linarith
  have h3 : |D| ≤ K * |τ' - τ| := by
    have e : D = (τ' - τ) * ((τ' - τ)⁻¹ * D) := by field_simp
    rw [e, abs_mul]
    calc |τ' - τ| * |(τ' - τ)⁻¹ * D| ≤ |τ' - τ| * K := mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
      _ = K * |τ' - τ| := mul_comm _ _
  have h4 : |τ' - τ| < ε / K := lt_of_lt_of_le hlt (min_le_right _ _)
  rw [Real.dist_eq]
  calc |propagatorW C 0 τ' φ x - propagatorW C 0 τ φ x| = |D| := rfl
    _ ≤ K * |τ' - τ| := h3
    _ < K * (ε / K) := mul_lt_mul_of_pos_left h4 hK0
    _ = ε := by field_simp

theorem s21a_orbClass (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {a β : ℝ} (ha : 0 < a) (hβ : 0 < β) {T : ℝ}
    (hT : 0 < T) {εstar ε₃ c₁ C₁ C : ℝ} (hle : εstar ≤ ε₃)
    (hwin : ∀ ρβ : Euc d → ℝ, IsThermalEquilibrium d s a β ρβ → ∀ ρ : ℝ → Euc d → ℝ,
      IsR2WindowTrajectory d s a β ρβ ε₃ c₁ C₁ ρ → ∀ α : MultiIndex d,
      (∀ t : ℝ, 0 ≤ t → ∃ f : ℝ → Euc d → ℝ, IsClassicalAdjointW ((quadraticGradientDyn d s a β).coeff ρ) t
        (oscTestFun (((24 * d + 240 : ℕ)) : ℝ) α) f) →
      ∀ b : ℝ, 0 ≤ b → ∀ n : ℕ,
        MemCb (4 * d + 42) (r2WindowTest ((quadraticGradientDyn d s a β).coeff ρ) (((24 * d + 240 : ℕ)) : ℝ) T b n α) ∧
        cbNorm (4 * d + 42) (r2WindowTest ((quadraticGradientDyn d s a β).coeff ρ) (((24 * d + 240 : ℕ)) : ℝ) T b n α) ≤
          C * (1 + (n : ℝ)) ^ (-(5 : ℝ) / 4) *
            oscEigenvalue d α ^ ((((18 * d + 180 : ℕ) : ℝ) - ((24 * d + 240 : ℕ) : ℝ)) / 2))
    (hNL : S104nAllOrb d s a β εstar c₁ C₁) :
    S21iOrbClass d s a β T εstar c₁ C₁ (max C 0) := by
  intro ρβ hρβ ε ψ hadm ρ hres
  obtain ⟨hadm', hres'⟩ := s21a_cls_mono hd hs0 hsd ha hβ hρβ hle hadm hres
  have htraj : IsR2WindowTrajectory d s a β ρβ ε₃ c₁ C₁ ρ := Or.inr ⟨ε, ψ, hadm', hres'⟩
  refine ⟨le_max_right _ _, fun bw hbw n α => ?_, fun bw hbw α x => ?_⟩
  · have h := hwin ρβ hρβ ρ htraj α
      (fun t ht => (hNL ρβ hρβ ε ψ ρ hadm hres α t ht).ex0 t ⟨ht, le_rfl⟩) bw hbw n
    refine ⟨h.1, h.2.trans ?_⟩
    have hB : 0 ≤ s21iB d α := s21i_B_nonneg α
    have hn : 0 ≤ (1 + (n : ℝ)) ^ (-(5 : ℝ) / 4) := Real.rpow_nonneg (by positivity) _
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hn) hB
  · have hc := s21a_cont_of_diff (T0 := bw + T) (by linarith)
      (hNL ρβ hρβ ε ψ ρ hadm hres α (bw + T) (by linarith)) x
    refine hc.comp (continuousOn_const.add continuousOn_id) fun u hu => ⟨by linarith [hu.1], by linarith [hu.2]⟩

end HRS.MS.S21A
