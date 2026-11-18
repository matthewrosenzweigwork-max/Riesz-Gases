import HRS.MS.S104bNL8

/-!
# S10.5 (nonlinear), packet S104b-NL9: the window comparison `S105CompareNL` for the resulting solutions

`s104b_compare_NL`: `S105CompareNL d s a β T εstar c₁ C₁` (R2GenInitNL4) from the master window comparison `s104b_master` and the moving window data `s104b_data`, under the
analytic inputs `S104nAllOrb` (adjoint-orbit terminal-time regularity), the S10.3 gradient orbit bounds `hgrad`, and the regularity `S105nReg` of the resulting solutions.
Constants as in `s105_compare_stat`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.S104b

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MS.R2GenInit HRS.MS.R2WinErr HRS.MS.S21m

variable {d : ℕ}

theorem s104b_compare_NL (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {a β : ℝ} (ha : 0 < a) (hβ : 0 < β)
    {T : ℝ} (hT : 0 < T) {εstar c₁ C₁ : ℝ} (hNL : S104nAllOrb d s a β εstar c₁ C₁)
    (Cs0 cdec : ℝ) (hcdec : 0 < cdec) (hsum : Summable (s104_b d))
    (hgrad : ∀ ρβ : Euc d → ℝ, IsThermalEquilibrium d s a β ρβ → ∀ (ε : ℝ) (ψ : Euc d → ℝ) (ρ : ℝ → Euc d → ℝ),
      IsAdmissiblePerturbation ρβ εstar ε ψ → IsResultingSolution d s a β ρβ εstar ε ψ c₁ C₁ ρ →
      ∀ α : MultiIndex d,
      (∀ t : ℝ, 0 ≤ t → R2OrbitGrad ((quadraticGradientDyn d s a β).coeff ρ) (4 * d + 42) t
        (oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) α) (Cs0 * s104_b d α) cdec) ∧
      (∀ t : ℝ, 0 ≤ t → R2OrbitGrad ((quadraticGradientDyn d s a β).coeff ρ) (4 * d + 42) t
        (generatorW ((quadraticGradientDyn d s a β).coeff ρ) t (oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) α))
        (Cs0 * s104_b d α) cdec))
    (hreg : S105nReg d s a β εstar c₁ C₁) : S105CompareNL d s a β T εstar c₁ C₁ := by
  obtain ⟨Cs, Cw, hCs, hCw, hCmp⟩ := s105_win_compare (d := d) ((wholeSpaceIndex d : ℕ) : ℝ) T hT
  obtain ⟨M, L, Mom, C₀c, hC₀c, hcl⟩ := s104n_hcls hd hs0 hsd ha hβ εstar c₁ C₁
  refine ⟨max 1 (max Cs Cw), le_trans zero_le_one (le_max_left _ _), ?_⟩
  intro ρβ hρβ ρ hρcls N hN _ Ω _ P _ X₀ W X hreal _ η₀ _ Y hY hcontc b hb F Wt hFb hBt
  obtain ⟨ε, ψ, hadm, hres⟩ := hρcls
  have htraj : IsR2WindowTrajectory d s a β ρβ εstar c₁ C₁ ρ := Or.inr ⟨ε, ψ, hadm, hres⟩
  obtain ⟨hρc, -, hjm⟩ := hcl ρβ hρβ ρ htraj
  have hd1 : 1 ≤ d := by omega
  have hT0 : 0 ≤ T := hT.le
  have hτ' : 0 < b + T := by linarith
  have hS : S21mData d s a β T b ρ :=
    s104b_data hd hs0 hsd ha hβ hρβ hres (fun α T0 h0 => hNL ρβ hρβ ε ψ ρ hadm hres α T0 h0) Cs0 cdec hcdec hsum
      (hgrad ρβ hρβ ε ψ ρ hadm hres) (hreg ρβ hρβ ε ψ ρ hadm hres) hjm (hρc 0 le_rfl).2.2.1 hT hb
  have hm : (d : ℝ) < ((wholeSpaceIndex d : ℕ) : ℝ) := by
    unfold wholeSpaceIndex; push_cast; linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
  obtain ⟨hsm, hw1⟩ := s104b_master hCmp hd hs0 hsd hβ hT hb hS hN P X₀ W X hreal η₀ Y hY (hcontc b hb) F Wt hFb hBt
  have hX : IsWholeStrongSolution P (quadraticGradientDyn d s a β) (b + T) X₀ W X := hreal.solution (b + T)
  have hΞP : AEMeasurable (flucPathW ((wholeSpaceIndex d : ℕ) : ℝ) T b (Real.sqrt N) X ρ) P :=
    s21p_fluc_window_aemeas hd1 (by omega) hm hb hT0 P X ρ (Real.sqrt N) (fun t => hX.adapted t) hX.cont
      (fun t ht => hS.hprob ht) hS.hcont
  have hYP : AEMeasurable (processWindow ((wholeSpaceIndex d : ℕ) : ℝ) T b Y) P := by
    have e : processWindow ((wholeSpaceIndex d : ℕ) : ℝ) T b Y = HRS.Uniform.windowPath b T Y := by
      funext ζ
      unfold processWindow windowPathOf HRS.Uniform.windowPath
      rfl
    rw [e]
    exact HRS.Uniform.Comp28.aemeasurable_windowPath_a P hb hT0 hτ' _ (fun t _ => (hY (b + T)).meas t)
      (hY (b + T)).cont
  refine ⟨hΞP, hYP, ?_, ?_⟩
  · refine hsm.trans ?_
    have h1 : ENNReal.ofReal Cs ≤ ENNReal.ofReal (max 1 (max Cs Cw)) :=
      ENNReal.ofReal_le_ofReal ((le_max_left _ _).trans (le_max_right _ _))
    have h2 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (max 1 (max Cs Cw)) := by
      rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (le_max_left _ _)
    calc ENNReal.ofReal Cs * Wt + F + _
        ≤ ENNReal.ofReal (max 1 (max Cs Cw)) * Wt + ENNReal.ofReal (max 1 (max Cs Cw)) * F +
          ENNReal.ofReal (max 1 (max Cs Cw)) * _ := by
          gcongr
          · exact le_mul_of_one_le_left bot_le h2
          · exact le_mul_of_one_le_left bot_le h2
      _ = _ := by ring
  · refine hw1.trans ?_
    have h1 : ENNReal.ofReal Cw ≤ ENNReal.ofReal (max 1 (max Cs Cw)) :=
      ENNReal.ofReal_le_ofReal ((le_max_right _ _).trans (le_max_right _ _))
    have h2 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (max 1 (max Cs Cw)) := by
      rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (le_max_left _ _)
    calc ENNReal.ofReal Cw * Wt ^ (1 / 2 : ℝ) + F + _
        ≤ ENNReal.ofReal (max 1 (max Cs Cw)) * Wt ^ (1 / 2 : ℝ) + ENNReal.ofReal (max 1 (max Cs Cw)) * F +
          ENNReal.ofReal (max 1 (max Cs Cw)) * _ := by
          gcongr
          · exact le_mul_of_one_le_left bot_le h2
          · exact le_mul_of_one_le_left bot_le h2
      _ = _ := by ring


end HRS.MS.S104b
