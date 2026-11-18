import HRS.MS.WsPrepAux1
import HRS.MS.WsStatAux3

/-!
# S21R packet 6: monotonicity of `S21PrepMain` in the constants, and the single-`C₀` reduction

`S21PrepMain.mono`: `S21PrepMain d s a β β₀ T c₁ C₁ εstar C₀ C` implies the same statement for every larger `C₀' ≥ C₀` and larger `C' ≥ C`
(the right-hand sides are monotone: `oN`, hence `localizationRate`, is monotone in `C₀`, and the brackets are nonnegative).

`whole_space_prepared_of_main'`: the reduction of `whole_space_prepared` to `S21PrepMain` at ONE completion constant `C₀'` (instead of all
`C₀ ≥` a threshold as in `whole_space_prepared_of_main`).  The frozen `C₀` is `max C₀' C₀min`, `C₀min` the threshold of
the proved completion clause.  This is the form that S6.6 (`MovEntAt`, one completion constant) supplies.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.Whole

variable {d : ℕ}

theorem s21p_localizationRate_nonneg (d : ℕ) (s C₀ : ℝ) (N : ℕ) : 0 ≤ localizationRate d s C₀ N := by
  unfold localizationRate
  exact Real.rpow_nonneg (add_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (Real.sqrt_nonneg _)) _

theorem s21p_localizationRate_mono {s C₀ C₀' : ℝ} (h : C₀ ≤ C₀') (N : ℕ) :
    localizationRate d s C₀ N ≤ localizationRate d s C₀' N := by
  unfold localizationRate
  refine Real.rpow_le_rpow (add_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (Real.sqrt_nonneg _))
    (add_le_add le_rfl (Real.sqrt_le_sqrt (HRS.MS.S21.s21_oN_mono h N))) ?_
  have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  positivity

theorem s21p_iN_nonneg (d : ℕ) (s β₀ : ℝ) (N : ℕ) : 0 ≤ iN d s β₀ N := by
  unfold iN
  split_ifs
  · exact Real.rpow_nonneg (Nat.cast_nonneg _) _
  · exact Real.sqrt_nonneg _

theorem s21p_jN_nonneg {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (β₀ : ℝ) (N : ℕ) (hN : 1 ≤ N) :
    0 ≤ jN d s β₀ N := by
  unfold jN
  split_ifs
  · exact Real.rpow_nonneg (Nat.cast_nonneg _) _
  · exact Real.rpow_nonneg (HRS.MS.S21.s21_deltaN_pos hs0 hsd N hN).le _

theorem S21PrepMain.mono {s a β β₀ T c₁ C₁ εstar C₀ C C₀' C' : ℝ} (hs0 : 0 ≤ s) (hsd : s < d)
    (h : S21PrepMain d s a β β₀ T c₁ C₁ εstar C₀ C) (hC₀ : C₀ ≤ C₀') (hC0 : 0 ≤ C) (hC : C ≤ C') :
    S21PrepMain d s a β β₀ T c₁ C₁ εstar C₀' C' := by
  intro ρβ hρβ ε ψ hadm ρ hres N hN hGEC Ω _ P _ X₀ W X hBr hInd hlaw hstrong Ω' _ P' _ Z hZ a₀ ha₀
  obtain ⟨h1, h2, h3, h4⟩ := h ρβ hρβ ε ψ hadm ρ hres N hN hGEC P X₀ W X hBr hInd hlaw hstrong P' Z hZ a₀ ha₀
  have hδ : 0 ≤ deltaN d s N := (HRS.MS.S21.s21_deltaN_pos hs0 hsd N (by omega)).le
  have hl := s21p_localizationRate_mono (d := d) (s := s) hC₀ N
  have hl0 := s21p_localizationRate_nonneg d s C₀ N
  have hi := s21p_iN_nonneg d s β₀ N
  have hj := s21p_jN_nonneg hs0 hsd β₀ N (by omega)
  have hsq : 0 ≤ Real.sqrt N * deltaN d s N := mul_nonneg (Real.sqrt_nonneg _) hδ
  have hC'0 : 0 ≤ C' := hC0.trans hC
  have hsl : Real.sqrt (localizationRate d s C₀ N) ≤ Real.sqrt (localizationRate d s C₀' N) :=
    Real.sqrt_le_sqrt hl
  refine ⟨h1, h2, h3.trans ?_, h4.trans (ENNReal.ofReal_le_ofReal ?_)⟩
  · have hb : 0 ≤ Real.sqrt N * deltaN d s N + localizationRate d s C₀ N + iN d s β₀ N := by positivity
    have hb' : Real.sqrt N * deltaN d s N + localizationRate d s C₀ N + iN d s β₀ N ≤
        Real.sqrt N * deltaN d s N + localizationRate d s C₀' N + iN d s β₀ N := by linarith
    exact (mul_le_mul_of_nonneg_right hC hb).trans (mul_le_mul_of_nonneg_left hb' hC'0)
  · have hb : 0 ≤ Real.sqrt N * deltaN d s N + Real.sqrt (localizationRate d s C₀ N) +
        jN d s β₀ N := by positivity
    have hb' : Real.sqrt N * deltaN d s N + Real.sqrt (localizationRate d s C₀ N) + jN d s β₀ N ≤
        Real.sqrt N * deltaN d s N + Real.sqrt (localizationRate d s C₀' N) + jN d s β₀ N := by
      linarith
    exact (mul_le_mul_of_nonneg_right hC hb).trans (mul_le_mul_of_nonneg_left hb' hC'0)

/-- The reduction of the frozen statement S2.1 (ii) to `S21PrepMain` at one completion constant. -/
theorem whole_space_prepared_of_main'
    (hmain : ∀ (d : ℕ), 2 ≤ d → ∀ (s : ℝ), 0 ≤ s → s < 2 * (d : ℝ) / 3 → ∀ (a β : ℝ), 0 < a → 0 < β →
      ∀ β₀ : ℝ, 0 ≤ β₀ → ∀ T : ℝ, 0 < T → ∀ c₁ C₁ : ℝ,
      ∃ εstar : ℝ, 0 < εstar ∧ ∃ C₀ C : ℝ, 0 ≤ C ∧ S21PrepMain d s a β β₀ T c₁ C₁ εstar C₀ C) :
    HRS.Whole.WholeSpacePreparedStatement := by
  refine whole_space_prepared_of_main fun d hd s hs0 hs a β ha hβ β₀ hβ₀ T hT c₁ C₁ => ?_
  have hsd : s < d := by
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  obtain ⟨εstar, hε, C₀, C, hC0, h⟩ := hmain d hd s hs0 hs a β ha hβ β₀ hβ₀ T hT c₁ C₁
  exact ⟨εstar, hε, C₀, fun C₀' hC₀' => ⟨C, h.mono hs0 hsd hC₀' hC0 le_rfl⟩⟩

end HRS.Whole
