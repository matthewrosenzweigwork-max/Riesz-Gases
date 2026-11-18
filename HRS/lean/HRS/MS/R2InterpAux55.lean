import HRS.MS.R2InterpAux54
import HRS.MC.S7PIHC12

/-!
# S10.2 (worker S102), part 55 (packet F6, heat part): the `C^{1,2}` extension of the heat function of the grid on a piece without observation times
-/

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators MatrixOrder Matrix

namespace HRS.MS.R2Interp

open HRS HRS.Whole HRS.MS.CovMeas HRS.MC.Sec7.PI

variable {d : ℕ} {C : WholeCoeff d} {m T : ℝ} {r : ℕ} {c : MultiIndex d → ℝ}

/-- The rate on a piece `[a,b]` without observation times in `(a,b)`: the observations with `t_k < b` are frozen. -/
def s102_Ar (C : WholeCoeff d) (m : ℝ) {T : ℝ} (hT : 0 < T) (L : ℕ) (b v : ℝ) :
    Matrix (Fin (s102_q d L)) (Fin (s102_q d L)) ℝ :=
  Matrix.of fun k k' => 2 * C.ν * (if b ≤ min (s102_tk hT L k) (s102_tk hT L k') then s102_gram C m hT L v k k' else 0)

theorem s102_Ar_eq_rate (hT : 0 < T) (L : ℕ) {a b v : ℝ} (hv : v ∈ Ioc a b)
    (hno : ∀ k : Fin (s102_q d L), ¬ (a < s102_tk hT L k ∧ s102_tk hT L k < b)) :
    s102_Ar C m hT L b v = s102_rateM C m hT L v := by
  ext k k'
  simp only [s102_Ar, s102_rateM, Matrix.of_apply]
  congr 1
  by_cases h : b ≤ min (s102_tk hT L k) (s102_tk hT L k')
  · rw [if_pos h, if_pos (hv.2.trans h)]
  · rw [if_neg h]
    rw [if_neg]
    intro hle
    apply h
    apply le_min
    · by_contra h1
      push Not at h1
      have h2 := hno k
      have : s102_tk hT L k ≤ a := by
        by_contra h3
        push Not at h3
        exact h2 ⟨h3, h1⟩
      linarith [hv.1, hle.trans (min_le_left _ _)]
    · by_contra h1
      push Not at h1
      have h2 := hno k'
      have : s102_tk hT L k' ≤ a := by
        by_contra h3
        push Not at h3
        exact h2 ⟨h3, h1⟩
      linarith [hv.1, hle.trans (min_le_right _ _)]

theorem s102_Ar_psd (hs : S102Std C m T r c) (hT : 0 < T) (L : ℕ) {a b v : ℝ} (hv : v ∈ Icc a b) (ha : 0 ≤ a)
    (hb : b ≤ T) : (s102_Ar C m hT L b v).PosSemidef := by
  have hvT : v ∈ Icc (0 : ℝ) T := ⟨ha.trans hv.1, hv.2.trans hb⟩
  have hR := s102_rateM_psd hs.hD hT L hvT (by rw [hs.hstat v]; exact hs.hint) (fun x => by rw [hs.hstat v]; exact hs.hnn x) hs.hν
  set D : Matrix (Fin (s102_q d L)) (Fin (s102_q d L)) ℝ :=
    Matrix.diagonal fun k => if b ≤ s102_tk hT L k then (1 : ℝ) else 0 with hD
  have hDH : Dᴴ = D := by
    rw [hD, Matrix.diagonal_conjTranspose]; ext i j; simp [Matrix.diagonal]
  have := hR.conjTranspose_mul_mul_same D
  rw [hDH] at this
  convert this using 1
  ext k k'
  simp only [s102_Ar, s102_rateM, hD, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.of_apply]
  by_cases h1 : b ≤ s102_tk hT L k <;> by_cases h2 : b ≤ s102_tk hT L k'
  · have hm : b ≤ min (s102_tk hT L k) (s102_tk hT L k') := le_min h1 h2
    rw [if_pos hm, if_pos (hv.2.trans hm)]
    simp [h1, h2]
  · have hm : ¬ b ≤ min (s102_tk hT L k) (s102_tk hT L k') := fun h => h2 (h.trans (min_le_right _ _))
    simp [h1, h2, hm]
  · have hm : ¬ b ≤ min (s102_tk hT L k) (s102_tk hT L k') := fun h => h1 (h.trans (min_le_left _ _))
    simp [h1, h2, hm]
  · have hm : ¬ b ≤ min (s102_tk hT L k) (s102_tk hT L k') := fun h => h1 (h.trans (min_le_left _ _))
    simp [h1, h2, hm]

end HRS.MS.R2Interp

end
