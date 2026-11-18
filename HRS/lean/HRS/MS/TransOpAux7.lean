import HRS.MS.TransOpAux6

/-!
# S611 packet P1g: translations by a general vector on `Σ^m`

`s611_memOsc_translate`: `m ≥ 1`, `φ ∈ Σ^m ⇒ φ(· + c) ∈ Σ^m`, `‖φ(· + c)‖_{Σ^m} ≤ s611_K m c ‖φ‖_{Σ^m}` with
`s611_K m c = exp(m 3^m ∑_j |c_j|)`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.TransOp

open HRS.Whole
open HRS (Euc)

variable {d : ℕ}

theorem s611_sum_e (c : Euc d) : ∑ j, c j • s611_e j = c := by
  ext k
  simp [s611_e, Pi.single_apply]

/-- The constant of the `Σ^m` bound for the translation by `c`. -/
def s611_K (m : ℕ) (c : Euc d) : ℝ := Real.exp (m * 3 ^ m * ∑ j, |c j|)

theorem s611_K_pos (m : ℕ) (c : Euc d) : 0 < s611_K m c := Real.exp_pos _

theorem s611_one_le_K (m : ℕ) (c : Euc d) : 1 ≤ s611_K m c := by
  unfold s611_K
  rw [Real.one_le_exp_iff]
  positivity

theorem s611_translate_sum_bound (m : ℕ) (hm : 1 ≤ m) (c : Euc d) (S : Finset (Fin d)) :
    ∀ {f : Euc d → ℝ}, MemLp f 2 (volume : Measure (Euc d)) →
      Summable (fun α => s611_w d m α * hermiteCoeff f α ^ 2) →
      Summable (fun α => s611_w d m α *
        hermiteCoeff (fun x => f (x + ∑ j ∈ S, c j • s611_e j)) α ^ 2) ∧
      ∑' α, s611_w d m α * hermiteCoeff (fun x => f (x + ∑ j ∈ S, c j • s611_e j)) α ^ 2 ≤
        Real.exp (2 * m * 3 ^ m * ∑ j ∈ S, |c j|) * ∑' α, s611_w d m α * hermiteCoeff f α ^ 2 := by
  induction S using Finset.induction_on with
  | empty =>
    intro f hf hS
    simp only [Finset.sum_empty, add_zero, mul_zero, Real.exp_zero, one_mul]
    exact ⟨hS, le_rfl⟩
  | insert j S hj ih =>
    intro f hf hS
    obtain ⟨h1, h2⟩ := ih hf hS
    set g : Euc d → ℝ := fun x => f (x + ∑ k ∈ S, c k • s611_e k) with hg
    have hgL : MemLp g 2 (volume : Measure (Euc d)) := s611_memLp_translate hf _
    obtain ⟨h3, h4⟩ := s611_axis_bound m hm j hgL h1 (-c j)
    have e : (fun x => f (x + ∑ k ∈ insert j S, c k • s611_e k)) =
        fun x => g (x - (-c j) • s611_e j) := by
      funext x
      simp only [hg, Finset.sum_insert hj, neg_smul, sub_neg_eq_add]
      congr 1
      abel
    rw [e]
    refine ⟨h3, h4.trans ?_⟩
    rw [Finset.sum_insert hj, abs_neg] at *
    rw [show 2 * (m : ℝ) * 3 ^ m * (|c j| + ∑ k ∈ S, |c k|) =
      2 * m * 3 ^ m * |c j| + 2 * m * 3 ^ m * ∑ k ∈ S, |c k| by ring, Real.exp_add]
    calc Real.exp (2 * m * 3 ^ m * |c j|) * ∑' α, s611_w d m α * hermiteCoeff g α ^ 2
        ≤ Real.exp (2 * m * 3 ^ m * |c j|) * (Real.exp (2 * m * 3 ^ m * ∑ k ∈ S, |c k|) *
          ∑' α, s611_w d m α * hermiteCoeff f α ^ 2) := by gcongr
      _ = _ := by ring

theorem s611_memOsc_translate (m : ℕ) (hm : 1 ≤ m) (c : Euc d) {φ : Euc d → ℝ}
    (hφ : MemOsc (m : ℝ) φ) :
    MemOsc (m : ℝ) (fun x => φ (x + c)) ∧
      oscNorm (m : ℝ) (fun x => φ (x + c)) ≤ s611_K m c * oscNorm (m : ℝ) φ := by
  have hS : Summable (fun α => s611_w d m α * hermiteCoeff φ α ^ 2) := by
    simpa [s611_w, Real.rpow_natCast] using hφ.2
  obtain ⟨h1, h2⟩ := s611_translate_sum_bound m hm c Finset.univ hφ.1 hS
  rw [s611_sum_e c] at h1 h2
  refine ⟨⟨s611_memLp_translate hφ.1 c, ?_⟩, ?_⟩
  · simpa [s611_w, Real.rpow_natCast] using h1
  · unfold oscNorm
    simp only [Real.rpow_natCast]
    have hK2 : Real.exp (2 * m * 3 ^ m * ∑ j, |c j|) = s611_K m c ^ 2 := by
      unfold s611_K
      rw [sq, ← Real.exp_add]
      congr 1; ring
    rw [hK2] at h2
    have h3 : ∑' α, oscEigenvalue d α ^ m * hermiteCoeff (fun x => φ (x + c)) α ^ 2 ≤
        s611_K m c ^ 2 * ∑' α, oscEigenvalue d α ^ m * hermiteCoeff φ α ^ 2 := h2
    calc Real.sqrt (∑' α, oscEigenvalue d α ^ m * hermiteCoeff (fun x => φ (x + c)) α ^ 2)
        ≤ Real.sqrt (s611_K m c ^ 2 * ∑' α, oscEigenvalue d α ^ m * hermiteCoeff φ α ^ 2) :=
          Real.sqrt_le_sqrt h3
      _ = s611_K m c * Real.sqrt (∑' α, oscEigenvalue d α ^ m * hermiteCoeff φ α ^ 2) := by
          rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (s611_K_pos m c).le]

end HRS.MS.TransOp

end
