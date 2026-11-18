import HRS.Main.A9Aux15

/-!
# Packet A9, part 16: the explicit bound of the core estimate (sums over modes)
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators MeasureTheory

namespace HRS.Main.A9

local notation "ℝ^" p => EuclideanSpace ℝ (Fin p)

open HRS HRS.A33 HRS.PDE HRS.Main.A8P HRS.GF HRS.Uniform

variable {d : ℕ}

/-- The tail of the mode sum outside `range k`. -/
def a9tail (d : ℕ) (Λ₁ t : ℝ) {q : ℕ} (k : Fin q → NonzeroLattice d) : ℝ :=
  open Classical in ∑' j, if j ∈ Set.range k then 0 else a9K d Λ₁ t j

theorem a9tail_nonneg (Λ₁ t : ℝ) {q : ℕ} (k : Fin q → NonzeroLattice d) : 0 ≤ a9tail d Λ₁ t k := by
  classical
  unfold a9tail
  exact tsum_nonneg fun j => by split_ifs <;> simp [a9K_nonneg]

theorem a9tail_summable (Λ₁ t : ℝ) {q : ℕ} (k : Fin q → NonzeroLattice d) :
    Summable fun j => (open Classical in if j ∈ Set.range k then 0 else a9K d Λ₁ t j) := by
  classical
  refine Summable.of_nonneg_of_le (fun j => by split_ifs <;> simp [a9K_nonneg])
    (fun j => by split_ifs <;> simp [a9K_nonneg]) (a9K_summable (d := d) Λ₁ t)

section Arith

variable {S : MainData d} {Ca Cq cT Λ₁ : ℝ}

theorem a9bQ_tsum (hCq : 0 ≤ Cq) (hcT : 0 ≤ cT) (hCa : 0 ≤ Ca) {N : ℕ} (hN : 1 ≤ N) {t 𝔈N : ℝ}
    (h𝔈 : 0 ≤ 𝔈N) {q : ℕ} (k : Fin q → NonzeroLattice d) :
    ∑' j, a9bQ S N Ca Cq cT Λ₁ t 𝔈N k j =
      S.sigma N * ((1 / 2) * (Cq * cT)) * (S.T * 𝔈N) * ∑' j, a9K d Λ₁ t j +
        Real.sqrt (S.T * (2 * (S.sigma N ^ 2 * S.invβ N / N))) * ((d : ℝ) * Ca) *
          a9tail d Λ₁ t k := by
  classical
  have hT := S.hT.le
  have hq0 : 0 ≤ S.sigma N ^ 2 * S.invβ N / N := by
    have := S.hinvβ N
    positivity
  have hCd : 0 ≤ (d : ℝ) * Ca := mul_nonneg (Nat.cast_nonneg d) hCa
  have hpt : ∀ j, a9bQ S N Ca Cq cT Λ₁ t 𝔈N k j =
      S.sigma N * ((1 / 2) * (Cq * cT)) * (S.T * 𝔈N) * a9K d Λ₁ t j +
        Real.sqrt (S.T * (2 * (S.sigma N ^ 2 * S.invβ N / N))) * ((d : ℝ) * Ca) *
          (if j ∈ Set.range k then 0 else a9K d Λ₁ t j) := by
    intro j
    have hK := a9K_nonneg (d := d) Λ₁ t j
    unfold a9bQ
    split_ifs with hj
    · ring
    · have : S.T * (2 * (S.sigma N ^ 2 * S.invβ N / N) * (d * (Ca * a9K d Λ₁ t j)) ^ 2) =
          (S.T * (2 * (S.sigma N ^ 2 * S.invβ N / N))) * (((d : ℝ) * Ca) * a9K d Λ₁ t j) ^ 2 := by
        ring
      rw [this, a9_sqrt_form (by positivity) hK hCd]
      ring
  simp_rw [hpt]
  rw [Summable.tsum_add ((a9K_summable (d := d) Λ₁ t).mul_left _)
    ((a9tail_summable Λ₁ t k).mul_left _), tsum_mul_left, tsum_mul_left]
  rfl

theorem a9bG_tsum (hCa : 0 ≤ Ca) {N : ℕ} {t : ℝ} {q : ℕ} (k : Fin q → NonzeroLattice d) :
    ∑' j, a9bG S N Ca Λ₁ t k j =
      Real.sqrt (2 * S.qN N * t) * ((d : ℝ) * Ca) * a9tail d Λ₁ t k := by
  classical
  by_cases hq : 0 ≤ 2 * S.qN N * t
  · have hCd : 0 ≤ (d : ℝ) * Ca := mul_nonneg (Nat.cast_nonneg d) hCa
    have hpt : ∀ j, a9bG S N Ca Λ₁ t k j = Real.sqrt (2 * S.qN N * t) * ((d : ℝ) * Ca) *
        (if j ∈ Set.range k then 0 else a9K d Λ₁ t j) := by
      intro j
      have hK := a9K_nonneg (d := d) Λ₁ t j
      unfold a9bG
      split_ifs with hj
      · ring
      · have e : (d : ℝ) * (Ca * a9K d Λ₁ t j) = ((d : ℝ) * Ca) * a9K d Λ₁ t j := by ring
        rw [e, a9_sqrt_form hq hK hCd]
        ring
    simp_rw [hpt]
    rw [tsum_mul_left]
    rfl
  · -- negative radicand: `Real.sqrt = 0`
    have h0 : Real.sqrt (2 * S.qN N * t) = 0 := Real.sqrt_eq_zero_of_nonpos (not_le.1 hq).le
    have hpt : ∀ j, a9bG S N Ca Λ₁ t k j = 0 := by
      intro j
      unfold a9bG
      split_ifs with hj
      · rfl
      · have : 2 * S.qN N * t * (d * (Ca * a9K d Λ₁ t j)) ^ 2 ≤ 0 := by
          have : 2 * S.qN N * t ≤ 0 := (not_le.1 hq).le
          nlinarith [sq_nonneg ((d : ℝ) * (Ca * a9K d Λ₁ t j))]
        exact Real.sqrt_eq_zero_of_nonpos this
    simp_rw [hpt]
    simp [h0]

end Arith

end HRS.Main.A9
