import HRS.Main.A9Aux12

/-!
# Packet A9, part 13: the field comparison for one test function `Φ`, one finite set of modes, fixed `N`
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators MeasureTheory

namespace HRS.Main.A9

local notation "ℝ^" p => EuclideanSpace ℝ (Fin p)

open HRS HRS.A33 HRS.PDE HRS.Main.A8P HRS.GF HRS.Uniform

variable {d : ℕ}

section Core

variable {S : MainData d} {R : ∀ N, Realization d N} {Rg : PDE.Regime} {ν₀ MB Λ VB C₀ Cc : ℝ}
  {𝔈 : ℕ → ℝ} {Ca Λ₁ C₀' Cq Cp cT : ℝ}

/-- The coordinate bound of the `Q`-term: `E|Q_j| ≤ bQ j`. -/
def a9bQ (S : MainData d) (N : ℕ) (Ca Cq cT Λ₁ t : ℝ) (𝔈N : ℝ) {q : ℕ} (k : Fin q → NonzeroLattice d)
    (j : NonzeroLattice d) : ℝ :=
  open Classical in
  if j ∈ Set.range k then
    S.sigma N * ((1 / 2) * (Cq * (cT * a9K d Λ₁ t j))) * (S.T * 𝔈N)
  else
    Real.sqrt (S.T * (2 * (S.sigma N ^ 2 * S.invβ N / N) * (d * (Ca * a9K d Λ₁ t j)) ^ 2)) +
      S.sigma N * ((1 / 2) * (Cq * (cT * a9K d Λ₁ t j))) * (S.T * 𝔈N)

/-- The coordinate bound of the Gaussian tail. -/
def a9bG (S : MainData d) (N : ℕ) (Ca Λ₁ t : ℝ) {q : ℕ} (k : Fin q → NonzeroLattice d)
    (j : NonzeroLattice d) : ℝ :=
  open Classical in
  if j ∈ Set.range k then 0 else
    Real.sqrt (2 * S.qN N * t * (d * (Ca * a9K d Λ₁ t j)) ^ 2)

theorem a9bQ_nonneg (hCa : 0 ≤ Ca) (hCq : 0 ≤ Cq) (hcT : 0 ≤ cT) {N : ℕ} (hN : 1 ≤ N) {t 𝔈N : ℝ}
    (h𝔈 : 0 ≤ 𝔈N) {q : ℕ} (k : Fin q → NonzeroLattice d) (j : NonzeroLattice d) :
    0 ≤ a9bQ S N Ca Cq cT Λ₁ t 𝔈N k j := by
  have hσ := a8p_sigma_nonneg S N
  have hK := a9K_nonneg (d := d) Λ₁ t j
  have hT := S.hT.le
  have h1 : 0 ≤ S.sigma N * ((1 / 2) * (Cq * (cT * a9K d Λ₁ t j))) * (S.T * 𝔈N) := by positivity
  unfold a9bQ
  split_ifs
  · exact h1
  · exact add_nonneg (Real.sqrt_nonneg _) h1

theorem a9bQ_summable (hCa : 0 ≤ Ca) (hCq : 0 ≤ Cq) (hcT : 0 ≤ cT) {N : ℕ} (hN : 1 ≤ N) {t 𝔈N : ℝ}
    (h𝔈 : 0 ≤ 𝔈N) {q : ℕ} (k : Fin q → NonzeroLattice d) :
    Summable (a9bQ S N Ca Cq cT Λ₁ t 𝔈N k) := by
  have hσ := a8p_sigma_nonneg S N
  have hT := S.hT.le
  have hq0 : 0 ≤ S.sigma N ^ 2 * S.invβ N / N := by
    have := S.hinvβ N
    positivity
  have hCd : 0 ≤ (d : ℝ) * Ca := mul_nonneg (Nat.cast_nonneg d) hCa
  set c : ℝ := Real.sqrt (S.T * (2 * (S.sigma N ^ 2 * S.invβ N / N))) * ((d : ℝ) * Ca) +
    S.sigma N * ((1 / 2) * (Cq * cT)) * (S.T * 𝔈N) with hc
  have hsum := (a9K_summable (d := d) Λ₁ t).mul_left c
  refine Summable.of_nonneg_of_le (fun j => a9bQ_nonneg hCa hCq hcT hN h𝔈 k j) (fun j => ?_) hsum
  have hK := a9K_nonneg (d := d) Λ₁ t j
  have e1 : Real.sqrt (S.T * (2 * (S.sigma N ^ 2 * S.invβ N / N) * (d * (Ca * a9K d Λ₁ t j)) ^ 2)) =
      Real.sqrt (S.T * (2 * (S.sigma N ^ 2 * S.invβ N / N))) * (((d : ℝ) * Ca) * a9K d Λ₁ t j) := by
    have : S.T * (2 * (S.sigma N ^ 2 * S.invβ N / N) * (d * (Ca * a9K d Λ₁ t j)) ^ 2) =
        (S.T * (2 * (S.sigma N ^ 2 * S.invβ N / N))) * (((d : ℝ) * Ca) * a9K d Λ₁ t j) ^ 2 := by ring
    rw [this, a9_sqrt_form (by positivity) hK hCd]
  have hr0 : 0 ≤ S.sigma N * ((1 / 2) * (Cq * (cT * a9K d Λ₁ t j))) * (S.T * 𝔈N) := by positivity
  unfold a9bQ
  split_ifs
  · have : S.sigma N * ((1 / 2) * (Cq * (cT * a9K d Λ₁ t j))) * (S.T * 𝔈N) =
        S.sigma N * ((1 / 2) * (Cq * cT)) * (S.T * 𝔈N) * a9K d Λ₁ t j := by ring
    rw [this, hc]
    have h2 : 0 ≤ Real.sqrt (S.T * (2 * (S.sigma N ^ 2 * S.invβ N / N))) * ((d : ℝ) * Ca) :=
      mul_nonneg (Real.sqrt_nonneg _) hCd
    nlinarith [mul_nonneg h2 hK]
  · rw [e1]
    have : S.sigma N * ((1 / 2) * (Cq * (cT * a9K d Λ₁ t j))) * (S.T * 𝔈N) =
        S.sigma N * ((1 / 2) * (Cq * cT)) * (S.T * 𝔈N) * a9K d Λ₁ t j := by ring
    rw [this, hc]
    nlinarith

end Core

end HRS.Main.A9
