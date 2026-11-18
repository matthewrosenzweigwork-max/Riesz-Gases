import HRS.MS.SA12X4W1
import HRS.MS.SA12X4W3

/-!
# S.A.12 (SA12X4) W5: the pointwise weighted domination of the cell rate terms

A pure `ℝ≥0∞` lemma: the weighted sum of the cell rate bound
`A9 ∑_{E9} f_{z+k} + κ ∑_{E7} D_{z+k} + A7 ∑_{E7} f_{z+k} + A7 ∑'_{z'} K_{zz'} 𝓜_{z'}`
is at most `κ c₇ ∑ w D + (A9 c₉ + A7 (c₇ + K_w C_K C₁₂)) ∑ w f` (the shifted-sum weight constants `c₇, c₉`, the comparison `w ≤ K_w ω`,
the weighted column bound of `K` and the weighted mass bound).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12X4

open HRS HRS.Whole HRS.Whole.AppendixA

variable {d : ℕ}

theorem sa12x4_weighted_rate_dom (E7 E9 : Finset (Fin d → ℤ)) {c7 c9 : ℝ}
    (h7 : ∀ u : (Fin d → ℤ) → ℝ≥0∞,
      ∑' z, ENNReal.ofReal (jbracket (cellPt d z) ^ (-((d : ℝ) + 3))) * ∑ k ∈ E7, u (z + k) ≤
        ENNReal.ofReal c7 * ∑' z, ENNReal.ofReal (jbracket (cellPt d z) ^ (-((d : ℝ) + 3))) * u z)
    (h9 : ∀ u : (Fin d → ℤ) → ℝ≥0∞,
      ∑' z, ENNReal.ofReal (jbracket (cellPt d z) ^ (-((d : ℝ) + 3))) * ∑ k ∈ E9, u (z + k) ≤
        ENNReal.ofReal c9 * ∑' z, ENNReal.ofReal (jbracket (cellPt d z) ^ (-((d : ℝ) + 3))) * u z)
    (A9 κ A7 Kw CK C12 : ℝ) (hC12 : 0 ≤ C12) (hA9 : 0 ≤ A9) (hκ : 0 ≤ κ) (hA7 : 0 ≤ A7) (hKw : 0 ≤ Kw) (hCK : 0 ≤ CK)
    (hc7 : 0 ≤ c7) (hc9 : 0 ≤ c9)
    (hwt : ∀ z, jbracket (cellPt d z) ^ (-((d : ℝ) + 3)) ≤ Kw * cellWeight d z)
    (fz Dz : (Fin d → ℤ) → ℝ) (hf : ∀ z, 0 ≤ fz z) (hD : ∀ z, 0 ≤ Dz z)
    (mass : (Fin d → ℤ) → ℝ≥0∞) (Kc : (Fin d → ℤ) → (Fin d → ℤ) → ℝ≥0)
    (hcol : ∀ z', ∑' z, ENNReal.ofReal (cellWeight d z) * (Kc z z' : ℝ≥0∞) ≤
      ENNReal.ofReal CK * ENNReal.ofReal (cellWeight d z'))
    (hmass : ∑' z', ENNReal.ofReal (cellWeight d z') * mass z' ≤
      ENNReal.ofReal C12 * ∑' z, ENNReal.ofReal (jbracket (cellPt d z) ^ (-((d : ℝ) + 3))) * ENNReal.ofReal (fz z)) :
    ∑' z, ENNReal.ofReal (jbracket (cellPt d z) ^ (-((d : ℝ) + 3))) *
        (ENNReal.ofReal (A9 * ∑ k ∈ E9, fz (z + k)) + ENNReal.ofReal (κ * ∑ k ∈ E7, Dz (z + k)) +
          ENNReal.ofReal (A7 * ∑ k ∈ E7, fz (z + k)) + ENNReal.ofReal A7 * ∑' z', (Kc z z' : ℝ≥0∞) * mass z') ≤
      ENNReal.ofReal (κ * c7) * ∑' z, ENNReal.ofReal (jbracket (cellPt d z) ^ (-((d : ℝ) + 3))) * ENNReal.ofReal (Dz z) +
        ENNReal.ofReal (A9 * c9 + A7 * (c7 + Kw * CK * C12)) *
          ∑' z, ENNReal.ofReal (jbracket (cellPt d z) ^ (-((d : ℝ) + 3))) * ENNReal.ofReal (fz z) := by
  classical
  set wt : (Fin d → ℤ) → ℝ≥0∞ := fun z => ENNReal.ofReal (jbracket (cellPt d z) ^ (-((d : ℝ) + 3))) with hwtdef
  set Sf : ℝ≥0∞ := ∑' z, wt z * ENNReal.ofReal (fz z) with hSf
  set SD : ℝ≥0∞ := ∑' z, wt z * ENNReal.ofReal (Dz z) with hSD
  have hnn : ∀ (u : (Fin d → ℤ) → ℝ), (∀ z, 0 ≤ u z) → ∀ (E : Finset (Fin d → ℤ)) z,
      ENNReal.ofReal (∑ k ∈ E, u (z + k)) = ∑ k ∈ E, ENNReal.ofReal (u (z + k)) :=
    fun u hu E z => ENNReal.ofReal_sum_of_nonneg fun k _ => hu _
  -- the four pieces
  have p1 : ∑' z, wt z * ENNReal.ofReal (A9 * ∑ k ∈ E9, fz (z + k)) ≤ ENNReal.ofReal (A9 * c9) * Sf := by
    calc ∑' z, wt z * ENNReal.ofReal (A9 * ∑ k ∈ E9, fz (z + k))
        = ENNReal.ofReal A9 * ∑' z, wt z * ∑ k ∈ E9, ENNReal.ofReal (fz (z + k)) := by
          rw [← ENNReal.tsum_mul_left]
          refine tsum_congr fun z => ?_
          rw [ENNReal.ofReal_mul hA9, hnn fz hf E9 z]; ring
      _ ≤ ENNReal.ofReal A9 * (ENNReal.ofReal c9 * Sf) := by
          gcongr
          exact h9 (fun z => ENNReal.ofReal (fz z))
      _ = ENNReal.ofReal (A9 * c9) * Sf := by rw [ENNReal.ofReal_mul hA9, mul_assoc]
  have p2 : ∑' z, wt z * ENNReal.ofReal (κ * ∑ k ∈ E7, Dz (z + k)) ≤ ENNReal.ofReal (κ * c7) * SD := by
    calc ∑' z, wt z * ENNReal.ofReal (κ * ∑ k ∈ E7, Dz (z + k))
        = ENNReal.ofReal κ * ∑' z, wt z * ∑ k ∈ E7, ENNReal.ofReal (Dz (z + k)) := by
          rw [← ENNReal.tsum_mul_left]
          refine tsum_congr fun z => ?_
          rw [ENNReal.ofReal_mul hκ, hnn Dz hD E7 z]; ring
      _ ≤ ENNReal.ofReal κ * (ENNReal.ofReal c7 * SD) := by
          gcongr
          exact h7 (fun z => ENNReal.ofReal (Dz z))
      _ = ENNReal.ofReal (κ * c7) * SD := by rw [ENNReal.ofReal_mul hκ, mul_assoc]
  have p3 : ∑' z, wt z * ENNReal.ofReal (A7 * ∑ k ∈ E7, fz (z + k)) ≤ ENNReal.ofReal (A7 * c7) * Sf := by
    calc ∑' z, wt z * ENNReal.ofReal (A7 * ∑ k ∈ E7, fz (z + k))
        = ENNReal.ofReal A7 * ∑' z, wt z * ∑ k ∈ E7, ENNReal.ofReal (fz (z + k)) := by
          rw [← ENNReal.tsum_mul_left]
          refine tsum_congr fun z => ?_
          rw [ENNReal.ofReal_mul hA7, hnn fz hf E7 z]; ring
      _ ≤ ENNReal.ofReal A7 * (ENNReal.ofReal c7 * Sf) := by
          gcongr
          exact h7 (fun z => ENNReal.ofReal (fz z))
      _ = ENNReal.ofReal (A7 * c7) * Sf := by rw [ENNReal.ofReal_mul hA7, mul_assoc]
  have p4 : ∑' z, wt z * (ENNReal.ofReal A7 * ∑' z', (Kc z z' : ℝ≥0∞) * mass z') ≤
      ENNReal.ofReal (A7 * (Kw * CK * C12)) * Sf := by
    have hcol' : ∀ z', ∑' z, wt z * (Kc z z' : ℝ≥0∞) ≤ ENNReal.ofReal (Kw * CK) * ENNReal.ofReal (cellWeight d z') := by
      intro z'
      calc ∑' z, wt z * (Kc z z' : ℝ≥0∞) ≤ ∑' z, ENNReal.ofReal Kw * (ENNReal.ofReal (cellWeight d z) * (Kc z z' : ℝ≥0∞)) :=
            ENNReal.tsum_le_tsum fun z => by
              rw [← mul_assoc, ← ENNReal.ofReal_mul hKw]
              gcongr
              exact ENNReal.ofReal_le_ofReal (hwt z)
        _ = ENNReal.ofReal Kw * ∑' z, ENNReal.ofReal (cellWeight d z) * (Kc z z' : ℝ≥0∞) := ENNReal.tsum_mul_left
        _ ≤ ENNReal.ofReal Kw * (ENNReal.ofReal CK * ENNReal.ofReal (cellWeight d z')) := by gcongr; exact hcol z'
        _ = ENNReal.ofReal (Kw * CK) * ENNReal.ofReal (cellWeight d z') := by rw [ENNReal.ofReal_mul hKw, mul_assoc]
    calc ∑' z, wt z * (ENNReal.ofReal A7 * ∑' z', (Kc z z' : ℝ≥0∞) * mass z')
        = ENNReal.ofReal A7 * ∑' z, ∑' z', wt z * (Kc z z' : ℝ≥0∞) * mass z' := by
          rw [← ENNReal.tsum_mul_left]
          refine tsum_congr fun z => ?_
          rw [mul_left_comm, ← ENNReal.tsum_mul_left]
          congr 1
          exact tsum_congr fun z' => (mul_assoc _ _ _).symm
      _ = ENNReal.ofReal A7 * ∑' z', (∑' z, wt z * (Kc z z' : ℝ≥0∞)) * mass z' := by
          rw [ENNReal.tsum_comm]
          congr 1
          refine tsum_congr fun z' => ?_
          rw [← ENNReal.tsum_mul_right]
      _ ≤ ENNReal.ofReal A7 * ∑' z', ENNReal.ofReal (Kw * CK) * (ENNReal.ofReal (cellWeight d z') * mass z') := by
          gcongr ENNReal.ofReal A7 * ?_
          refine ENNReal.tsum_le_tsum fun z' => ?_
          rw [← mul_assoc]
          gcongr ?_ * mass z'
          exact hcol' z'
      _ = ENNReal.ofReal A7 * (ENNReal.ofReal (Kw * CK) * ∑' z', ENNReal.ofReal (cellWeight d z') * mass z') := by
          rw [ENNReal.tsum_mul_left]
      _ ≤ ENNReal.ofReal A7 * (ENNReal.ofReal (Kw * CK) * (ENNReal.ofReal C12 * Sf)) := by
          gcongr
      _ = ENNReal.ofReal (A7 * (Kw * CK * C12)) * Sf := by
          rw [ENNReal.ofReal_mul hA7, ENNReal.ofReal_mul (mul_nonneg hKw hCK), ENNReal.ofReal_mul hKw] 
          ring
  -- assemble
  have hsum4 : ∑' z, wt z * (ENNReal.ofReal (A9 * ∑ k ∈ E9, fz (z + k)) + ENNReal.ofReal (κ * ∑ k ∈ E7, Dz (z + k)) +
          ENNReal.ofReal (A7 * ∑ k ∈ E7, fz (z + k)) + ENNReal.ofReal A7 * ∑' z', (Kc z z' : ℝ≥0∞) * mass z') =
      ∑' z, wt z * ENNReal.ofReal (A9 * ∑ k ∈ E9, fz (z + k)) + ∑' z, wt z * ENNReal.ofReal (κ * ∑ k ∈ E7, Dz (z + k)) +
        ∑' z, wt z * ENNReal.ofReal (A7 * ∑ k ∈ E7, fz (z + k)) +
          ∑' z, wt z * (ENNReal.ofReal A7 * ∑' z', (Kc z z' : ℝ≥0∞) * mass z') := by
    simp only [mul_add]
    rw [ENNReal.tsum_add, ENNReal.tsum_add, ENNReal.tsum_add]
  rw [hsum4]
  calc _ ≤ ENNReal.ofReal (A9 * c9) * Sf + ENNReal.ofReal (κ * c7) * SD + ENNReal.ofReal (A7 * c7) * Sf +
        ENNReal.ofReal (A7 * (Kw * CK * C12)) * Sf := by gcongr
    _ = ENNReal.ofReal (κ * c7) * SD + ENNReal.ofReal (A9 * c9 + A7 * (c7 + Kw * CK * C12)) * Sf := by
        have hx : ENNReal.ofReal (A9 * c9 + A7 * (c7 + Kw * CK * C12)) =
            ENNReal.ofReal (A9 * c9) + ENNReal.ofReal (A7 * c7) + ENNReal.ofReal (A7 * (Kw * CK * C12)) := by
          rw [← ENNReal.ofReal_add (mul_nonneg hA9 hc9) (mul_nonneg hA7 hc7),
            ← ENNReal.ofReal_add (add_nonneg (mul_nonneg hA9 hc9) (mul_nonneg hA7 hc7))
              (mul_nonneg hA7 (mul_nonneg (mul_nonneg hKw hCK) hC12))]
          congr 1; ring
        rw [hx]; ring

end HRS.MH.AdjointRd.Phase2SA12X4
