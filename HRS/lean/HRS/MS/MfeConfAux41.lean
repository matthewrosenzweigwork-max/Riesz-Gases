import HRS.MS.MfeConfAux40

/-!
# S.B.1, packet F6 (part 3): the fixed-time cut-off inequality with a tilted reference

`sb1_pointwise`: the pointwise bound `-∑_k χ A_k J_k ≤ χ u ∑_k w_k A_k + N Kl² Q/(4θ)` (Young with `δ = 1`);
`sb1_fixed_time`: the integrated inequality.
-/

open MeasureTheory Filter Topology
open HRS HRS.Whole HRS.MP.SelfSimP4 HRS.MP.SelfSimP4Mol
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MS.MfeConf

variable {d N : ℕ}

section
variable {v : ℝ} {ν : Measure (EucConfig d N)}

theorem sb1_pointwise [IsProbabilityMeasure ν] (hv : 0 < v) (hm : Integrable p4m_q ν) {θ : ℝ} (hθ : 0 < θ)
    {b w : EucConfig d N → EucConfig d N} {Kl : ℝ≥0} (hbl : LipschitzWith Kl b) {B K : ℝ} (hB : 0 ≤ B)
    (hK : 0 ≤ K) (hbg : ∀ y, ‖b y‖ ≤ B + K * ‖y‖) (x : EucConfig d N) {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    -∑ k : Fin N × Fin d, c * (p4m_ell v θ ν b k x + w x k.1 k.2 / θ) *
        (θ * p4m_gu v ν k x - p4m_B v ν b k x) ≤
      c * (p4Mol v ν x * ∑ k : Fin N × Fin d, w x k.1 k.2 * (p4m_ell v θ ν b k x + w x k.1 k.2 / θ)) +
        N * (Kl : ℝ) ^ 2 * p4m_Q v ν x / (4 * θ) := by
  set A : Fin N × Fin d → ℝ := fun k => p4m_ell v θ ν b k x + w x k.1 k.2 / θ with hA
  set u := p4Mol v ν x with hu
  have hupos : 0 < u := p4m_mol_pos hv hm x
  have hcomm : ∀ k : Fin N × Fin d, c * A k * (θ * p4m_gu v ν k x - p4m_B v ν b k x) =
      c * (θ * u) * A k ^ 2 - c * u * (w x k.1 k.2 * A k) -
        c * ((p4m_B v ν b k x - u * b x k.1 k.2) * A k) := by
    intro k
    rw [p4m_J_eq hv hm hθ b k x]
    simp only [hA]
    field_simp
    ring
  have hsum : ∑ k : Fin N × Fin d, c * A k * (θ * p4m_gu v ν k x - p4m_B v ν b k x) =
      c * (θ * u) * ∑ k, A k ^ 2 - c * u * ∑ k, w x k.1 k.2 * A k -
        c * ∑ k, (p4m_B v ν b k x - u * b x k.1 k.2) * A k := by
    simp_rw [hcomm]
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
  have hy := sb1_young_gen hv hm hθ one_pos hbl hB hK hbg A x
  simp only [mul_one] at hy
  have hT := p4m_T_le_Q hv hm hbl hB hK hbg x
  have hT0 := p4m_T_nonneg v hv ν b x
  have hp4 : 0 < 4 * θ := by positivity
  have a1 := mul_le_mul_of_nonneg_left (sub_nonpos.2 hy) hc0
  have a2 : c * (p4m_T v ν b x / (4 * θ)) ≤ p4m_T v ν b x / (4 * θ) :=
    mul_le_of_le_one_left (div_nonneg hT0 hp4.le) hc1
  have a3 : p4m_T v ν b x / (4 * θ) ≤ N * (Kl : ℝ) ^ 2 * p4m_Q v ν x / (4 * θ) :=
    div_le_div_of_nonneg_right hT hp4.le
  rw [hsum]
  have e : c * (u * ∑ k, w x k.1 k.2 * A k) = c * u * ∑ k, w x k.1 k.2 * A k := by ring
  rw [e]
  nlinarith [a1, a2, a3]

end

end HRS.MS.MfeConf
