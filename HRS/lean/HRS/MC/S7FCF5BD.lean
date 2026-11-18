import HRS.MC.S7FCF5Defs

/-!
# Block D of the F5 packet: summability and the weighted Jensen inequality (proofs of `fcf5_D1a_summable`,
`fcf5_D1_weighted_sum`)

Route: `D1a` is the lattice sum `Torus.summable_jp_rpow`.  `D1` is a weighted Jensen inequality for `ENNReal`
tsums, `(∑' w z)^p ≤ (∑' w)^(p-1) ∑' w z^p` for `p ≥ 1`, proved from the finite Hölder inequality
`ENNReal.inner_le_Lp_mul_Lq` by taking the supremum over finite sets; `D1` is this with `w_k = ⟨k⟩^{4-2r}`,
`z_k = ⟨k⟩^{-4} S_k²`, `p = q/2`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7FCF5B

open HRS HRS.Sec7 HRS.MC.Sec7 HRS.MC.SEdge HRS.MC.QRSpec HRS.MC.Sec7.FCPlan HRS.MC.Sec7.FCF5Plan

variable {d : ℕ}

/-- Finite weighted Jensen (power-mean form) in `ℝ≥0∞`: `(∑ w z)^p ≤ (∑ w)^(p-1) ∑ w z^p` for `p > 1`. -/
lemma S7FCF5B_holder_finset {ι : Type*} (s : Finset ι) (w z : ι → ℝ≥0∞) {p : ℝ} (hp : 1 < p) :
    (∑ i ∈ s, w i * z i) ^ p ≤ (∑ i ∈ s, w i) ^ (p - 1) * ∑ i ∈ s, w i * z i ^ p := by
  have hp0 : (0 : ℝ) < p := by linarith
  have hpq : p.HolderConjugate (Real.conjExponent p) := Real.HolderConjugate.conjExponent hp
  have ha0 : 0 < Real.conjExponent p := hpq.symm.pos
  have hsum : p⁻¹ + (Real.conjExponent p)⁻¹ = 1 := hpq.inv_add_inv_eq_one
  have hp1 : p - 1 ≠ 0 := (sub_pos.2 hp).ne'
  have e4 : 1 / Real.conjExponent p * p = p - 1 := by
    unfold Real.conjExponent
    field_simp
  have e5 : p⁻¹ * p = 1 := inv_mul_cancel₀ hp0.ne'
  have e6 : 1 / p * p = 1 := by rw [one_div]; exact e5
  have H := ENNReal.inner_le_Lp_mul_Lq s (fun i => w i ^ (Real.conjExponent p)⁻¹)
    (fun i => w i ^ p⁻¹ * z i) hpq.symm
  have e1 : ∀ i, w i ^ (Real.conjExponent p)⁻¹ * (w i ^ p⁻¹ * z i) = w i * z i := by
    intro i
    rw [← mul_assoc, ← ENNReal.rpow_add_of_nonneg ((Real.conjExponent p)⁻¹) p⁻¹ (inv_nonneg.2 ha0.le) (inv_nonneg.2 hp0.le),
      add_comm, hsum, ENNReal.rpow_one]
  have e2 : ∀ i, (w i ^ (Real.conjExponent p)⁻¹) ^ Real.conjExponent p = w i := by
    intro i
    rw [← ENNReal.rpow_mul, inv_mul_cancel₀ ha0.ne', ENNReal.rpow_one]
  have e3 : ∀ i, (w i ^ p⁻¹ * z i) ^ p = w i * z i ^ p := by
    intro i
    rw [ENNReal.mul_rpow_of_nonneg _ _ hp0.le, ← ENNReal.rpow_mul, e5, ENNReal.rpow_one]
  simp only [e1, e2, e3] at H
  have H2 := ENNReal.rpow_le_rpow H hp0.le
  rw [ENNReal.mul_rpow_of_nonneg _ _ hp0.le, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul, e4, e6,
    ENNReal.rpow_one] at H2
  exact H2

/-- Weighted Jensen for `ENNReal` tsums: `(∑' w z)^p ≤ (∑' w)^(p-1) ∑' w z^p` for `p ≥ 1`. -/
lemma S7FCF5B_jensen_tsum {ι : Type*} (w z : ι → ℝ≥0∞) {p : ℝ} (hp : 1 ≤ p) :
    (∑' i, w i * z i) ^ p ≤ (∑' i, w i) ^ (p - 1) * ∑' i, w i * z i ^ p := by
  rcases eq_or_lt_of_le hp with h1 | h1
  · subst h1
    simp
  · have hp0 : (0 : ℝ) < p := by linarith
    have hfin : ∀ s : Finset ι, ∑ i ∈ s, w i * z i ≤
        ((∑' i, w i) ^ (p - 1) * ∑' i, w i * z i ^ p) ^ p⁻¹ := by
      intro s
      have hh := S7FCF5B_holder_finset s w z h1
      have hw : ∑ i ∈ s, w i ≤ ∑' i, w i := ENNReal.sum_le_tsum s
      have hz : ∑ i ∈ s, w i * z i ^ p ≤ ∑' i, w i * z i ^ p := ENNReal.sum_le_tsum s
      have hpow : (∑ i ∈ s, w i * z i) ^ p ≤ (∑' i, w i) ^ (p - 1) * ∑' i, w i * z i ^ p :=
        hh.trans (mul_le_mul' (ENNReal.rpow_le_rpow hw (by linarith)) hz)
      apply (ENNReal.rpow_le_rpow_iff hp0).mp
      rw [← ENNReal.rpow_mul, inv_mul_cancel₀ hp0.ne', ENNReal.rpow_one]
      exact hpow
    have hsup : ∑' i, w i * z i = ⨆ s : Finset ι, ∑ i ∈ s, w i * z i := ENNReal.tsum_eq_iSup_sum
    rw [hsup]
    calc (⨆ s : Finset ι, ∑ i ∈ s, w i * z i) ^ p
        ≤ (((∑' i, w i) ^ (p - 1) * ∑' i, w i * z i ^ p) ^ p⁻¹) ^ p :=
          ENNReal.rpow_le_rpow (iSup_le hfin) hp0.le
      _ = (∑' i, w i) ^ (p - 1) * ∑' i, w i * z i ^ p := by
          rw [← ENNReal.rpow_mul, inv_mul_cancel₀ hp0.ne', ENNReal.rpow_one]

/-- **D1a (summability)**, proof. -/
theorem fcf5_D1a_summable_proof (r : ℝ) (hr : r = 2 * (d : ℝ) + 6) :
    Summable fun k : NonzeroLattice d => Lattice.jp k.1 ^ (4 - 2 * r) := by
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have h := HRS.summable_jp_rpow (d := d) (r - 2) (by rw [hr]; linarith)
  refine h.congr fun k => ?_
  congr 1
  rw [hr]
  ring

/-- **D1 (deterministic weighted Jensen for the `ℓ²`-sum)**, proof. -/
theorem fcf5_D1_weighted_sum_proof (r : ℝ) (hr : r = 2 * (d : ℝ) + 6) (q : ℝ) (hq : 2 ≤ q)
    (S : NonzeroLattice d → ℝ≥0∞) :
    (∑' k : NonzeroLattice d, ENNReal.ofReal (Lattice.jp k.1 ^ (-2 * r)) * S k ^ 2) ^ (q / 2) ≤
      ENNReal.ofReal (fcf5Z d r ^ (q / 2 - 1)) *
        ∑' k : NonzeroLattice d, ENNReal.ofReal (Lattice.jp k.1 ^ (4 - 2 * r - 2 * q)) * S k ^ q := by
  have hsum : Summable fun k : NonzeroLattice d => Lattice.jp k.1 ^ (4 - 2 * r) :=
    fcf5_D1a_summable_proof r hr
  have hjp : ∀ k : NonzeroLattice d, 0 < Lattice.jp k.1 := fun k => Torus.jp_pos k.1
  have hq2 : (0 : ℝ) ≤ q / 2 := by linarith
  have hq21 : (0 : ℝ) ≤ q / 2 - 1 := by linarith
  have hZ : 0 ≤ fcf5Z d r := tsum_nonneg fun k => Real.rpow_nonneg (hjp k).le _
  have hw_sum : ∑' k : NonzeroLattice d, ENNReal.ofReal (Lattice.jp k.1 ^ (4 - 2 * r)) =
      ENNReal.ofReal (fcf5Z d r) :=
    (ENNReal.ofReal_tsum_of_nonneg (fun k => Real.rpow_nonneg (hjp k).le _) hsum).symm
  have F1 : ∀ k : NonzeroLattice d,
      ENNReal.ofReal (Lattice.jp k.1 ^ (4 - 2 * r)) *
        (ENNReal.ofReal (Lattice.jp k.1 ^ (-4 : ℝ)) * S k ^ 2) =
      ENNReal.ofReal (Lattice.jp k.1 ^ (-2 * r)) * S k ^ 2 := by
    intro k
    rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.rpow_nonneg (hjp k).le _),
      ← Real.rpow_add (hjp k), show (4 - 2 * r) + (-4 : ℝ) = -2 * r by ring]
  have hS : ∀ k : NonzeroLattice d, (S k ^ 2) ^ (q / 2) = S k ^ q := by
    intro k
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    congr 1
    push_cast
    ring
  have F2 : ∀ k : NonzeroLattice d,
      ENNReal.ofReal (Lattice.jp k.1 ^ (4 - 2 * r)) *
        (ENNReal.ofReal (Lattice.jp k.1 ^ (-4 : ℝ)) * S k ^ 2) ^ (q / 2) =
      ENNReal.ofReal (Lattice.jp k.1 ^ (4 - 2 * r - 2 * q)) * S k ^ q := by
    intro k
    rw [ENNReal.mul_rpow_of_nonneg _ _ hq2,
      ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg (hjp k).le _) hq2, hS k,
      ← Real.rpow_mul (hjp k).le, ← mul_assoc, ← ENNReal.ofReal_mul (Real.rpow_nonneg (hjp k).le _),
      ← Real.rpow_add (hjp k), show (4 - 2 * r) + (-4 * (q / 2)) = 4 - 2 * r - 2 * q by ring]
  have hJ := S7FCF5B_jensen_tsum
    (fun k : NonzeroLattice d => ENNReal.ofReal (Lattice.jp k.1 ^ (4 - 2 * r)))
    (fun k : NonzeroLattice d => ENNReal.ofReal (Lattice.jp k.1 ^ (-4 : ℝ)) * S k ^ 2)
    (p := q / 2) (by linarith)
  have e1 : (∑' k : NonzeroLattice d, ENNReal.ofReal (Lattice.jp k.1 ^ (-2 * r)) * S k ^ 2) =
      ∑' k : NonzeroLattice d, ENNReal.ofReal (Lattice.jp k.1 ^ (4 - 2 * r)) *
        (ENNReal.ofReal (Lattice.jp k.1 ^ (-4 : ℝ)) * S k ^ 2) :=
    tsum_congr fun k => (F1 k).symm
  have e2 : (∑' k : NonzeroLattice d, ENNReal.ofReal (Lattice.jp k.1 ^ (4 - 2 * r - 2 * q)) * S k ^ q) =
      ∑' k : NonzeroLattice d, ENNReal.ofReal (Lattice.jp k.1 ^ (4 - 2 * r)) *
        (ENNReal.ofReal (Lattice.jp k.1 ^ (-4 : ℝ)) * S k ^ 2) ^ (q / 2) :=
    tsum_congr fun k => (F2 k).symm
  rw [e1, e2, ← ENNReal.ofReal_rpow_of_nonneg hZ hq21, ← hw_sum]
  exact hJ

end HRS.MC.Sec7.S7FCF5B

end
