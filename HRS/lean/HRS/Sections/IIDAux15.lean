import HRS.Sections.IIDAux14

/-!
# IID helper chain, part 15: the comparison for a sampling density `q` with `|q - ρ| ≤ κρ` against
the Gaussian of covariance `ρ` (uniform constants), the engine of the mixture statement.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace HRS.IID

section Gen

open HRS.InitialDataAux

variable {d : ℕ}

theorem comparison_gen (hd : 2 ≤ d) (m : ℝ) (hm : (d : ℝ) / 2 < m) (c : ℝ) (hc : 0 < c) :
    ∃ Cs Cw Cz M : ℝ, 0 ≤ Cs ∧ 0 ≤ Cw ∧ 0 ≤ Cz ∧ 0 < M ∧
      ∀ q ρ : Torus d → ℝ, IsProbDensity q → (∀ x, c ≤ q x) → IsProbDensity ρ →
      ∀ κ : ℝ, 0 ≤ κ → (∀ x, |q x - ρ x| ≤ κ * ρ x) →
      ∀ γ : Measure (NegSobolev d m), IsCenteredGaussianWithCov m γ (iidCov (withDensityReal ρ)) →
      ∀ N : ℕ, 1 ≤ N →
        smoothDist 2 ((Measure.pi fun _ : Fin N => withDensityReal q).map
            (fld m N (withDensityReal q))) γ ≤
          Cs * (N : ℝ) ^ (-((m - (d : ℝ) / 2) / (2 * m))) + Cz * κ ∧
        CB ((Measure.pi fun _ : Fin N => withDensityReal q).map (fld m N (withDensityReal q))) γ
          (Cw * (Real.log (Real.exp 1 * N) / Real.sqrt N) ^
            ((m - (d : ℝ) / 2) / (m + (d : ℝ) / 2)) + Cz * κ) M := by
  have hm2 : (d : ℝ) < 2 * m := by
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  set Z : ℝ := ∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (-(2 * m)) with hZ
  have hZ0 : 0 ≤ Z := Z_nonneg
  obtain ⟨Ct, hCt0, hCt⟩ := tail_boxT_le (d := d) hm2
  obtain ⟨C2, hC2, h2⟩ := rate_smooth hd hm hZ0 hCt0
  obtain ⟨C1, hC1, h1⟩ := rate_W hd hm hZ0 hCt0
  refine ⟨C2, C1 + 1, Real.sqrt (20 * Z), 1632 * Z ^ 2 + 1, hC2, by positivity, by positivity,
    by positivity, ?_⟩
  intro q ρ hq hqc hρ κ hκ hqρ γ hγ N hN
  haveI : IsProbabilityMeasure γ := by haveI := hγ.1.1; infer_instance
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  set Λ : ℝ := Real.log (Real.exp 1 * N) with hΛ
  have hΛ1 : 1 ≤ Λ := by
    rw [hΛ, Real.log_mul (Real.exp_pos 1).ne' hN0.ne', Real.log_exp]
    have : 0 ≤ Real.log N := Real.log_nonneg hN1
    linarith
  set j : ℝ := (Λ / Real.sqrt N) ^ ((m - (d : ℝ) / 2) / (m + (d : ℝ) / 2)) with hj
  have hj0 : 0 < j := Real.rpow_pos_of_pos (div_pos (by linarith) (Real.sqrt_pos.2 hN0)) _
  have hδ : ∀ T : Finset (NonzeroLattice d), Real.sqrt (20 * κ ^ 2 * ∑ k ∈ T, Lattice.jp k.1 ^ (-(2 * m))) ≤
      Real.sqrt (20 * Z) * κ := by
    intro T
    have hS := S_le_Z hm2 T
    calc Real.sqrt (20 * κ ^ 2 * ∑ k ∈ T, Lattice.jp k.1 ^ (-(2 * m))) ≤ Real.sqrt (κ ^ 2 * (20 * Z)) := by
          apply Real.sqrt_le_sqrt; nlinarith [sq_nonneg κ]
      _ = Real.sqrt (20 * Z) * κ := by
          rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hκ]; ring
  obtain ⟨L, hL1, hL⟩ := h2 N hN
  obtain ⟨L', hL1', hL'⟩ := h1 N hN
  refine ⟨?_, ?_⟩
  · have hd2 := iid_T_d2_mix hm2 hc hq hqc hρ hκ hqρ hγ (boxT d L) hN
    refine hd2.trans ?_
    have hS := S_le_Z hm2 (boxT d L)
    have hcard : ((boxT d L).card : ℝ) ≤ (((2 * L + 1) ^ d : ℕ) : ℝ) := by
      exact_mod_cast card_boxT_le L
    have ht := tailR_box_le (hCt L hL1)
    have := hδ (boxT d L)
    have hle : 8 * (∑ k ∈ boxT d L, Lattice.jp k.1 ^ (-(2 * m))) / N *
        (2 * Real.sqrt (boxT d L).card * Real.sqrt N + 1) + 2 * Real.sqrt (tailR d m (boxT d L)) ≤
        8 * Z / N * (2 * Real.sqrt (((2 * L + 1) ^ d : ℕ) : ℝ) * Real.sqrt N + 1) +
          2 * Real.sqrt (2 * (Ct * (L : ℝ) ^ ((d : ℝ) - 2 * m))) := by
      gcongr
    linarith
  · have hCB := CB_T_mix hm2 hc hq hqc hρ hκ hqρ hγ (boxT d L') hN hj0
    obtain ⟨π, hπ, hp, a, b⟩ := hCB
    refine ⟨π, hπ, hp, a.trans (ENNReal.ofReal_le_ofReal ?_), b.trans (ENNReal.ofReal_le_ofReal ?_)⟩
    · have hS := S_le_Z hm2 (boxT d L')
      have hcard : ((boxT d L').card : ℝ) ≤ (((2 * L' + 1) ^ d : ℕ) : ℝ) := by
        exact_mod_cast card_boxT_le L'
      have ht := tailR_box_le (hCt L' hL1')
      have := hδ (boxT d L')
      have hle : Real.sqrt (8 * (∑ k ∈ boxT d L', Lattice.jp k.1 ^ (-(2 * m))) / N) *
          (((boxT d L').card : ℝ) * Λ + 2) + 2 * Real.sqrt (tailR d m (boxT d L')) ≤
          Real.sqrt (8 * Z / N) * ((((2 * L' + 1) ^ d : ℕ) : ℝ) * Λ + 2) +
            2 * Real.sqrt (2 * (Ct * (L' : ℝ) ^ ((d : ℝ) - 2 * m))) := by
        gcongr
      nlinarith [hL', hle]
    · nlinarith [sq_nonneg Z]

end Gen

end HRS.IID
