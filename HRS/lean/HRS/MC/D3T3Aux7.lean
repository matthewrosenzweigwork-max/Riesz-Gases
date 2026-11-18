import HRS.MC.D3T3Aux6

/-!
# Packet D3T3, auxiliary facts: `∑_k |k|² ψ̂(tk)² ≤ A t^{-(d+2)}` for every `t > 0`.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal FourierTransform

namespace HRS.MC.D3T3

open HRS HRS.MC.FDLE HRS.MC.Per HRS.MC.D3T1

variable {d : ℕ}

lemma d3f_rpow_neg_nat {t : ℝ} (ht : 0 < t) (N : ℕ) : t ^ (-(N : ℝ)) = (t ^ N)⁻¹ := by
  rw [Real.rpow_neg ht.le, Real.rpow_natCast]

lemma d3f_lattice_sum (hd : 1 ≤ d) {ψ : Euc d → ℝ} (hψ : IsFDLProfile ψ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ t : ℝ, 0 < t →
      Summable (fun k : Lattice d => Lattice.enorm k ^ 2 * fdlPsiHat ψ (t • Lattice.toEuc k) ^ 2) ∧
      ∑' k : Lattice d, Lattice.enorm k ^ 2 * fdlPsiHat ψ (t • Lattice.toEuc k) ^ 2
        ≤ A * t ^ (-((d : ℝ) + 2)) := by
  obtain ⟨C, hC0, hC⟩ := d3f_psi_sq hψ (d + 2)
  set r : ℝ := 2 - 2 * ((d + 2 : ℕ) : ℝ) with hr
  have hsum := summable_enorm_rpow_aux (d := d) r (by
    rw [hr]; push_cast; linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)])
  set S0 : ℝ := ∑' k : NonzeroLattice d, Lattice.enorm k.1 ^ r with hS0
  have hS00 : 0 ≤ S0 := tsum_nonneg fun k => Real.rpow_nonneg (norm_nonneg _) _
  set L0 : ℝ := Laplacian.laplacian (fdlPhi ψ) 0 with hL0
  have hpi : 0 < 4 * Real.pi ^ 2 := by positivity
  refine ⟨|L0| / (4 * Real.pi ^ 2) + C * S0 * 2 ^ (d + 2), by positivity, fun t ht => ?_⟩
  have hNt : 0 < t ^ (-((d : ℝ) + 2)) := Real.rpow_pos_of_pos ht _
  have hNe : t ^ (-((d : ℝ) + 2)) = (t ^ (d + 2))⁻¹ := by
    have := d3f_rpow_neg_nat ht (d + 2)
    push_cast at this
    exact this
  by_cases ht2 : t ≤ 1 / 2
  · -- small `t`: Fourier series at the origin
    have hl := d3f_lap_zero (φ := fdlPer (fdlPhiScale ψ t)) (d3f_per_smooth hψ ht)
    have hre : ∀ k : Lattice d, (Torus.fcoef (fdlPer (fdlPhiScale ψ t)) k).re
        = fdlPsiHat ψ (t • Lattice.toEuc k) ^ 2 := by
      intro k; rw [per_fcoef hd hψ ht k, Complex.ofReal_re]
    simp only [hre] at hl
    obtain ⟨hl1, hl2⟩ := hl
    refine ⟨hl1, ?_⟩
    rw [d3f_lap_per_small hψ ht ht2] at hl2
    have hsumeq : ∑' k : Lattice d, Lattice.enorm k ^ 2 * fdlPsiHat ψ (t • Lattice.toEuc k) ^ 2
        = -((t ^ (d + 2))⁻¹ * L0) / (4 * Real.pi ^ 2) := by
      rw [eq_div_iff hpi.ne']
      linarith [hl2]
    rw [hsumeq, hNe]
    have hinv : 0 ≤ (t ^ (d + 2))⁻¹ := inv_nonneg.2 (pow_nonneg ht.le _)
    have h1 : -((t ^ (d + 2))⁻¹ * L0) ≤ (t ^ (d + 2))⁻¹ * |L0| := by
      have := neg_abs_le L0
      nlinarith [mul_le_mul_of_nonneg_left (neg_le_abs L0) hinv]
    calc -((t ^ (d + 2))⁻¹ * L0) / (4 * Real.pi ^ 2)
        ≤ ((t ^ (d + 2))⁻¹ * |L0|) / (4 * Real.pi ^ 2) :=
          div_le_div_of_nonneg_right h1 hpi.le
      _ = |L0| / (4 * Real.pi ^ 2) * (t ^ (d + 2))⁻¹ := by ring
      _ ≤ (|L0| / (4 * Real.pi ^ 2) + C * S0 * 2 ^ (d + 2)) * (t ^ (d + 2))⁻¹ :=
          mul_le_mul_of_nonneg_right (by nlinarith [mul_nonneg (mul_nonneg hC0 hS00) (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (d + 2))]) hinv
  · -- large `t`: crude decay
    have ht2' : 1 / 2 < t := not_le.mp ht2
    have hterm : ∀ k : NonzeroLattice d,
        Lattice.enorm k.1 ^ 2 * fdlPsiHat ψ (t • Lattice.toEuc k.1) ^ 2 ≤
          (C * t ^ (-(2 * ((d + 2 : ℕ) : ℝ)))) * Lattice.enorm k.1 ^ r := by
      intro k
      have hen : 0 < Lattice.enorm k.1 := lt_of_lt_of_le one_pos (d3f_enorm_ge_one k.2)
      have h1 := hC t ht k.1 k.2
      calc Lattice.enorm k.1 ^ 2 * fdlPsiHat ψ (t • Lattice.toEuc k.1) ^ 2
          ≤ Lattice.enorm k.1 ^ 2 * (C * t ^ (-(2 * ((d + 2 : ℕ) : ℝ))) *
              Lattice.enorm k.1 ^ (-(2 * ((d + 2 : ℕ) : ℝ)))) :=
            mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
        _ = (C * t ^ (-(2 * ((d + 2 : ℕ) : ℝ)))) *
              (Lattice.enorm k.1 ^ (2 : ℕ) * Lattice.enorm k.1 ^ (-(2 * ((d + 2 : ℕ) : ℝ)))) := by ring
        _ = _ := by
            rw [← Real.rpow_natCast, ← Real.rpow_add hen, hr]
            push_cast; ring_nf
    have hsumA : Summable (fun k : NonzeroLattice d => (C * t ^ (-(2 * ((d + 2 : ℕ) : ℝ)))) *
        Lattice.enorm k.1 ^ r) := hsum.mul_left _
    have hsumN : Summable (fun k : Lattice d =>
        Lattice.enorm k ^ 2 * fdlPsiHat ψ (t • Lattice.toEuc k) ^ 2) := by
      rw [Torus.summable_lattice_iff]
      exact Summable.of_nonneg_of_le (fun k => mul_nonneg (sq_nonneg _) (sq_nonneg _)) hterm hsumA
    refine ⟨hsumN, ?_⟩
    rw [Torus.tsum_lattice _ hsumN]
    have h0 : Lattice.enorm (0 : Lattice d) ^ 2 * fdlPsiHat ψ (t • Lattice.toEuc (0 : Lattice d)) ^ 2 = 0 := by
      have : Lattice.toEuc (0 : Lattice d) = 0 := by ext i; simp [Lattice.toEuc]
      simp [Lattice.enorm, this]
    rw [h0, zero_add]
    have h2 : ∑' k : NonzeroLattice d, Lattice.enorm k.1 ^ 2 * fdlPsiHat ψ (t • Lattice.toEuc k.1) ^ 2
        ≤ (C * t ^ (-(2 * ((d + 2 : ℕ) : ℝ)))) * S0 := by
      rw [hS0, ← tsum_mul_left]
      exact Summable.tsum_le_tsum hterm ((Torus.summable_lattice_iff _).mp hsumN) hsumA
    refine h2.trans ?_
    -- `t^{-2N} ≤ 2^N t^{-N}` for `t > 1/2`
    have hN : t ^ (-(2 * ((d + 2 : ℕ) : ℝ))) ≤ 2 ^ (d + 2) * t ^ (-((d : ℝ) + 2)) := by
      have e1 : t ^ (-(2 * ((d + 2 : ℕ) : ℝ))) = t ^ (-((d : ℝ) + 2)) * t ^ (-((d : ℝ) + 2)) := by
        rw [← Real.rpow_add ht]; push_cast; ring_nf
      have e2 : t ^ (-((d : ℝ) + 2)) ≤ 2 ^ (d + 2) := by
        rw [hNe, ← inv_pow]
        refine pow_le_pow_left₀ (inv_nonneg.2 ht.le) ?_ _
        rw [inv_le_comm₀ ht (by norm_num)]
        linarith
      rw [e1]
      exact mul_le_mul_of_nonneg_right e2 hNt.le
    calc C * t ^ (-(2 * ((d + 2 : ℕ) : ℝ))) * S0
        ≤ C * (2 ^ (d + 2) * t ^ (-((d : ℝ) + 2))) * S0 := by gcongr
      _ = (C * S0 * 2 ^ (d + 2)) * t ^ (-((d : ℝ) + 2)) := by ring
      _ ≤ (|L0| / (4 * Real.pi ^ 2) + C * S0 * 2 ^ (d + 2)) * t ^ (-((d : ℝ) + 2)) := by
          gcongr
          exact le_add_of_nonneg_left (by positivity)

end HRS.MC.D3T3
