import HRS.MC.S7PIM1a

/-!
# Packet piM, part M1b: the quadratic field `ℬ̃_N` as an honest element of `E_r` and `E_m` (prefix `S7PIM_`)

* `S7PIM_ofSeq_mem`, `S7PIM_ofSeq_norm_le`: a sequence with `|c_k| ≤ A ⟨k⟩²` is in `E_m` for `d < 2(m-2)` with
  norm `≤ |A| (∑ ⟨k⟩^{-2(m-2)})^{1/2}`;
* `S7PIM_tilde_embed`: `quadFieldTilde m = embedCLM (quadFieldTilde r)` for `r ≤ m`, `d < 2(r-2)`, `N ≥ 1`, `t ≥ 0`;
* `S7PIM_tilde_bdd_one`: for `N = 1` the field `quadFieldTilde m` is bounded in `E_m` uniformly in `X` and `t ≥ 0`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7PIM

open HRS HRS.Sec7 HRS.MC.Sec7 HRS.MC.SEdge HRS.MC.QRSpec

variable {d : ℕ}

theorem S7PIM_sq_le {m : ℝ} (A : ℝ) (c : NonzeroLattice d → ℝ) (hc : ∀ k, |c k| ≤ A * Lattice.jp k.1 ^ 2)
    (k : NonzeroLattice d) :
    (Lattice.jp k.1 ^ (-m) * c k) ^ 2 ≤ A ^ 2 * Lattice.jp k.1 ^ (-(2 * (m - 2))) := by
  have hj := Torus.jp_pos k.1
  have h1 : c k ^ 2 ≤ (A * Lattice.jp k.1 ^ 2) ^ 2 := by
    rw [← sq_abs (c k)]
    exact pow_le_pow_left₀ (abs_nonneg _) (hc k) 2
  have h2 : Lattice.jp k.1 ^ (-(2 * (m - 2))) = Lattice.jp k.1 ^ (2 * (-m)) * Lattice.jp k.1 ^ 4 := by
    rw [show -(2 * (m - 2)) = 2 * (-m) + (4 : ℕ) by push_cast; ring, Real.rpow_add hj, Real.rpow_natCast]
  rw [mul_pow, Torus.jp_rpow_sq, h2]
  calc Lattice.jp k.1 ^ (2 * (-m)) * c k ^ 2
      ≤ Lattice.jp k.1 ^ (2 * (-m)) * (A * Lattice.jp k.1 ^ 2) ^ 2 :=
        mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg hj.le _)
    _ = A ^ 2 * (Lattice.jp k.1 ^ (2 * (-m)) * Lattice.jp k.1 ^ 4) := by ring

theorem S7PIM_ofSeq_mem {m : ℝ} (hm : (d : ℝ) < 2 * (m - 2)) (A : ℝ) (c : NonzeroLattice d → ℝ)
    (hc : ∀ k, |c k| ≤ A * Lattice.jp k.1 ^ 2) :
    Memℓp (fun k : NonzeroLattice d => Lattice.jp k.1 ^ (-m) * c k) 2 := by
  rw [Torus.memℓp_two_iff]
  exact Summable.of_nonneg_of_le (fun k => sq_nonneg _) (S7PIM_sq_le A c hc)
    ((summable_jp_rpow (m - 2) hm).mul_left (A ^ 2))

theorem S7PIM_ofSeq_norm_le {m : ℝ} (hm : (d : ℝ) < 2 * (m - 2)) (A : ℝ) (c : NonzeroLattice d → ℝ)
    (hc : ∀ k, |c k| ≤ A * Lattice.jp k.1 ^ 2) :
    ‖NegSobolev.ofSeq m c‖ ≤
      |A| * Real.sqrt (∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (-(2 * (m - 2)))) := by
  have hmem := S7PIM_ofSeq_mem hm A c hc
  have hs := summable_jp_rpow (d := d) (m - 2) hm
  obtain ⟨h1, h2⟩ := NegSobolev.coord_sq (NegSobolev.ofSeq m c)
  have hZ : 0 ≤ ∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (-(2 * (m - 2))) :=
    tsum_nonneg fun k => Real.rpow_nonneg (Torus.jp_pos k.1).le _
  have hsq : ‖NegSobolev.ofSeq m c‖ ^ 2 ≤
      (|A| * Real.sqrt (∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (-(2 * (m - 2))))) ^ 2 := by
    rw [h2, mul_pow, Real.sq_sqrt hZ, sq_abs, ← tsum_mul_left]
    refine h1.tsum_le_tsum (fun k => ?_) (hs.mul_left _)
    rw [NegSobolev.coord_ofSeq_of_mem c hmem k]
    exact S7PIM_sq_le A c hc k
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp hsq

theorem S7PIM_tilde_embed (R : Regime d) {r m : ℝ} (hr : (d : ℝ) < 2 * (r - 2)) (hrm : r ≤ m) {N : ℕ}
    (hN : 0 < N) {t : ℝ} (ht : 0 ≤ t) (X : Config d N) :
    quadFieldTilde m R.D.s (withDensityReal (R.ρ t)) X =
      HRS.MD.EQInterp.embedCLM hrm (quadFieldTilde r R.D.s (withDensityReal (R.ρ t)) X) := by
  obtain ⟨K1, K2, c, hK1, hK2, hb⟩ := S7PIM_coeff_bound R
  set cf : NonzeroLattice d → ℝ := fun k => (N : ℝ) *
    modulatedEnergy (hTransport d R.D.s (Torus.realMode k)) X (withDensityReal (R.ρ t)) with hcf
  have hmem := S7PIM_ofSeq_mem hr (K1 / (2 * N) *
      ∑ i, ∑ j ∈ Finset.univ.erase i, (periodicRiesz d R.D.s (X i - X j) + c) + 3 / 2 * N * K2) cf
    (fun k => by
      exact (hb t ht hN X k).trans (le_of_eq (mul_comm _ _)))
  rw [HRS.MD.EQInterp.embedCLM_apply]
  unfold quadFieldTilde NegSobolev.embed
  congr 1
  funext k
  show cf k = NegSobolev.fourierCoeff (NegSobolev.ofSeq r cf) k
  unfold NegSobolev.fourierCoeff
  rw [NegSobolev.coord_ofSeq_of_mem cf hmem k, ← mul_assoc, ← Real.rpow_add (Torus.jp_pos k.1)]
  simp

theorem S7PIM_tilde_bdd_one (R : Regime d) {m : ℝ} (hm : (d : ℝ) < 2 * (m - 2)) :
    ∃ C : ℝ, ∀ t : ℝ, 0 ≤ t → ∀ X : Config d 1,
      ‖quadFieldTilde m R.D.s (withDensityReal (R.ρ t)) X‖ ≤ C := by
  obtain ⟨K1, K2, c, hK1, hK2, hb⟩ := S7PIM_coeff_bound R
  refine ⟨|3 / 2 * ((1 : ℕ) : ℝ) * K2| *
    Real.sqrt (∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (-(2 * (m - 2)))), fun t ht X => ?_⟩
  unfold quadFieldTilde
  have hG : ∀ i : Fin 1, ∑ j ∈ Finset.univ.erase i, (periodicRiesz d R.D.s (X i - X j) + c) = 0 := by
    intro i
    have : Finset.univ.erase i = ∅ := by
      ext j
      simp [Subsingleton.elim j i]
    rw [this]; simp
  refine (S7PIM_ofSeq_norm_le hm (3 / 2 * ((1 : ℕ) : ℝ) * K2) _ (fun k => ?_))
  have := hb t ht Nat.one_pos X k
  simp only [hG, Finset.sum_const_zero, mul_zero, zero_add] at this
  exact this.trans (le_of_eq (mul_comm _ _))

end HRS.MC.Sec7.S7PIM

end
