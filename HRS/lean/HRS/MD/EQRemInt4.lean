import HRS.MD.EQRemInt3

/-!
# EQ-REM (b), part 4: duality and Sobolev bounds for the adjoint propagator
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MD.EQRem

open HRS HRS.MD.EQ29 HRS.Quad

variable {d : ℕ} {s : ℝ}

theorem eqrem_funRealCoeff_realMode (k j : NonzeroLattice d) :
    Torus.funRealCoeff (Torus.realMode k : Torus d → ℝ) j = if j = k then 1 else 0 := by
  unfold Torus.funRealCoeff
  rw [Torus.realMode_orthonormal j k]

theorem eqrem_eval_realMode {m : ℝ} (F : NegSobolev d m) (k : NonzeroLattice d) :
    NegSobolev.eval F (Torus.realMode k) = NegSobolev.fourierCoeff F k := by
  unfold NegSobolev.eval
  simp_rw [eqrem_funRealCoeff_realMode k]
  rw [tsum_eq_single k]
  · simp
  · intro j hj; simp [hj]

theorem eqrem_abs_coord_le {m : ℝ} (F : NegSobolev d m) (k : NonzeroLattice d) :
    |NegSobolev.coord F k| ≤ ‖F‖ := by
  obtain ⟨hs, hn⟩ := NegSobolev.coord_sq F
  have h1 : NegSobolev.coord F k ^ 2 ≤ ∑' j, NegSobolev.coord F j ^ 2 := hs.le_tsum k (fun j _ => sq_nonneg _)
  rw [← hn] at h1
  exact abs_le_of_sq_le_sq' (by simpa using h1) (norm_nonneg _) |> fun h => abs_le.2 h

theorem eqrem_coord_ofSeq_finite {m : ℝ} (F : Finset (NonzeroLattice d)) (c : NonzeroLattice d → ℝ)
    (hc : ∀ j, j ∉ F → c j = 0) (j : NonzeroLattice d) :
    NegSobolev.fourierCoeff (NegSobolev.ofSeq m c) j = c j := by
  have hmem : Memℓp (fun k : NonzeroLattice d => Lattice.jp k.1 ^ (-m) * c k) 2 := by
    rw [Torus.memℓp_two_iff]
    exact summable_of_ne_finset_zero (s := F) fun k hk => by simp [hc k hk]
  unfold NegSobolev.fourierCoeff
  rw [NegSobolev.coord_ofSeq_of_mem c hmem, ← mul_assoc, ← Real.rpow_add (Torus.jp_pos j.1)]
  simp

/-- Sobolev bound of a test function from the duality with a bounded operator on `E_M`. -/
theorem eqrem_dual_sobolev {M : ℝ} (W : NegSobolev d M →L[ℝ] NegSobolev d M) {κ : ℝ} (hκ : ‖W‖ ≤ κ)
    (φ : Torus d → ℝ) (k : NonzeroLattice d)
    (hdual : ∀ Y : NegSobolev d M, NegSobolev.fourierCoeff (W Y) k = NegSobolev.eval Y φ) :
    Summable (fun j : NonzeroLattice d => Lattice.jp j.1 ^ (2 * M) * Torus.funRealCoeff φ j ^ 2) ∧
    ∑' j : NonzeroLattice d, Lattice.jp j.1 ^ (2 * M) * Torus.funRealCoeff φ j ^ 2 ≤
      (Lattice.jp k.1 ^ M * κ) ^ 2 := by
  classical
  have hκ0 : 0 ≤ κ := (norm_nonneg _).trans hκ
  set A : ℝ := Lattice.jp k.1 ^ M * κ with hA
  have hA0 : 0 ≤ A := mul_nonneg (Real.rpow_nonneg (Torus.jp_pos _).le _) hκ0
  set w : NonzeroLattice d → ℝ := fun j => Lattice.jp j.1 ^ (2 * M) * Torus.funRealCoeff φ j ^ 2 with hw
  have hw0 : ∀ j, 0 ≤ w j := fun j => mul_nonneg (Real.rpow_nonneg (Torus.jp_pos _).le _) (sq_nonneg _)
  have key : ∀ F : Finset (NonzeroLattice d), ∑ j ∈ F, w j ≤ A ^ 2 := by
    intro F
    set c : NonzeroLattice d → ℝ := fun j => if j ∈ F then Lattice.jp j.1 ^ (2 * M) * Torus.funRealCoeff φ j else 0
      with hc
    have hcF : ∀ j, j ∉ F → c j = 0 := fun j hj => by simp [hc, hj]
    set Y : NegSobolev d M := NegSobolev.ofSeq M c with hY
    have hfc : ∀ j, NegSobolev.fourierCoeff Y j = c j := eqrem_coord_ofSeq_finite F c hcF
    -- eval Y φ = ∑_F w
    have hev : NegSobolev.eval Y φ = ∑ j ∈ F, w j := by
      unfold NegSobolev.eval
      simp_rw [hfc]
      rw [tsum_eq_sum (s := F) (fun j hj => by simp [hc, hj])]
      refine Finset.sum_congr rfl fun j hj => ?_
      simp only [hc, if_pos hj, hw]; ring
    -- ‖Y‖² = ∑_F w
    have hnorm : ‖Y‖ ^ 2 = ∑ j ∈ F, w j := by
      obtain ⟨-, hn⟩ := NegSobolev.coord_sq Y
      rw [hn]
      have hcoord : ∀ j, NegSobolev.coord Y j = Lattice.jp j.1 ^ (-M) * c j := by
        intro j
        have hmem : Memℓp (fun k : NonzeroLattice d => Lattice.jp k.1 ^ (-M) * c k) 2 := by
          rw [Torus.memℓp_two_iff]
          exact summable_of_ne_finset_zero (s := F) fun k hk => by simp [hcF k hk]
        exact NegSobolev.coord_ofSeq_of_mem c hmem j
      rw [tsum_eq_sum (s := F) (fun j hj => by simp [hcoord, hcF j hj])]
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [hcoord]
      simp only [hc, if_pos hj, hw]
      have hjp := Torus.jp_pos j.1
      calc (Lattice.jp j.1 ^ (-M) * (Lattice.jp j.1 ^ (2 * M) * Torus.funRealCoeff φ j)) ^ 2
          = (Lattice.jp j.1 ^ (-M) * Lattice.jp j.1 ^ (2 * M)) ^ 2 * Torus.funRealCoeff φ j ^ 2 := by ring
        _ = (Lattice.jp j.1 ^ M) ^ 2 * Torus.funRealCoeff φ j ^ 2 := by
            rw [← Real.rpow_add hjp]; congr 2; ring_nf
        _ = _ := by rw [Torus.jp_rpow_sq]
    have h1 : ∑ j ∈ F, w j ≤ Lattice.jp k.1 ^ M * ‖W‖ * ‖Y‖ := by
      rw [← hev, ← hdual Y]
      have hfk : NegSobolev.fourierCoeff (W Y) k = Lattice.jp k.1 ^ M * NegSobolev.coord (W Y) k := rfl
      rw [hfk]
      calc Lattice.jp k.1 ^ M * NegSobolev.coord (W Y) k
          ≤ Lattice.jp k.1 ^ M * |NegSobolev.coord (W Y) k| :=
            mul_le_mul_of_nonneg_left (le_abs_self _) (Real.rpow_nonneg (Torus.jp_pos _).le _)
        _ ≤ Lattice.jp k.1 ^ M * ‖W Y‖ :=
            mul_le_mul_of_nonneg_left (eqrem_abs_coord_le _ k) (Real.rpow_nonneg (Torus.jp_pos _).le _)
        _ ≤ Lattice.jp k.1 ^ M * (‖W‖ * ‖Y‖) :=
            mul_le_mul_of_nonneg_left (W.le_opNorm Y) (Real.rpow_nonneg (Torus.jp_pos _).le _)
        _ = _ := by ring
    have h2 : ∑ j ∈ F, w j ≤ A * ‖Y‖ := by
      refine h1.trans ?_
      rw [hA]
      have := Real.rpow_nonneg (Torus.jp_pos k.1).le M
      gcongr
    -- S ≤ A ‖Y‖, ‖Y‖² = S  ⟹  S ≤ A²
    have hS0 : 0 ≤ ∑ j ∈ F, w j := Finset.sum_nonneg fun j _ => hw0 j
    have hY0 : 0 ≤ ‖Y‖ := norm_nonneg _
    have hYA : ‖Y‖ ≤ A := by
      by_contra hcon
      push Not at hcon
      have : ‖Y‖ ^ 2 ≤ A * ‖Y‖ := by rw [hnorm]; exact h2
      nlinarith
    calc ∑ j ∈ F, w j = ‖Y‖ ^ 2 := hnorm.symm
      _ ≤ A ^ 2 := pow_le_pow_left₀ hY0 hYA 2
  exact ⟨summable_of_sum_le hw0 key, (summable_of_sum_le hw0 key).tsum_le_of_sum_le key⟩

end HRS.MD.EQRem

end
