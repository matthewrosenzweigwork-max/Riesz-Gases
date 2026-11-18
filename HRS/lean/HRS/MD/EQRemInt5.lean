import HRS.MD.EQRemInt4

/-!
# EQ-REM (b), part 5: the `E_M`-energy of the pairing is transported by the dual evolution
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MD.EQRem

open HRS HRS.MD.EQ29 HRS.Quad

variable {d : ℕ} {s : ℝ}

theorem eqrem_coordEnergy_eq {M : ℝ} {c : NonzeroLattice d → ℝ}
    (hsum : Summable fun k : NonzeroLattice d => Lattice.jp k.1 ^ (-2 * M) * c k ^ 2) :
    coordEnergy M c = ENNReal.ofReal (∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (-2 * M) * c k ^ 2) := by
  unfold coordEnergy
  exact (ENNReal.ofReal_tsum_of_nonneg (fun k => mul_nonneg (Real.rpow_nonneg (Torus.jp_pos _).le _)
    (sq_nonneg _)) hsum).symm

theorem eqrem_summable_of_coordEnergy {M : ℝ} {c : NonzeroLattice d → ℝ} (h : coordEnergy M c ≠ ⊤) :
    Summable fun k : NonzeroLattice d => Lattice.jp k.1 ^ (-2 * M) * c k ^ 2 := by
  have h1 := ENNReal.summable_toReal h
  refine h1.congr fun k => ?_
  rw [ENNReal.toReal_ofReal (mul_nonneg (Real.rpow_nonneg (Torus.jp_pos _).le _) (sq_nonneg _))]

/-- Summability of the product of two weighted `ℓ²` sequences. -/
theorem eqrem_summable_prod {M : ℝ} {a b : NonzeroLattice d → ℝ}
    (ha : Summable fun k : NonzeroLattice d => Lattice.jp k.1 ^ (-2 * M) * a k ^ 2)
    (hb : Summable fun k : NonzeroLattice d => Lattice.jp k.1 ^ (2 * M) * b k ^ 2) :
    Summable fun k : NonzeroLattice d => a k * b k := by
  refine Summable.of_norm_bounded ((ha.add hb).mul_left (1 / 2)) fun k => ?_
  have hj := Torus.jp_pos k.1
  have e1 : Lattice.jp k.1 ^ (-2 * M) * Lattice.jp k.1 ^ (2 * M) = 1 := by
    rw [← Real.rpow_add hj]; simp
  rw [Real.norm_eq_abs]
  have hx : 0 ≤ Lattice.jp k.1 ^ (-2 * M) := Real.rpow_nonneg hj.le _
  have hy : 0 ≤ Lattice.jp k.1 ^ (2 * M) := Real.rpow_nonneg hj.le _
  -- |a b| ≤ (u a² + v b²)/2 with u v = 1
  have : (a k * b k) ^ 2 * (Lattice.jp k.1 ^ (-2 * M) * Lattice.jp k.1 ^ (2 * M)) =
      (Lattice.jp k.1 ^ (-2 * M) * a k ^ 2) * (Lattice.jp k.1 ^ (2 * M) * b k ^ 2) := by ring
  rw [e1, mul_one] at this
  have h2 : |a k * b k| ^ 2 ≤ ((Lattice.jp k.1 ^ (-2 * M) * a k ^ 2 + Lattice.jp k.1 ^ (2 * M) * b k ^ 2) / 2) ^ 2 := by
    rw [sq_abs, this]
    nlinarith [sq_nonneg (Lattice.jp k.1 ^ (-2 * M) * a k ^ 2 - Lattice.jp k.1 ^ (2 * M) * b k ^ 2)]
  have h3 := abs_le_of_sq_le_sq' h2 (by positivity)
  calc |a k * b k| ≤ (Lattice.jp k.1 ^ (-2 * M) * a k ^ 2 + Lattice.jp k.1 ^ (2 * M) * b k ^ 2) / 2 := h3.2
    _ = 1 / 2 * (Lattice.jp k.1 ^ (-2 * M) * a k ^ 2 + Lattice.jp k.1 ^ (2 * M) * b k ^ 2) := by ring

/-- The transported energy: if `φ_k` are `C²` test functions with `⟨W Y, e_k⟩ = ⟨Y, φ_k⟩` for a bounded operator `W` on
`E_M` (`‖W‖ ≤ κ`, `κ > 0`), then `∑_k ⟨k⟩^{-2M} 𝓡(φ_k)(X)² ≤ κ² ∑_k ⟨k⟩^{-2M} 𝓡(e_k)(X)²` for every configuration. -/
theorem eqrem_energy_transfer (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (V : Torus d → ℝ) (hV : Torus.IsSmooth V)
    {β : ℝ} (hβ : 0 < β) {ρβ : Torus d → ℝ} (hρ : IsThermalDensity (periodicRiesz d s) V β ρβ)
    {N : ℕ} (hN : 2 ≤ N) {M : ℝ} (hM : (d : ℝ) / 2 + 2 < M)
    (W : NegSobolev d M →L[ℝ] NegSobolev d M) {κ : ℝ} (hκ : ‖W‖ ≤ κ) (hκpos : 0 < κ)
    (φ : NonzeroLattice d → Torus d → ℝ) (hφ2 : ∀ k, Torus.IsCk 2 (φ k))
    (hdual : ∀ (k : NonzeroLattice d) (Y : NegSobolev d M), NegSobolev.fourierCoeff (W Y) k = NegSobolev.eval Y (φ k))
    (X : Config d N) :
    coordEnergy M (fun k => statRemainder d s V β ρβ (N := N) (φ k) X) ≤
      ENNReal.ofReal (κ ^ 2) * coordEnergy M (fun j => statRemainder d s V β ρβ (N := N) (Torus.realMode j) X) := by
  set r : NonzeroLattice d → ℝ := fun j => statRemainder d s V β ρβ (N := N) (Torus.realMode j) X with hr
  by_cases hE : coordEnergy M r = ⊤
  · rw [hE, ENNReal.mul_top (ENNReal.ofReal_pos.2 (by positivity)).ne']
    exact le_top
  have hrs := eqrem_summable_of_coordEnergy hE
  -- the element Y with coordinates r
  have hmem : Memℓp (fun k : NonzeroLattice d => Lattice.jp k.1 ^ (-M) * r k) 2 := by
    rw [Torus.memℓp_two_iff]
    refine hrs.congr fun k => ?_
    rw [mul_pow, Torus.jp_rpow_sq]; ring_nf
  set Y : NegSobolev d M := NegSobolev.ofSeq M r with hY
  have hcoordY : ∀ j, NegSobolev.coord Y j = Lattice.jp j.1 ^ (-M) * r j := NegSobolev.coord_ofSeq_of_mem r hmem
  have hfY : ∀ j, NegSobolev.fourierCoeff Y j = r j := by
    intro j
    unfold NegSobolev.fourierCoeff
    rw [hcoordY, ← mul_assoc, ← Real.rpow_add (Torus.jp_pos j.1)]; simp
  -- the coordinates of the transported element
  have hg : ∀ k, statRemainder d s V β ρβ (N := N) (φ k) X = NegSobolev.fourierCoeff (W Y) k := by
    intro k
    obtain ⟨hsob, -⟩ := eqrem_dual_sobolev W hκ (φ k) k (hdual k)
    have hexp := eqrem_stat_expansion hd hs0 hsd V hV hβ hρ hN hM X (hφ2 k) hsob
    -- ⟨Y, φ_k⟩ = ∑' r_j φ̂_j
    have hsp : Summable fun j : NonzeroLattice d => r j * Torus.funRealCoeff (φ k) j :=
      eqrem_summable_prod (a := r) (b := Torus.funRealCoeff (φ k)) hrs hsob
    have hlim : Tendsto (fun F : Finset (NonzeroLattice d) => ∑ j ∈ F, r j * Torus.funRealCoeff (φ k) j)
        atTop (𝓝 (∑' j, r j * Torus.funRealCoeff (φ k) j)) := hsp.hasSum
    have hlim' : Tendsto (fun F : Finset (NonzeroLattice d) => ∑ j ∈ F, r j * Torus.funRealCoeff (φ k) j)
        atTop (𝓝 (statRemainder d s V β ρβ (N := N) (φ k) X)) := by
      refine hexp.congr fun F => ?_
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [hdual k Y, NegSobolev.eval]
    simp_rw [hfY]
    exact tendsto_nhds_unique hlim' hlim
  have hnorm_sq : ∀ k, Lattice.jp k.1 ^ (-2 * M) * (NegSobolev.fourierCoeff (W Y) k) ^ 2 =
      NegSobolev.coord (W Y) k ^ 2 := by
    intro k
    unfold NegSobolev.fourierCoeff
    rw [mul_pow, ← mul_assoc, Torus.jp_rpow_sq, ← Real.rpow_add (Torus.jp_pos k.1)]
    simp
  obtain ⟨hsW, hnW⟩ := NegSobolev.coord_sq (W Y)
  obtain ⟨hsY, hnY⟩ := NegSobolev.coord_sq Y
  have hsumg : Summable fun k : NonzeroLattice d =>
      Lattice.jp k.1 ^ (-2 * M) * (statRemainder d s V β ρβ (N := N) (φ k) X) ^ 2 := by
    refine hsW.congr fun k => ?_
    rw [hg k, hnorm_sq k]
  rw [eqrem_coordEnergy_eq hsumg, eqrem_coordEnergy_eq hrs]
  have h1 : ∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (-2 * M) * (statRemainder d s V β ρβ (N := N) (φ k) X) ^ 2 =
      ‖W Y‖ ^ 2 := by
    rw [hnW]
    exact tsum_congr fun k => by rw [hg k, hnorm_sq k]
  have h2 : ∑' j : NonzeroLattice d, Lattice.jp j.1 ^ (-2 * M) * r j ^ 2 = ‖Y‖ ^ 2 := by
    rw [hnY]
    refine tsum_congr fun j => ?_
    rw [hcoordY, mul_pow, Torus.jp_rpow_sq]; ring_nf
  rw [h1, h2, ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have : ‖W Y‖ ≤ κ * ‖Y‖ := (W.le_opNorm Y).trans (mul_le_mul_of_nonneg_right hκ (norm_nonneg _))
  calc ‖W Y‖ ^ 2 ≤ (κ * ‖Y‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) this 2
    _ = κ ^ 2 * ‖Y‖ ^ 2 := by ring

end HRS.MD.EQRem

end
