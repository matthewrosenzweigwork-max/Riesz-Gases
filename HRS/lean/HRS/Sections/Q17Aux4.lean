import HRS.Sections.Sec7Fields

/-!
# Q17 projection 1: the spatial Fourier projection on `E_m` (for `projection_strong`)

`fourierProj m L` is the coordinate truncation to the box `|k_i| ≤ L` (weighted coordinates).
We prove: coordinates, linearity, contractivity in the `ℓ²` norm, and strong convergence to
the identity (Tannery's dominated convergence on the coordinate sums).
-/

noncomputable section

open MeasureTheory Filter Topology

namespace HRS.Sec7

variable {d : ℕ}

open Classical in
/-- Indicator of the frequency box `|k_i| ≤ L` (all `i`). -/
def q17_ind (L : ℕ) (k : NonzeroLattice d) : ℝ := if ∀ i, |k.1 i| ≤ (L : ℤ) then 1 else 0

theorem q17_jp_mul_rpow {m : ℝ} (k : NonzeroLattice d) (x : ℝ) :
    Lattice.jp k.1 ^ (-m) * (Lattice.jp k.1 ^ m * x) = x := by
  rw [← mul_assoc, ← Real.rpow_add (Torus.jp_pos k.1), neg_add_cancel, Real.rpow_zero, one_mul]

theorem q17_memℓp_ite {m : ℝ} (P : NonzeroLattice d → Prop) [DecidablePred P]
    (F : NegSobolev d m) :
    Memℓp (fun k : NonzeroLattice d => if P k then NegSobolev.coord F k else 0) 2 := by
  rw [Torus.memℓp_two_iff]
  refine Summable.of_nonneg_of_le (fun k => by split_ifs <;> positivity) (fun k => ?_)
    (NegSobolev.coord_sq F).1
  split_ifs
  · exact le_rfl
  · simpa using sq_nonneg (NegSobolev.coord F k)

theorem q17_coord_fourierProj {m : ℝ} (L : ℕ) (F : NegSobolev d m) (k : NonzeroLattice d) :
    NegSobolev.coord (fourierProj m L F) k = q17_ind L k * NegSobolev.coord F k := by
  classical
  have hmem : Memℓp (fun j : NonzeroLattice d => Lattice.jp j.1 ^ (-m) *
      (if ∀ i, |j.1 i| ≤ (L : ℤ) then NegSobolev.fourierCoeff F j else 0)) 2 := by
    have hfun : (fun j : NonzeroLattice d => Lattice.jp j.1 ^ (-m) *
        (if ∀ i, |j.1 i| ≤ (L : ℤ) then NegSobolev.fourierCoeff F j else 0)) =
        fun j => if ∀ i, |j.1 i| ≤ (L : ℤ) then NegSobolev.coord F j else 0 := by
      funext j
      by_cases h : ∀ i, |j.1 i| ≤ (L : ℤ)
      · rw [if_pos h, if_pos h]
        unfold NegSobolev.fourierCoeff
        exact q17_jp_mul_rpow j _
      · rw [if_neg h, if_neg h, mul_zero]
    rw [hfun]
    exact q17_memℓp_ite (fun j : NonzeroLattice d => ∀ i, |j.1 i| ≤ (L : ℤ)) F
  unfold fourierProj
  rw [NegSobolev.coord_ofSeq_of_mem _ hmem k]
  by_cases h : ∀ i, |k.1 i| ≤ (L : ℤ)
  · rw [if_pos h, q17_ind, if_pos h, one_mul]
    unfold NegSobolev.fourierCoeff
    exact q17_jp_mul_rpow k _
  · rw [if_neg h, q17_ind, if_neg h, zero_mul, mul_zero]

theorem q17_ext {m : ℝ} (F G : NegSobolev d m) (h : ∀ k, NegSobolev.coord F k = NegSobolev.coord G k) :
    F = G :=
  lp.ext (funext fun k => h k)

theorem q17_coord_add {m : ℝ} (F G : NegSobolev d m) (k : NonzeroLattice d) :
    NegSobolev.coord (F + G) k = NegSobolev.coord F k + NegSobolev.coord G k := by
  unfold NegSobolev.coord
  rfl

theorem q17_coord_sub {m : ℝ} (F G : NegSobolev d m) (k : NonzeroLattice d) :
    NegSobolev.coord (F - G) k = NegSobolev.coord F k - NegSobolev.coord G k := by
  unfold NegSobolev.coord
  rfl

theorem q17_fourierProj_add {m : ℝ} (L : ℕ) (F G : NegSobolev d m) :
    fourierProj m L (F + G) = fourierProj m L F + fourierProj m L G := by
  apply q17_ext
  intro k
  rw [q17_coord_fourierProj, q17_coord_add, q17_coord_add, q17_coord_fourierProj,
    q17_coord_fourierProj, mul_add]

theorem q17_fourierProj_smul {m : ℝ} (L : ℕ) (c : ℝ) (F : NegSobolev d m) :
    fourierProj m L (c • F) = c • fourierProj m L F := by
  apply q17_ext
  intro k
  have h1 : NegSobolev.coord (c • F) k = c * NegSobolev.coord F k := by
    unfold NegSobolev.coord
    rfl
  have h2 : NegSobolev.coord (c • fourierProj m L F) k = c * NegSobolev.coord (fourierProj m L F) k := by
    unfold NegSobolev.coord
    rfl
  rw [q17_coord_fourierProj, h1, h2, q17_coord_fourierProj]
  ring

/-- Contractivity of the projection in the `ℓ²` (`H^{-m}`) norm. -/
theorem q17_norm_fourierProj_le {m : ℝ} (L : ℕ) (F : NegSobolev d m) :
    ‖fourierProj m L F‖ ≤ ‖F‖ := by
  have h1 := (NegSobolev.coord_sq (fourierProj m L F)).2
  have h2 := (NegSobolev.coord_sq F).2
  have hs : Summable (fun k : NonzeroLattice d => NegSobolev.coord (fourierProj m L F) k ^ 2) :=
    (NegSobolev.coord_sq (fourierProj m L F)).1
  have hle : ‖fourierProj m L F‖ ^ 2 ≤ ‖F‖ ^ 2 := by
    rw [h1, h2]
    refine Summable.tsum_le_tsum (fun k => ?_) hs (NegSobolev.coord_sq F).1
    rw [q17_coord_fourierProj]
    have hi : q17_ind L k ^ 2 ≤ 1 := by
      unfold q17_ind
      split_ifs <;> norm_num
    have hi0 : 0 ≤ q17_ind L k := by
      unfold q17_ind
      split_ifs <;> norm_num
    calc (q17_ind L k * NegSobolev.coord F k) ^ 2 = q17_ind L k ^ 2 * NegSobolev.coord F k ^ 2 := by
          ring
      _ ≤ 1 * NegSobolev.coord F k ^ 2 := mul_le_mul_of_nonneg_right hi (sq_nonneg _)
      _ = NegSobolev.coord F k ^ 2 := one_mul _
  calc ‖fourierProj m L F‖ = Real.sqrt (‖fourierProj m L F‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt (‖F‖ ^ 2) := Real.sqrt_le_sqrt hle
    _ = ‖F‖ := Real.sqrt_sq (norm_nonneg _)

/-- Strong convergence of the projection to the identity on `E_m`. -/
theorem q17_fourierProj_tendsto {m : ℝ} (F : NegSobolev d m) :
    Tendsto (fun L : ℕ => ‖fourierProj m L F - F‖) atTop (𝓝 0) := by
  -- squared norms tend to zero by dominated convergence on the coordinate sums
  have hsq : Tendsto (fun L : ℕ => ‖fourierProj m L F - F‖ ^ 2) atTop (𝓝 0) := by
    have hterm : ∀ L : ℕ, ‖fourierProj m L F - F‖ ^ 2 =
        ∑' k : NonzeroLattice d, (q17_ind L k - 1) ^ 2 * NegSobolev.coord F k ^ 2 := by
      intro L
      rw [(NegSobolev.coord_sq _).2]
      refine tsum_congr (fun k => ?_)
      rw [q17_coord_sub, q17_coord_fourierProj]
      ring
    simp_rw [hterm]
    have hlim := tendsto_tsum_of_dominated_convergence (𝓕 := atTop)
      (f := fun (L : ℕ) (k : NonzeroLattice d) => (q17_ind L k - 1) ^ 2 * NegSobolev.coord F k ^ 2)
      (g := fun _ => 0) (bound := fun k => NegSobolev.coord F k ^ 2)
      (NegSobolev.coord_sq F).1 ?_ ?_
    · simpa using hlim
    · intro k
      have hev : ∀ᶠ L : ℕ in atTop, q17_ind L k = 1 := by
        obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ i, |k.1 i| ≤ (N : ℤ) := by
          refine ⟨∑ i, (k.1 i).natAbs, fun i => ?_⟩
          have h1 : |k.1 i| ≤ ((k.1 i).natAbs : ℤ) := by
            rw [Int.abs_eq_natAbs]
          have h2 : (((k.1 i).natAbs : ℕ) : ℤ) ≤ ((∑ j, (k.1 j).natAbs : ℕ) : ℤ) := by
            exact_mod_cast Finset.single_le_sum (f := fun j => (k.1 j).natAbs)
              (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
          exact h1.trans h2
        filter_upwards [eventually_ge_atTop N] with L hL
        unfold q17_ind
        rw [if_pos]
        intro i
        exact (hN i).trans (by exact_mod_cast hL)
      apply tendsto_const_nhds.congr'
      filter_upwards [hev] with L hL
      rw [hL]
      ring
    · exact Filter.Eventually.of_forall fun L k => by
        have hi : (q17_ind L k - 1) ^ 2 ≤ 1 := by
          unfold q17_ind
          split_ifs <;> norm_num
        calc ‖(q17_ind L k - 1) ^ 2 * NegSobolev.coord F k ^ 2‖
            = (q17_ind L k - 1) ^ 2 * NegSobolev.coord F k ^ 2 := by
              rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
          _ ≤ 1 * NegSobolev.coord F k ^ 2 := mul_le_mul_of_nonneg_right hi (sq_nonneg _)
          _ = NegSobolev.coord F k ^ 2 := one_mul _
  have hcont : Tendsto (fun x : ℝ => Real.sqrt x) (𝓝 0) (𝓝 0) := by
    simpa using Real.continuous_sqrt.tendsto 0
  have := hcont.comp hsq
  refine this.congr (fun L => ?_)
  simp [Real.sqrt_sq (norm_nonneg _)]

end HRS.Sec7
