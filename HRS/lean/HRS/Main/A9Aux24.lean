import HRS.Main.A9Aux23

/-!
# Packet A9, part 24: truncation in `E_γ`, and the mode-wise convergence of the transported functional
at the adjoint level `γ` (stability at the output level `γ - 2` plus a density argument)
-/

noncomputable section

open MeasureTheory Filter Topology Finset ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.Main.A9

open HRS HRS.PDE HRS.A33 HRS.Main HRS.A34

variable {d : ℕ}

section Trunc

variable {m : ℝ}

theorem a9_norm_unit (k : NonzeroLattice d) : ‖a9unit m k‖ = 1 := by
  have := (a9unit_orthonormal (m := m) (q := 1) (k := fun _ => k) (fun a b _ => Subsingleton.elim a b)).1 0
  simpa using this

theorem a9_abs_coord_le (F : NegSobolev d m) (k : NonzeroLattice d) :
    |NegSobolev.coord F k| ≤ ‖F‖ := by
  rw [← a9unit_inner]
  have := abs_real_inner_le_norm (a9unit m k) F
  simpa [a9_norm_unit] using this

/-- truncation of `F` to the finite set `E` of modes. -/
def a9trunc (E : Finset (NonzeroLattice d)) (F : NegSobolev d m) : NegSobolev d m :=
  ∑ j ∈ E, NegSobolev.coord F j • a9unit m j

theorem a9trunc_coord (E : Finset (NonzeroLattice d)) (F : NegSobolev d m) (j : NonzeroLattice d) :
    NegSobolev.coord (a9trunc E F) j = if j ∈ E then NegSobolev.coord F j else 0 := by
  classical
  rw [← a9unit_inner]
  unfold a9trunc
  rw [inner_sum]
  have : ∀ i ∈ E, inner ℝ (a9unit m j) (NegSobolev.coord F i • a9unit m i) =
      if j = i then NegSobolev.coord F i else 0 := by
    intro i _
    rw [real_inner_smul_right, a9unit_inner, a9unit_coord]
    split_ifs with h
    · subst h; simp
    · simp
  rw [Finset.sum_congr rfl this]
  by_cases hj : j ∈ E
  · rw [Finset.sum_eq_single j]
    · simp [hj]
    · intro i _ hij; simp [Ne.symm hij]
    · intro h; exact absurd hj h
  · rw [if_neg hj]
    refine Finset.sum_eq_zero fun i hi => ?_
    have : j ≠ i := fun h => hj (h ▸ hi)
    simp [this]

theorem a9_trunc_tail_small (F : NegSobolev d m) {ε : ℝ} (hε : 0 < ε) :
    ∃ E : Finset (NonzeroLattice d), ‖F - a9trunc E F‖ < ε := by
  classical
  have hsum := (NegSobolev.coord_sq F).1
  have h := tendsto_tsum_compl_atTop_zero (fun j => NegSobolev.coord F j ^ 2)
  obtain ⟨E, hE⟩ := ((tendsto_order.1 h).2 (ε ^ 2) (by positivity)).exists
  refine ⟨E, ?_⟩
  have hnorm : ‖F - a9trunc E F‖ ^ 2 = ∑' j : {x // x ∉ E}, NegSobolev.coord F j ^ 2 := by
    rw [(NegSobolev.coord_sq (F - a9trunc E F)).2]
    rw [show (∑' j : {x // x ∉ E}, NegSobolev.coord F j ^ 2) =
      ∑' j : ↥({x | x ∉ E} : Set (NonzeroLattice d)), NegSobolev.coord F j ^ 2 from rfl,
      tsum_subtype ({x | x ∉ E} : Set (NonzeroLattice d)) (fun j => NegSobolev.coord F j ^ 2)]
    refine tsum_congr fun j => ?_
    rw [a9_coord_sub, a9trunc_coord]
    by_cases hj : j ∈ E
    · simp [hj]
    · simp [hj, Set.indicator]
  have : ‖F - a9trunc E F‖ ^ 2 < ε ^ 2 := by rw [hnorm]; exact hE
  exact lt_of_pow_lt_pow_left₀ 2 hε.le this

end Trunc

section ModeConv

theorem a9_eval_trunc {m : ℝ} (E : Finset (NonzeroLattice d)) (F : NegSobolev d m)
    (ψ : Torus d → ℝ) :
    NegSobolev.eval (a9trunc E F) ψ =
      ∑ j ∈ E, NegSobolev.fourierCoeff F j * Torus.funRealCoeff ψ j := by
  classical
  unfold NegSobolev.eval
  rw [tsum_eq_sum (s := E)]
  · refine Finset.sum_congr rfl fun j hj => ?_
    unfold NegSobolev.fourierCoeff
    rw [a9trunc_coord, if_pos hj]
  · intro j hj
    unfold NegSobolev.fourierCoeff
    rw [a9trunc_coord, if_neg hj]; simp

theorem a9_funRealCoeff_le {m : ℝ} (hm : 0 ≤ m) {ψ : Torus d → ℝ} (hψ : MemSobolev m ψ)
    (j : NonzeroLattice d) : |Torus.funRealCoeff ψ j| ≤ sobolevNorm m ψ := by
  have hs := hψ.2
  have h1 : Lattice.jp j.1 ^ (2 * m) * Torus.funRealCoeff ψ j ^ 2 ≤
      ∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (2 * m) * Torus.funRealCoeff ψ k ^ 2 :=
    hs.le_tsum j (fun k _ => mul_nonneg (Real.rpow_nonneg (Torus.jp_pos _).le _) (sq_nonneg _))
  have hj1 : 1 ≤ Lattice.jp j.1 ^ (2 * m) :=
    Real.one_le_rpow (Torus.jp_ge_one _) (by linarith)
  have h2 : Torus.funRealCoeff ψ j ^ 2 ≤ Lattice.jp j.1 ^ (2 * m) * Torus.funRealCoeff ψ j ^ 2 := by
    nlinarith [sq_nonneg (Torus.funRealCoeff ψ j)]
  unfold sobolevNorm
  refine Real.abs_le_sqrt ?_
  have := sq_nonneg (Torus.mean ψ)
  linarith

theorem a9_eval_bound (hd : 1 ≤ d) (Rg : Regime) (MB Λ VB ν₀ T : ℝ) (D : DynData d)
    (ρ : ℝ → Torus d → ℝ) (hA : AdjointData D.s (gammaIdx d) Rg MB Λ VB D ν₀ T ρ) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) T) {K' : ℝ}
    (hK' : ∀ F : NegSobolev d (gammaIdx d : ℝ), ‖transportField D ρ t (gammaIdx d : ℝ) F‖ ≤ ‖F‖ * K')
    (G : NegSobolev d (gammaIdx d : ℝ)) (k : NonzeroLattice d) :
    |NegSobolev.eval G (propagator D ρ 0 t (Torus.realMode k))| ≤
      Lattice.jp k.1 ^ (gammaIdx d : ℝ) * (‖G‖ * K') := by
  have h := a34_coord_tf hd Rg MB Λ VB ν₀ T D ρ hA ht G k
  have hj := Torus.jp_pos k.1
  have e : NegSobolev.eval G (propagator D ρ 0 t (Torus.realMode k)) =
      Lattice.jp k.1 ^ (gammaIdx d : ℝ) *
        NegSobolev.coord (transportField D ρ t (gammaIdx d : ℝ) G) k := by
    rw [h, ← mul_assoc, ← Real.rpow_add hj]; simp
  rw [e, abs_mul, abs_of_pos (Real.rpow_pos_of_pos hj _)]
  exact mul_le_mul_of_nonneg_left ((a9_abs_coord_le _ k).trans (hK' G)) (Real.rpow_nonneg hj.le _)

end ModeConv

end HRS.Main.A9
