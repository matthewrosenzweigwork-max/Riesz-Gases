import HRS.Main.T25PAux14

/-!
# T25P, part 15: `E ‖C_N^r - C̄^r‖_{𝔖₁(E_m)} ≤ C √(B_N/N)` (`P:eq:noneq-trace`), uniformly in `r`

The trace norm of the covariance discrepancy is at most the `ℓ¹` norm of its entries in the standard basis of `E_m`
(`t25p_traceNormForm_le_entries`); the entries are `2q w_k w_l (μ_N(F_{kl}) - μ(F_{kl}))` (`Q48c.entry_eq`) with
`|F_{kl}| ≤ 2d ⟨k⟩⟨l⟩`, and `t25_linear_input` bounds `E|μ_N(F) - μ(F)| ≤ C ‖F‖_∞ √(B_N/N)`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace HRS.T25P

open HRS HRS.Uniform HRS.GF HRS.AdjK HRS.Uniform.Q48c

variable {d : ℕ} {m : ℝ} {s β : ℝ} {V ρ₀ : Torus d → ℝ} {ρ : ℝ → Torus d → ℝ}

/-- The entries `(C_N - C̄)(e_k,e_l)` of the covariance discrepancy. -/
def t25pEntry (d : ℕ) (m q : ℝ) (ν : Measure (Torus d)) {N : ℕ} (x : Config d N) (p : NonzeroLattice d × NonzeroLattice d) : ℝ :=
  2 * q * (wt m p.1 * wt m p.2) * ((N : ℝ)⁻¹ * ∑ i, Fkl p.1 p.2 (x i) - ∫ u, Fkl p.1 p.2 u ∂ν)

theorem t25p_entry_abs_le (hm : (d : ℝ) + 2 < m) {q : ℝ} (hq : 0 ≤ q) {ν : Measure (Torus d)}
    [IsProbabilityMeasure ν] {N : ℕ} (hN : 1 ≤ N) (x : Config d N) (p : NonzeroLattice d × NonzeroLattice d) :
    |t25pEntry d m q ν x p| ≤ 8 * q * d * ((wt m p.1 * Lattice.jp p.1.1) * (wt m p.2 * Lattice.jp p.2.1)) := by
  have hF : ∀ u, |Fkl p.1 p.2 u| ≤ 2 * d * (Lattice.jp p.1.1 * Lattice.jp p.2.1) := fun u => abs_Fkl_le p.1 p.2 u
  set Kc : ℝ := 2 * d * (Lattice.jp p.1.1 * Lattice.jp p.2.1) with hKc
  have hKc0 : 0 ≤ Kc := by have := Torus.jp_pos p.1.1; have := Torus.jp_pos p.2.1; positivity
  have h1 : |(N : ℝ)⁻¹ * ∑ i, Fkl p.1 p.2 (x i)| ≤ Kc := by
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
    rw [abs_mul, abs_of_pos (inv_pos.2 hN0)]
    calc (N : ℝ)⁻¹ * |∑ i, Fkl p.1 p.2 (x i)| ≤ (N : ℝ)⁻¹ * ∑ i : Fin N, |Fkl p.1 p.2 (x i)| :=
          mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (inv_nonneg.2 hN0.le)
      _ ≤ (N : ℝ)⁻¹ * ∑ _i : Fin N, Kc :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => hF _) (inv_nonneg.2 hN0.le)
      _ = Kc := by simp [Finset.sum_const]; field_simp
  have h2 : |∫ u, Fkl p.1 p.2 u ∂ν| ≤ Kc := by
    have := norm_integral_le_of_norm_le_const (μ := ν) (f := Fkl p.1 p.2) (C := Kc)
      (Filter.Eventually.of_forall fun u => by simpa [Real.norm_eq_abs] using hF u)
    simpa [Real.norm_eq_abs, Measure.real, measure_univ] using this
  unfold t25pEntry
  have hw := wt_pos (m := m) p.1
  have hw' := wt_pos (m := m) p.2
  rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 * q * (wt m p.1 * wt m p.2))]
  calc 2 * q * (wt m p.1 * wt m p.2) * |(N : ℝ)⁻¹ * ∑ i, Fkl p.1 p.2 (x i) - ∫ u, Fkl p.1 p.2 u ∂ν|
      ≤ 2 * q * (wt m p.1 * wt m p.2) * (Kc + Kc) :=
        mul_le_mul_of_nonneg_left ((abs_sub _ _).trans (add_le_add h1 h2)) (by positivity)
    _ = 8 * q * d * ((wt m p.1 * Lattice.jp p.1.1) * (wt m p.2 * Lattice.jp p.2.1)) := by
        rw [hKc]; ring

theorem t25p_trace_le_entries (hm : (d : ℝ) + 2 < m) {q : ℝ} (hq : 0 ≤ q) {ρ' : Torus d → ℝ}
    (hρc : Continuous ρ') (hρP : IsProbDensity ρ') {N : ℕ} (hN : 1 ≤ N) (x : Config d N) :
    traceNormForm (covForm m q (empirical x) - covForm m q (withDensityReal ρ')) ≤
      ∑' p : NonzeroLattice d × NonzeroLattice d,
        |t25pEntry d m q (withDensityReal ρ') x p| := by
  haveI := isProb_withDensityReal hρP
  have hm1 : (d : ℝ) / 2 + 2 < m := by
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  have hm2 : (d : ℝ) + 1 < m := by linarith
  have hs := summable_s (d := d) (m := m) hm2
  have hnn : ∀ k : NonzeroLattice d, 0 ≤ wt m k * Lattice.jp k.1 := fun k =>
    mul_nonneg (wt_pos k).le (Torus.jp_pos k.1).le
  have hsum2 : Summable fun p : NonzeroLattice d × NonzeroLattice d =>
      (wt m p.1 * Lattice.jp p.1.1) * (wt m p.2 * Lattice.jp p.2.1) := hs.mul_of_nonneg hs hnn hnn
  have hsum : Summable fun p : NonzeroLattice d × NonzeroLattice d => |t25pEntry d m q (withDensityReal ρ') x p| :=
    Summable.of_nonneg_of_le (fun p => abs_nonneg _) (fun p => t25p_entry_abs_le hm hq hN x p)
      (hsum2.mul_left (8 * q * d))
  have hent : ∀ p : NonzeroLattice d × NonzeroLattice d,
      (covForm m q (empirical x) - covForm m q (withDensityReal ρ')) (basis d m p.1) (basis d m p.2) =
        t25pEntry d m q (withDensityReal ρ') x p := fun p => entry_eq hm1 hq hρc hN x p.1 p.2
  have := t25p_traceNormForm_le_entries (basis d m)
    (covForm m q (empirical x) - covForm m q (withDensityReal ρ'))
    (by simpa only [hent] using hsum)
  simpa only [hent] using this

end HRS.T25P
