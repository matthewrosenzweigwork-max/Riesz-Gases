import HRS.MS.R2InterpAux57

/-!
# S10.2 (worker S102), part 58 (packet F6): the bracket identity for the noise coefficients of the grid, and their bound
-/

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators MatrixOrder Matrix

namespace HRS.MS.R2Interp

open HRS HRS.Whole HRS.MS.CovMeas HRS.MC.Sec7.PI

variable {d : ℕ} {C : WholeCoeff d} {m T : ℝ} {r : ℕ} {c : MultiIndex d → ℝ}

/-- The diffusion coefficient `Φ^i_{(p,a)}(s) = √N · (√(2ν)/N) ∂_a(obsTest_i s)(X^p_s)`. -/
def s102_Phic (C : WholeCoeff d) (m : ℝ) {T : ℝ} {N : ℕ} {Ω : Type} (hT : 0 < T) (L : ℕ)
    (X : ℝ≥0 → Ω → EucConfig d N) (s : ℝ) (ζ : Ω) (k : Fin N × Fin d) (i : Fin (s102_q d L)) : ℝ :=
  Real.sqrt N * (Real.sqrt (2 * C.ν) / N *
    gradient (s102_ot C m (s102_tauk hT L) (s102_alk L) i s) (X s.toNNReal ζ k.1) k.2)

theorem s102_bracket_grid (hν : 0 ≤ C.ν) (hT : 0 < T) (L : ℕ) (μ : Measure (Euc d)) {s : ℝ}
    (hμ : ∀ g : Euc d → ℝ, HRS.Whole.pair μ g = ∫ x, g x * C.ρ s x) {N : ℕ} (hN : 0 < N) {Ω : Type}
    (X : ℝ≥0 → Ω → EucConfig d N) (ζ : Ω) (i j : Fin (s102_q d L)) :
    ∑ k : Fin N × Fin d, s102_Phic C m hT L X s ζ k i * s102_Phic C m hT L X s ζ k j =
      s102_rateM C m hT L s i j + (Real.sqrt N)⁻¹ * (2 * C.ν *
        s102_hh2 C m (s102_tauk hT L) (s102_alk L) (s102_etaf μ X ζ) i j s) := by
  unfold s102_Phic
  rw [s102_bracket_sum hN (by linarith : 0 ≤ 2 * C.ν)]
  rw [s102_bracket_decomp hN (2 * C.ν) (HRS.Whole.empirical (X s.toNNReal ζ)) μ]
  rw [← s102_eta_ot (C := C) (m := m) hT L μ X ζ s i j, s102_pair_ot hT L μ hμ i j]
  rfl

/-- Bound of the diffusion coefficients, uniform in the configuration, for `s ∈ [0,T]`. -/
theorem s102_Phic_bound (hs : S102Std C m T r c) (hT : 0 < T) (L : ℕ) {N : ℕ} {Ω : Type}
    (X : ℝ≥0 → Ω → EucConfig d N) :
    ∃ Cn : ℝ, 0 ≤ Cn ∧ ∀ s ∈ Icc (0 : ℝ) T, ∀ ζ k i, |s102_Phic C m hT L X s ζ k i| ≤ Cn := by
  have hc0 : 0 ≤ ∑ k : Fin (s102_q d L), c (s102_alk L k) := Finset.sum_nonneg fun k _ => hs.hD.nonneg _
  refine ⟨Real.sqrt N * (Real.sqrt (2 * C.ν) / N * ∑ k : Fin (s102_q d L), c (s102_alk L k)), ?_, ?_⟩
  · positivity
  · intro s hsT ζ k i
    unfold s102_Phic
    rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _), abs_mul, abs_of_nonneg (by positivity)]
    refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (by positivity)) (Real.sqrt_nonneg _)
    have hc : 0 ≤ ∑ k : Fin (s102_q d L), c (s102_alk L k) := Finset.sum_nonneg fun k _ => hs.hD.nonneg _
    have hi : c (s102_alk L i) ≤ ∑ k : Fin (s102_q d L), c (s102_alk L k) :=
      Finset.single_le_sum (f := fun k => c (s102_alk L k)) (fun k _ => hs.hD.nonneg _) (Finset.mem_univ i)
    refine le_trans ?_ hi
    unfold s102_ot
    by_cases h : s ≤ (s102_tauk hT L i : ℝ)
    · rw [if_pos h]
      have hb := hs.hD.bddU (s102_alk L i) s hsT (s102_tauk hT L i) ⟨h, (s102_tauk hT L i).2.2⟩ 1
        (by omega) (X s.toNNReal ζ k.1)
      rw [s102_gradient_apply, ← Real.norm_eq_abs]
      have h1 := (iteratedFDeriv ℝ 1 (propagatorW C s (s102_tauk hT L i) (oscTestFun m (s102_alk L i)))
        (X s.toNNReal ζ k.1)).le_opNorm (fun _ : Fin 1 => (EuclideanSpace.single k.2 (1 : ℝ) : Euc d))
      simp only [iteratedFDeriv_one_apply, Finset.univ_unique, Fin.default_eq_zero, Finset.prod_singleton,
        EuclideanSpace.norm_single, norm_one, mul_one] at h1
      exact h1.trans hb
    · rw [if_neg h, s102_gradient_zero]
      simpa using hs.hD.nonneg (s102_alk L i)

end HRS.MS.R2Interp

end
