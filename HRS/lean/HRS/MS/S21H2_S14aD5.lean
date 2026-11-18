import HRS.MS.S21H2_S14aD3
import HRS.MS.S21H2_S14aD4
import HRS.MS.S21H2_S10B
import HRS.MS.S21F_S14
import HRS.MS.R2ChaosAux42

/-!
# S21H2, packet R26-T3.S14a (part D5): the actual initial reference carries a `KRep` operator, and its centered classes are infinite dimensional

`KRep` at the actual `μ₀` (`s111x2_krep_of_tcref`, as in `r26t3_initial_cov_bound`).  Infinite dimension of `V`: `s94_exists_onb` (with `s := 1`, so that the logarithmic-moment
field of `IsRound2Density` is vacuous) gives a `ℕ`-indexed orthonormal family `P_μ a_i` of centered classes.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set InformationTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace

namespace HRS.MS.R26T3
open HRS HRS.Whole HRS.Whole.Q34 HRS.MS.S111X2

theorem s21h2_krep_init {p : Parameters} {δ : ℝ} (hδ : 0 < δ) (hδh : δ ≤ 1 / 2)
    (R : Trajectory p δ) [IsProbabilityMeasure (r26t3_mu R 0)] :
    ∃ (Mg : ℝ) (K : Lp ℝ 2 (r26t3_mu R 0) →L[ℝ] Lp ℝ 2 (r26t3_mu R 0)),
      KRep (rieszKernel p.d p.s) (r26t3_mu R 0) K Mg := by
  obtain ⟨-, -, -, href⟩ := r26t3_reference_data p δ hδ hδh R
  obtain ⟨M, c, S, hc, hTc⟩ := href 0
  have hd := p.hd
  have hsd : p.s < (p.d : ℝ) := by
    have := p.hs
    have : (0 : ℝ) < p.d := by exact_mod_cast (by omega : 0 < p.d)
    linarith
  have hP : IsProbabilityMeasure (HRS.Whole.withDensityReal (R.ρ 0)) := ‹IsProbabilityMeasure (r26t3_mu R 0)›
  obtain ⟨Mg, K, hK⟩ := HRS.MS.S111X2.s111x2_krep_of_tcref (by omega) p.hs0 hsd hc hTc
  exact ⟨Mg, K, hK⟩

theorem s21h2_not_fin {p : Parameters} {δ : ℝ} (hδ : 0 < δ) (hδh : δ ≤ 1 / 2)
    (R : Trajectory p δ) [IsProbabilityMeasure (r26t3_mu R 0)] :
    ¬ FiniteDimensional ℝ (s21h2_V (r26t3_mu R 0)) := by
  obtain ⟨-, -, -, href⟩ := r26t3_reference_data p δ hδ hδh R
  obtain ⟨M, c, S, hc, hTc⟩ := href 0
  have hM : ∀ x, R.ρ 0 x ≤ |M| := fun x => by
    have h1 := hTc.gauss x
    have h2 : Real.exp (-c * ‖x‖ ^ 2) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg ‖x‖])
    have h0 : 0 ≤ M := by
      have := hTc.gauss 0
      have h3 := hTc.pos 0
      simp at this
      linarith
    calc R.ρ 0 x ≤ M * Real.exp (-c * ‖x‖ ^ 2) := h1
      _ ≤ M * 1 := mul_le_mul_of_nonneg_left h2 h0
      _ ≤ |M| := by rw [mul_one]; exact le_abs_self _
  have hρ : IsRound2Density p.d 1 |M| 0 (R.ρ 0) := ⟨hTc.prob, hM, fun h => absurd h one_ne_zero⟩
  obtain ⟨a, hat, hon, hcomp⟩ := HRS.MS.R2Chaos.s94_exists_onb p.hd hρ
  set μ := r26t3_mu R 0 with hμ
  let u : ℕ → s21h2_V μ := fun i =>
    ⟨(HRS.MS.R2Chaos.s94_memLp_projMean (μ := μ) (hat i)).toLp (HRS.Whole.projMean μ (a i)), by
      rw [s21h2_mem_V, inner_one2]
      have := (HRS.MS.R2Chaos.s94_memLp_projMean (μ := μ) (hat i)).coeFn_toLp
      rw [integral_congr_ae this]
      exact HRS.MS.R2Chaos.s94_integral_projMean (μ := μ) (hat i)⟩
  have hu : Orthonormal ℝ u := by
    rw [orthonormal_iff_ite]
    intro i j
    show inner ℝ ((HRS.MS.R2Chaos.s94_memLp_projMean (μ := μ) (hat i)).toLp (HRS.Whole.projMean μ (a i)))
      ((HRS.MS.R2Chaos.s94_memLp_projMean (μ := μ) (hat j)).toLp (HRS.Whole.projMean μ (a j))) = _
    rw [s21h2_L2_inner]
    exact hon i j
  intro hfd
  have := hu.linearIndependent.finite_of_isNoetherian
  exact not_finite ℕ

end HRS.MS.R26T3
