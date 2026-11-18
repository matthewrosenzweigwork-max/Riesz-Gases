import HRS.MS.SuppU11Aux2

/-!
# U11 helper file 3: boundedness of the thermal density, the coefficient family `a_{αℓ}` and
its Bessel bound `∑_ℓ a_{αℓ}² ≤ B_α` with `∑_α B_α < ∞`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal BigOperators

namespace HRS.Whole

variable {d : ℕ}

/-- The thermal density is bounded (`ρ ≤ Z⁻¹`, `V ≥ 0`, `g * μ ≥ 0`). -/
lemma u11_rho_le (hd : 2 ≤ d) {a β : ℝ} (ha : 0 < a) (hβ : 0 < β) {ρ : Euc d → ℝ}
    (hρ : IsThermalEquilibrium d ((d : ℝ) / 2) a β ρ) : ∃ M : ℝ, ∀ x, ρ x ≤ M := by
  obtain ⟨_, hprob, hden⟩ := hρ
  have hint : ∫ y, ρ y = 1 := hprob.integral_one
  have hs0 : ((d : ℝ) / 2) ≠ 0 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    positivity
  have hexp : ∀ y : Euc d, Real.exp (-β * (confinement a y +
      convMeasure (rieszKernel d ((d : ℝ) / 2)) (withDensityReal ρ) y)) ≤ 1 := by
    intro y
    rw [Real.exp_le_one_iff]
    have h1 : 0 ≤ confinement a y := by
      unfold confinement
      positivity
    have h2 : 0 ≤ convMeasure (rieszKernel d ((d : ℝ) / 2)) (withDensityReal ρ) y := by
      unfold convMeasure
      refine integral_nonneg fun z => ?_
      unfold rieszKernel
      rw [if_neg hs0]
      exact Real.rpow_nonneg (norm_nonneg _) _
    nlinarith
  have hZ0 : 0 ≤ ∫ y, Real.exp (-β * (confinement a y +
      convMeasure (rieszKernel d ((d : ℝ) / 2)) (withDensityReal ρ) y)) :=
    integral_nonneg fun y => (Real.exp_pos _).le
  have hZ : 0 < ∫ y, Real.exp (-β * (confinement a y +
      convMeasure (rieszKernel d ((d : ℝ) / 2)) (withDensityReal ρ) y)) := by
    rcases hZ0.lt_or_eq with h | h
    · exact h
    · exfalso
      have h0 : ∀ y, ρ y = 0 := fun y => by rw [hden y, ← h, div_zero]
      simp [h0] at hint
  refine ⟨(∫ y, Real.exp (-β * (confinement a y +
      convMeasure (rieszKernel d ((d : ℝ) / 2)) (withDensityReal ρ) y)))⁻¹, fun x => ?_⟩
  rw [hden x, div_eq_mul_inv]
  calc _ ≤ 1 * (∫ y, Real.exp (-β * (confinement a y +
        convMeasure (rieszKernel d ((d : ℝ) / 2)) (withDensityReal ρ) y)))⁻¹ :=
        mul_le_mul_of_nonneg_right (hexp x) (inv_nonneg.2 hZ0)
    _ = _ := one_mul _

/-- The coefficients `a_{αℓ} = β⟨P_μ φ_α, R_{β,μ} e_ℓ⟩` of `S:R:eq:return-map` (S line 6759). -/
def u11Coef (d : ℕ) (β : ℝ) (ρβ : Euc d → ℝ) (e : ℕ → Euc d → ℝ) (m : ℝ) (α : MultiIndex d)
    (l : ℕ) : ℝ :=
  β * l2Inner (withDensityReal ρβ) (projMean (withDensityReal ρβ) (oscTestFun m α))
    (responseInverse (rieszKernel d ((d : ℝ) / 2)) (withDensityReal ρβ) β (e l))

/-- Bessel bound of the coefficient rows with a summable bound. -/
lemma u11_coef_bessel (hd : 2 ≤ d) {a β : ℝ} (ha : 0 < a) (hβ : 0 < β) {ρβ : Euc d → ℝ}
    (hρ : IsThermalEquilibrium d ((d : ℝ) / 2) a β ρβ) {e : ℕ → Euc d → ℝ}
    (he : ∀ l, MemL2Zero (withDensityReal ρβ) (e l))
    (horth : ∀ l j, β * l2Inner (withDensityReal ρβ) (e l)
      (responseInverse (rieszKernel d ((d : ℝ) / 2)) (withDensityReal ρβ) β (e j)) =
        if l = j then 1 else 0) {m : ℝ} (hm : (wholeSpaceIndex d : ℝ) ≤ m) :
    ∃ B : MultiIndex d → ℝ, Summable B ∧ (∀ α, 0 ≤ B α) ∧
      ∀ (α : MultiIndex d) (S : Finset ℕ), ∑ l ∈ S, u11Coef d β ρβ e m α l ^ 2 ≤ B α := by
  have hprob : IsProbDensity ρβ := hρ.1.1
  obtain ⟨M, hM⟩ := u11_rho_le hd ha hβ hρ
  have := Q34.isProbabilityMeasure_nu hprob
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hQ : Q34.Q34Hyp d ((d : ℝ) / 2) ρβ M :=
    ⟨by omega, by positivity, by linarith, hprob, hM⟩
  obtain ⟨C0, hC0, hosc⟩ := u11_osc_bound (d := d)
  have hdm : (d : ℝ) < m := by
    have : (d : ℝ) < (wholeSpaceIndex d : ℝ) := by
      unfold wholeSpaceIndex
      push_cast
      linarith
    linarith
  refine ⟨fun α => 4 * β * C0 ^ 2 * oscEigenvalue d α ^ (-m), ?_, fun α => ?_, ?_⟩
  · exact (OscDual.summable_oscEv_neg_rpow hdm).mul_left _
  · have := Real.rpow_nonneg (oscEv_pos α).le (-m)
    positivity
  · intro α S
    have hK : ∀ x, |oscTestFun m α x| ≤ C0 * oscEigenvalue d α ^ (-(m / 2)) := hosc m α
    obtain ⟨hmem, hint⟩ := u11_projMean_bound (withDensityReal ρβ) (u11_osc_continuous m α) hK
    have hb := u11_bessel_model hQ hβ e he horth hmem S
    have hsq : (C0 * oscEigenvalue d α ^ (-(m / 2))) ^ 2 = C0 ^ 2 * oscEigenvalue d α ^ (-m) := by
      rw [mul_pow, show -(m / 2) = (-m) / 2 by ring, rpow_half_sq _ _ (oscEv_pos α)]
    calc ∑ l ∈ S, u11Coef d β ρβ e m α l ^ 2
        ≤ β * ∫ x, projMean (withDensityReal ρβ) (oscTestFun m α) x ^ 2 ∂(withDensityReal ρβ) :=
          hb
      _ ≤ β * (4 * (C0 * oscEigenvalue d α ^ (-(m / 2))) ^ 2) :=
          mul_le_mul_of_nonneg_left hint hβ.le
      _ = 4 * β * C0 ^ 2 * oscEigenvalue d α ^ (-m) := by rw [hsq]; ring

lemma u11_diag_norm_le (om : ℕ → ℝ) (hom : ∀ l, 0 < om l) {s : ℝ} (hs : 0 ≤ s) (z : SeqL2) :
    ‖u11Diag om s z‖ ≤ ‖z‖ := by
  have hsq : ‖u11Diag om s z‖ ^ 2 ≤ ‖z‖ ^ 2 := by
    rw [← u11_norm_sq, ← u11_norm_sq]
    refine (u11_coord_summable _).tsum_le_tsum (fun l => ?_) (u11_coord_summable z)
    unfold u11Diag
    rw [u11_coord_ofSeq (u11_diag_memℓp om hom hs z), mul_pow]
    have h1 : Real.exp (-s * om l) ≤ 1 := by
      rw [Real.exp_le_one_iff]; nlinarith [hom l]
    have h0 := Real.exp_pos (-s * om l)
    have h2 : Real.exp (-s * om l) ^ 2 ≤ 1 := pow_le_one₀ h0.le h1
    nlinarith [mul_nonneg (sub_nonneg.2 h2) (sq_nonneg (SeqL2.coord z l))]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 hsq

end HRS.Whole
