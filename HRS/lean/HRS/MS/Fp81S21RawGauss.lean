import HRS.MS.Fp81S21GaussIncrFull4
import HRS.MS.Fp81S21Uniform3

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory Set Classical
open scoped ENNReal NNReal BigOperators RealInnerProductSpace

namespace HRS.Fp81.S21

open HRS (Euc)
open HRS.Whole
open HRS.MS.R26T3 HRS.MS.S111X2

/-- The normalized Hermite coordinate trace of the combined feature is
uniformly summable at every nonnegative time. The KRep selected by the G2
feature increment theorem is fixed before the trace bound. -/
theorem fp81s21_combinedFeature_trace (p : Parameters) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ,
        ∀ [IsProbabilityMeasure (r26t3_mu R 0)],
        ∃ Mg : ℝ, ∃ K : Lp ℝ 2 (r26t3_mu R 0) →L[ℝ]
          Lp ℝ 2 (r26t3_mu R 0),
        ∃ hK : KRep (rieszKernel p.d p.s) (r26t3_mu R 0) K Mg,
        ∃ V : ℝ, 0 ≤ V ∧
          ∀ t : ℝ, 0 ≤ t →
            Summable (fun α : MultiIndex p.d =>
              ‖fp81s21_combinedFeature p R hK t
                (oscTestFun (wholeSpaceIndex p.d : ℝ) α)‖ ^ 2) ∧
            (∑' α : MultiIndex p.d,
              ‖fp81s21_combinedFeature p R hK t
                (oscTestFun (wholeSpaceIndex p.d : ℝ) α)‖ ^ 2) ≤ V := by
  obtain ⟨δG, hδG, hδGhalf, hG⟩ :=
    fp81s21_gaussian_combined_feature_increment_bound p
  obtain ⟨δC, hδC, -, hC⟩ :=
    fp81s21_uniform_covariance_domination p
  let δ0 := min δG δC
  have hδ0 : 0 < δ0 := lt_min hδG hδC
  have hδ0half : δ0 ≤ 1 / 2 :=
    (min_le_left _ _).trans hδGhalf
  refine ⟨δ0, hδ0, hδ0half, ?_⟩
  intro δ hδ hδle R hμ₀
  letI : IsProbabilityMeasure (r26t3_mu R 0) := hμ₀
  have hδG' : δ ≤ δG := hδle.trans (min_le_left _ _)
  have hδC' : δ ≤ δC := hδle.trans (min_le_right _ _)
  obtain ⟨Mg, K, hK, B, g, g', c, gN, cN,
      hB, hg, hg', hc, hgN, hcN, hGH⟩ :=
    hG δ hδ hδG' R
  obtain ⟨Kcov, hKcov, hCov⟩ := hC δ hδ hδC' R
  obtain ⟨Cbase, hCbase⟩ := hermiteFunD_uniform_bound (d := p.d)
  let Ch := max Cbase 1
  have hCh0 : 0 ≤ Ch := le_trans (by norm_num) (le_max_right _ _)
  have hCh : ∀ (α : MultiIndex p.d) (x : Euc p.d),
      |hermiteFunD α x| ≤ Ch := by
    intro α x
    exact (hCbase α x).trans (le_max_left _ _)
  let m : ℝ := wholeSpaceIndex p.d
  have hm : (p.d : ℝ) < m := by
    dsimp [m, wholeSpaceIndex]
    exact_mod_cast (show p.d < 24 * p.d + 240 by omega)
  have hsumlam : Summable (fun α : MultiIndex p.d => oscEigenvalue p.d α ^ (-m)) :=
    OscDual.summable_oscEv_neg_rpow hm
  let V : ℝ := Kcov * Ch ^ 2 * (∑' α : MultiIndex p.d,
    oscEigenvalue p.d α ^ (-m))
  have hV : 0 ≤ V := by
    dsimp [V]
    exact mul_nonneg (mul_nonneg hKcov (sq_nonneg Ch))
      (tsum_nonneg fun _ => Real.rpow_nonneg (le_of_lt (oscEv_pos _)) _)
  refine ⟨Mg, K, hK, V, hV, ?_⟩
  intro t ht
  have hT : 0 < t + 1 := by linarith
  have htmem : t ∈ Icc (0 : ℝ) (t + 1) := ⟨ht, by linarith⟩
  have hμt : IsProbabilityMeasure (r26t3_mu R t) :=
    HRS.Whole.Q34.isProbabilityMeasure_nu
      ((R.resulting.global (t + 1)).density t htmem)
  letI : IsProbabilityMeasure (r26t3_mu R t) := hμt
  let ψ : MultiIndex p.d → Euc p.d → ℝ := fun α =>
    oscTestFun (m) α
  have hψtest : ∀ α, IsOscTest m (ψ α) := by
    intro α
    simpa [ψ, m] using HRS.MS.GenPath.s56_isOscTest m α
  have hInt : ∀ α, Integrable (fun x => (ψ α x) ^ 2) (r26t3_mu R t) := by
    intro α
    let lam : ℝ := oscEigenvalue p.d α
    have hlam : 0 < lam := oscEv_pos α
    have hψbound : ∀ x, |ψ α x| ≤ Ch * lam ^ (-(m / 2)) := by
      intro x
      rw [show ψ α x = lam ^ (-(m / 2)) * hermiteFunD α x by rfl,
        abs_mul, abs_of_nonneg (Real.rpow_nonneg hlam.le _)]
      calc
        lam ^ (-(m / 2)) * |hermiteFunD α x| ≤
            lam ^ (-(m / 2)) * Ch :=
          mul_le_mul_of_nonneg_left (hCh α x) (Real.rpow_nonneg hlam.le _)
        _ = Ch * lam ^ (-(m / 2)) := by ring
    have hsqbound : ∀ x, (ψ α x) ^ 2 ≤
        Ch ^ 2 * lam ^ (-m) := by
      intro x
      have hscale : 0 ≤ Ch * lam ^ (-(m / 2)) :=
        mul_nonneg hCh0 (Real.rpow_nonneg hlam.le _)
      have hsq := sq_le_sq'
        (le_trans (neg_nonpos.mpr hscale) (abs_nonneg (ψ α x))) (hψbound x)
      have hpow : (lam ^ (-(m / 2))) ^ 2 = lam ^ (-m) := by
        rw [← neg_div, rpow_half_sq (-m) lam hlam]
      rw [sq_abs, mul_pow, hpow] at hsq
      nlinarith [hCh0, sq_nonneg Ch, Real.rpow_nonneg hlam.le (-m)]
    have hmaj : Integrable (fun _ : Euc p.d => Ch ^ 2 * lam ^ (-m))
        (r26t3_mu R t) := integrable_const _
    exact hmaj.mono' ((hψtest α).1.continuous.measurable.pow_const 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_of_nonneg (sq_nonneg _)]
        exact hsqbound x)
  have hIntBound : ∀ α,
      (∫ x, (ψ α x) ^ 2 ∂(r26t3_mu R t)) ≤
        Ch ^ 2 * oscEigenvalue p.d α ^ (-m) := by
    intro α
    let lam : ℝ := oscEigenvalue p.d α
    have hlam : 0 < lam := oscEv_pos α
    have hsqbound : ∀ x, (ψ α x) ^ 2 ≤
        Ch ^ 2 * lam ^ (-m) := by
      intro x
      have habs : |ψ α x| ≤ Ch * lam ^ (-(m / 2)) := by
        rw [show ψ α x = lam ^ (-(m / 2)) * hermiteFunD α x by rfl,
          abs_mul, abs_of_nonneg (Real.rpow_nonneg hlam.le _)]
        calc
          lam ^ (-(m / 2)) * |hermiteFunD α x| ≤
              lam ^ (-(m / 2)) * Ch :=
            mul_le_mul_of_nonneg_left (hCh α x) (Real.rpow_nonneg hlam.le _)
          _ = Ch * lam ^ (-(m / 2)) := by ring
      have hscale : 0 ≤ Ch * lam ^ (-(m / 2)) :=
        mul_nonneg hCh0 (Real.rpow_nonneg hlam.le _)
      have hs := sq_le_sq'
        (le_trans (neg_nonpos.mpr hscale) (abs_nonneg (ψ α x))) habs
      have hpow : (lam ^ (-(m / 2))) ^ 2 = lam ^ (-m) := by
        rw [← neg_div, rpow_half_sq (-m) lam hlam]
      rw [sq_abs, mul_pow, hpow] at hs
      nlinarith [hCh0, sq_nonneg Ch, Real.rpow_nonneg hlam.le (-m)]
    calc
      _ ≤ ∫ _x : Euc p.d, Ch ^ 2 * lam ^ (-m) ∂(r26t3_mu R t) :=
        integral_mono (hInt α) (integrable_const _) (fun x => hsqbound x)
      _ = Ch ^ 2 * lam ^ (-m) := by simp
  have hmode : ∀ α : MultiIndex p.d,
      ‖fp81s21_combinedFeature p R hK t (ψ α)‖ ^ 2 ≤
        (Kcov * Ch ^ 2) * oscEigenvalue p.d α ^ (-m) := by
    intro α
    have hgram := fp81s21_combinedFeature_gram p hδ
      (hδle.trans hδ0half) R hK ht ht (hψtest α) (hψtest α)
    have hcov := hCov t t ht ht (ψ α) (ψ α) (hψtest α) (hψtest α)
    have hI : 0 ≤ ∫ x, (ψ α x) ^ 2 ∂(r26t3_mu R t) :=
      integral_nonneg fun _ => sq_nonneg _
    have hroot :
        Real.sqrt (∫ x, (ψ α x) ^ 2 ∂(r26t3_mu R t)) ^ 2 =
          ∫ x, (ψ α x) ^ 2 ∂(r26t3_mu R t) := Real.sq_sqrt hI
    have hdiag :
        ‖fp81s21_combinedFeature p R hK t (ψ α)‖ ^ 2 ≤
          Kcov * ∫ x, (ψ α x) ^ 2 ∂(r26t3_mu R t) := by
      calc
        _ = HRS.MS.S21E.s21eCov p.d p.s p.a p.β p.γ R.ρ t t (ψ α) (ψ α) := by
          rw [← real_inner_self_eq_norm_sq, hgram]
        _ ≤ |HRS.MS.S21E.s21eCov p.d p.s p.a p.β p.γ R.ρ t t (ψ α) (ψ α)| := le_abs_self _
        _ ≤ Kcov * Real.sqrt (∫ x, (ψ α x) ^ 2 ∂(r26t3_mu R t)) *
              Real.sqrt (∫ x, (ψ α x) ^ 2 ∂(r26t3_mu R t)) := hcov
        _ = Kcov * ∫ x, (ψ α x) ^ 2 ∂(r26t3_mu R t) := by
          calc
            _ = Kcov * (Real.sqrt (∫ x, (ψ α x) ^ 2 ∂(r26t3_mu R t)) *
                Real.sqrt (∫ x, (ψ α x) ^ 2 ∂(r26t3_mu R t))) := by ring
            _ = _ := by rw [Real.mul_self_sqrt hI]
    calc
      _ ≤ Kcov * (Ch ^ 2 * oscEigenvalue p.d α ^ (-m)) :=
        le_trans hdiag (mul_le_mul_of_nonneg_left (hIntBound α) hKcov)
      _ = (Kcov * Ch ^ 2) * oscEigenvalue p.d α ^ (-m) := by ring
  have hmajor : Summable (fun α : MultiIndex p.d =>
      (Kcov * Ch ^ 2) * oscEigenvalue p.d α ^ (-m)) := hsumlam.mul_left _
  have hfeature : Summable (fun α : MultiIndex p.d =>
      ‖fp81s21_combinedFeature p R hK t (ψ α)‖ ^ 2) :=
    Summable.of_nonneg_of_le (fun α => sq_nonneg _) hmode hmajor
  refine ⟨hfeature, ?_⟩
  calc
    _ ≤ ∑' α : MultiIndex p.d,
        (Kcov * Ch ^ 2) * oscEigenvalue p.d α ^ (-m) :=
      hfeature.tsum_le_tsum hmode hmajor
    _ = Kcov * Ch ^ 2 * (∑' α : MultiIndex p.d,
          oscEigenvalue p.d α ^ (-m)) := by rw [tsum_mul_left]
    _ = V := by rfl

#print axioms fp81s21_combinedFeature_trace

end HRS.Fp81.S21

end
