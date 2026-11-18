import HRS.MS.Fp81S21InitialFR2

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace ContDiff

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000
noncomputable section

namespace HRS.Fp81.S21

open S99
open HRS.Whole
open HRS (Euc MemCb cbNorm)
open HRS.MS.R26T3

/-! The finite-rank response coefficients of the actual initial law admit the same
double-series rearrangement as in `S99.s99_FR`. This step uses only summability of
the actual susceptibility coefficients and the bounded second derivatives of the
test; no thermal-law identity is involved. -/

/-- Exchange the actual finite-rank `Qk` series with the two finite sums in the
kernel, using absolute summability of each actual susceptibility coefficient. -/
theorem fp81s21_initial_Qk_series
    {p : Parameters} {δ : ℝ} {R : Trajectory p δ}
    (E : InitialSteinEnv R) {φ : ℕ → Euc p.d → ℝ}
    (hφ : IsSummableFeatureFamily (fp81s21_J1 p.d) φ)
    (F : InitialFamData R φ)
    {G : Measure SeqL2} [IsProbabilityMeasure G]
    {m : ℕ} {cc : Fin m → Fin m → ℝ} {u : Fin m → Euc p.d → ℝ}
    (hcu : IsR2FiniteRankData cc u) {ψ : SeqL2 → ℝ} (hψ : S99.Bd 4 ψ) :
    ∑' l, ∑' q,
        fp81s21_initial_Qk R φ (r2FiniteRankKernel cc u) l q *
          ∫ z, S99.pd (S99.pd ψ l) q z ∂G =
      ∑ i, ∑ j, cc i j * ∑' l, ∑' q,
        fp81s21_initial_kap (R := R) (u i) φ l *
          fp81s21_initial_kap (R := R) (u j) φ q *
            ∫ z, S99.pd (S99.pd ψ l) q z ∂G := by
  have hcb : ∀ i, MemCb (fp81s21_J1 p.d) (u i) := fun i =>
    S99.s99_cb_of_cinf (hcu.smooth i) (hcu.compactSupport i) _
  have hsumκ : ∀ i, Summable fun l =>
      |fp81s21_initial_kap (R := R) (u i) φ l| := fun i =>
    fp81s21_initial_kap_summable E hφ F (hcb i)
  let Gm : ℕ → ℕ → ℝ := fun l q =>
    ∫ z, S99.pd (S99.pd ψ l) q z ∂G
  have hGb : ∀ l q, |Gm l q| ≤ 1 := by
    intro l q
    have h := norm_integral_le_of_norm_le_const (μ := G)
      (f := S99.pd (S99.pd ψ l) q) (C := 1)
      (Filter.Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs]
        exact ((hψ.pd l).pd q).abs_le z)
    simpa [Gm, Real.norm_eq_abs] using h
  have hQ : ∀ l q,
      fp81s21_initial_Qk R φ (r2FiniteRankKernel cc u) l q =
        ∑ i, ∑ j, cc i j *
          (fp81s21_initial_kap (R := R) (u i) φ l *
            fp81s21_initial_kap (R := R) (u j) φ q) := by
    intro l q
    exact fp81s21_initial_Qk_finrank E F hcu l q
  calc
    _ = ∑' l, ∑' q,
          (∑ i, ∑ j, cc i j *
            (fp81s21_initial_kap (R := R) (u i) φ l *
              fp81s21_initial_kap (R := R) (u j) φ q)) * Gm l q := by
        congr 1
        funext l
        congr 1
        funext q
        rw [hQ l q]
    _ = ∑ i, ∑ j, cc i j * ∑' l, ∑' q,
          fp81s21_initial_kap (R := R) (u i) φ l *
            fp81s21_initial_kap (R := R) (u j) φ q * Gm l q :=
      S99.s99_tsum2_finsum cc
        (fun i l => fp81s21_initial_kap (R := R) (u i) φ l)
        (fun j q => fp81s21_initial_kap (R := R) (u j) φ q)
        Gm hsumκ hsumκ hGb

#print axioms fp81s21_initial_Qk_series

end HRS.Fp81.S21

end
