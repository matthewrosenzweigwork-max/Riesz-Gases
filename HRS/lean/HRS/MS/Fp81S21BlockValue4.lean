import HRS.MS.Fp81S21BlockValue3

/-!
# S2.1(iii), packet 15d-4: shifted evaluation interface

This file states the window evaluation predicate with its exact shifted
physical cutoffs, and extends the existing basis-vector B-cancellation to
the finite observation combinations used by that predicate.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
noncomputable section

open MeasureTheory Filter Topology Set Classical
open scoped ENNReal NNReal BigOperators

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.Uniform HRS.Uniform.Q45 HRS.MS.CovMeas HRS.MS.GenPath

variable {d : ℕ}

/-- Window version of `IsR2JValue`: the observation horizon is `[0,H]`,
while evaluations of the propagator and the physical integration cutoff are
shifted by the observation start `a`. -/
def fp81s21_IsWindowJValue (C : WholeCoeff d) (m H a : ℝ)
    (z : ℝ → (Euc d → ℝ) → ℝ) (I : Set ℝ)
    (J : TensorDual (OscPath d m H) 2) : Prop :=
  J ∈ projTensor (OscPath d m H) 2 ∧
    ∀ (ta tb : ℝ) (φa φb : Euc d → ℝ)
      (l₁ l₂ : StrongDual ℝ (OscPath d m H)),
      IsR2DualCombo m φa → IsR2DualCombo m φb →
      ta ∈ Icc (0 : ℝ) H → tb ∈ Icc (0 : ℝ) H →
      (∀ w, l₁ w = OscDual.eval (r2PathAt w ta) φa) →
      (∀ w, l₂ w = OscDual.eval (r2PathAt w tb) φb) →
      J ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 2) ℝ).compContinuousLinearMap ![l₁, l₂]) =
        2 * C.ν * ∫ v in I ∩ Icc (0 : ℝ) (min (a + ta) (a + tb)),
          z v (fun x => inner ℝ
            (gradient (propagatorW C v (a + ta) φa) x)
            (gradient (propagatorW C v (a + tb) φb) x))

/-- B-cancellation for a finite combination of the basic observation tests.
The linearity hypothesis for the choice-defined propagator is an explicit,
separate binder. -/
theorem fp81s21_window_feature_B_cancellation_combo
    (hd : 1 ≤ d) {C : WholeCoeff d} {m H a : ℝ} {r : ℕ}
    (hH : 0 < H) (ha : 0 ≤ a)
    (horb : R2OrbitSummable C m (a + H) r)
    (hterminal : ∀ v ∈ Icc (0 : ℝ) (a + H), ∀ α : MultiIndex d, ∀ x : Euc d,
      propagatorW C v v (oscTestFun m α) x = oscTestFun m α x)
    (hlin : ∀ u t : ℝ, 0 ≤ u → u ≤ t → t ≤ a + H →
      ∀ φ ψ : Euc d → ℝ, ∀ c : ℝ,
        IsR2DualCombo m φ → IsR2DualCombo m ψ →
        propagatorW C u t (φ + c • ψ) = propagatorW C u t φ + c • propagatorW C u t ψ)
    {v : ℝ} (hv : v ∈ Icc (0 : ℝ) (a + H))
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) H)
    (S : Finset (MultiIndex d)) (c : MultiIndex d → ℝ) (x : Euc d) :
    inner ℝ (fp81s21_window_feature C m H a v x)
        (s101Pc m H t S c +
          (if v ≤ a + t then s101Qc m H S c else 0)) =
      if v ≤ a + t then
        propagatorW C v (a + t)
          (fun y => ∑ α ∈ S, c α * oscTestFun m α y) x
      else 0 := by
  let Γ := fp81s21_window_feature C m H a v x
  have hbasic (α : MultiIndex d) :
      inner ℝ Γ (s101P m H t α +
        (if v ≤ a + t then s101Q m H α else 0)) =
        if v ≤ a + t then propagatorW C v (a + t) (oscTestFun m α) x else 0 := by
    simpa [Γ] using fp81s21_window_feature_B_cancellation
      hd hH ha horb hterminal hv ht x α
  have hvec : s101Pc m H t S c +
      (if v ≤ a + t then s101Qc m H S c else 0) =
      ∑ α ∈ S, c α •
        (s101P m H t α + (if v ≤ a + t then s101Q m H α else 0)) := by
    by_cases hcut : v ≤ a + t
    · simp only [if_pos hcut]
      unfold s101Pc s101Qc
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro α hα
      rw [smul_add]
    · simp only [if_neg hcut]
      unfold s101Pc
      calc
        (∑ α ∈ S, c α • s101P m H t α) + 0 =
            ∑ α ∈ S, c α • s101P m H t α := by simp
        _ = ∑ α ∈ S, c α • (s101P m H t α + 0) := by
          apply Finset.sum_congr rfl
          intro α hα
          simp
  rw [hvec, inner_sum]
  simp only [inner_smul_right]
  change (∑ α ∈ S, c α * inner ℝ Γ
      (s101P m H t α + (if v ≤ a + t then s101Q m H α else 0))) = _
  have hsum :
      (∑ α ∈ S, c α * inner ℝ Γ
        (s101P m H t α + (if v ≤ a + t then s101Q m H α else 0))) =
      ∑ α ∈ S, c α * (if v ≤ a + t then
        propagatorW C v (a + t) (oscTestFun m α) x else 0) := by
    apply Finset.sum_congr rfl
    intro α hα
    rw [hbasic α]
  rw [hsum]
  by_cases hcut : v ≤ a + t
  · simp only [if_pos hcut]
    have hp := s101_prop_comb hlin hv.1 hcut (by linarith [ht.2]) S c
    rw [hp]
  · simp only [if_neg hcut]
    simp

#print axioms fp81s21_window_feature_B_cancellation_combo

end HRS.Fp81.S21

end
