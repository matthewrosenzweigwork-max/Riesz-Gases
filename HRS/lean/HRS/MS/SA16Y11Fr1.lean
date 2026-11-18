import HRS.MS.SA16Y5Ex2f

/-!
# S.A.16 (SA16Y11) Fr1: the fractional-order nonlocal operator of a SIGNED density, linear bound (`d-1 < s < d`, iso/hilbert matrices)

`sa16y11f_exists`: for `M = -(lam•1) + A` (`A` skew, `|M i j| ≤ MB`) and a smooth `a` with `sa16z_Cb (m+2) Λ a` (no positivity, no fractional-force term)
there is `T : W^{m+2,p} → W^{m,p}` with `SA16FOp d m p s M a T` and `‖T‖ ≤ K Λ`, `K = K(d,m,s,p,MB)`.
This is the existence part of `sa16y5f_Hex_iso/_hilb` (from `sa16y3_extend`, `sa16y3_extendA`) without the energy clause and with the bound LINEAR in `Λ`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer
open HRS.Whole.AppendixA.Phase2SA16Q

section Fr1
variable {d : ℕ}

set_option maxHeartbeats 6400000 in
theorem sa16y11f_exists (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (hs1 : (d : ℝ) - 1 < s)
    {p : ℝ} [Fact (2 ≤ p)] (m : ℕ) (MB : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {M : Matrix (Fin d) (Fin d) ℝ},
      (∃ lam : ℝ, 0 ≤ lam ∧ ∃ A : Matrix (Fin d) (Fin d) ℝ, A.transpose = -A ∧
        M = -(lam • (1 : Matrix (Fin d) (Fin d) ℝ)) + A) →
      (∀ i j, |M i j| ≤ MB) → ∀ {a : Euc d → ℝ}, ContDiff ℝ ∞ a → ∀ {Λ : ℝ}, 0 ≤ Λ → sa16z_Cb (m + 2) Λ a →
      ∃ T : WmpSpace d (m + 1 + 1) p →L[ℝ] WmpSpace d m p, SA16FOp d m p s M a T ∧ ‖T‖ ≤ K * Λ := by
  have hθ1 : 1 < s + 2 - d := by linarith
  obtain ⟨K1, hK10, hK1⟩ := sa16y3_extend (s := s) (p := p) hd hs0 hsd hθ1 m
  obtain ⟨K2, hK20, hK2⟩ := sa16y3_extendA (s := s) (p := p) hd hs0 hsd hθ1 m
  refine ⟨max MB 0 * K1 + K2 * max MB 0, by positivity, ?_⟩
  intro M hMC hM a ha Λ hΛ hCb
  obtain ⟨lam, hlam, A, hskew, hMl⟩ := hMC
  have hAii : ∀ i, A i i = 0 := fun i => by
    have := congrFun (congrFun hskew i) i
    simp only [Matrix.transpose_apply, Matrix.neg_apply] at this
    linarith
  have hlamMB : lam ≤ max MB 0 := by
    have h := hM ⟨0, by omega⟩ ⟨0, by omega⟩
    rw [hMl] at h
    have h' : lam ≤ MB := by simpa [hAii, abs_of_nonneg hlam] using h
    exact h'.trans (le_max_left _ _)
  have hA : ∀ i j, |A i j| ≤ max MB 0 := by
    intro i j
    by_cases h : i = j
    · subst h; rw [hAii]; simp
    · have h1 := hM i j
      rw [hMl] at h1
      have : |A i j| ≤ MB := by simpa [Matrix.one_apply, h] using h1
      exact this.trans (le_max_left _ _)
  obtain ⟨T, hT, hTc⟩ := hK1 ha hΛ hCb
  obtain ⟨TA, hTA, hTAj⟩ := hK2 (A := A) (AB := max MB 0) (le_max_right _ _) hA hskew ha hΛ hCb
  have hTj := fun φ => (hTc φ).2
  refine ⟨(-lam) • T + TA, ?_, ?_⟩
  · intro φ
    filter_upwards [sa16r_wrep_add d m p (((-lam) • T) (sa16r_Jcc d (m + 1 + 1) p φ))
        (TA (sa16r_Jcc d (m + 1 + 1) p φ)),
      sa16r_wrep_smul d m p (-lam) (T (sa16r_Jcc d (m + 1 + 1) p φ)),
      sa16y5f_wrep_of_jets _ (hTj φ), sa16y5f_wrep_of_jets _ (hTAj φ)] with x e1 e2 e3 e4
    rw [ContinuousLinearMap.add_apply, e1]
    have e2' : wrep d m p (((-lam) • T) (sa16r_Jcc d (m + 1 + 1) p φ)) x =
        -lam * wrep d m p (T (sa16r_Jcc d (m + 1 + 1) p φ)) x := by
      rw [ContinuousLinearMap.smul_apply]; exact e2
    rw [e2', e3, e4, hMl, sa16y3_eucNonlocal_split (s := s) lam A a φ.1 x]
    ring
  · calc ‖(-lam) • T + TA‖ ≤ ‖(-lam) • T‖ + ‖TA‖ := ContinuousLinearMap.opNorm_add_le _ _
      _ ≤ max MB 0 * (K1 * Λ) + K2 * (max MB 0 * Λ) := by
          refine add_le_add ?_ hTA
          calc ‖(-lam) • T‖ ≤ ‖-lam‖ * ‖T‖ := ContinuousLinearMap.opNorm_smul_le _ _
            _ = lam * ‖T‖ := by rw [Real.norm_eq_abs, abs_neg, abs_of_nonneg hlam]
            _ ≤ max MB 0 * (K1 * Λ) :=
                mul_le_mul hlamMB hT (ContinuousLinearMap.opNorm_nonneg _) (le_max_right _ _)
      _ = (max MB 0 * K1 + K2 * max MB 0) * Λ := by ring

end Fr1

end HRS.Whole.AppendixA.Phase2SA16R

end
