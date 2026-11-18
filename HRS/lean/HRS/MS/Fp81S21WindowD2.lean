import HRS.MS.Fp81S21WindowD

/-!
# S2.1(iii): cancellation of the window feature's terminal coordinate

Pairing with the shifted P vector and the time-localized Q vector recovers the
propagated observation. The strict cutoff in the feature's B coordinate is
used together with the inclusive terminal identity at the diagonal.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Fp81.S21

open HRS (Euc)
open HRS.Whole HRS.MS.CovMeas

variable {d : ℕ}

/-- Complete P/Q cancellation for the observation-window feature. The B slot
is supported on `a < v`; the evaluation cutoff is inclusive at `v = a+t`.
-/
theorem fp81s21_window_feature_B_cancellation
    (hd : 1 ≤ d) {C : WholeCoeff d} {m H a : ℝ} {r : ℕ}
    (hH : 0 < H) (ha : 0 ≤ a)
    (horb : R2OrbitSummable C m (a + H) r)
    (hterminal : ∀ v ∈ Icc (0 : ℝ) (a + H), ∀ β : MultiIndex d, ∀ y : Euc d,
      propagatorW C v v (oscTestFun m β) y = oscTestFun m β y)
    {v : ℝ} (hv : v ∈ Icc (0 : ℝ) (a + H))
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) H)
    (x : Euc d) (α : MultiIndex d) :
    inner ℝ (fp81s21_window_feature C m H a v x)
        (s101P m H t α + (if v ≤ a + t then s101Q m H α else 0)) =
      if v ≤ a + t then propagatorW C v (a + t) (oscTestFun m α) x else 0 := by
  obtain ⟨cData, hD⟩ := s101_data_of_horb hd horb
  have hrec := fp81s21_window_feature_reconstruct_y1_of_data
    (x := x) (α := α) hD ha hH.le hv (hterminal v hv) ht
  have hY : inner ℝ (fp81s21_window_feature C m H a v x)
      (s101P m H t α + s101Q m H α) =
      inner ℝ (fp81s21_window_feature C m H a v x)
        (HRS.MS.S52.s52y1 m H t α) := by
    have hΓ : fp81s21_window_feature C m H a v x =
        KSpace.mk (fp81s21_window_feature C m H a v x).A₀
          (fp81s21_window_feature C m H a v x).A'
          (fp81s21_window_feature C m H a v x).B := rfl
    have he : HRS.MS.S52.s52e m α = s101e m α := rfl
    rw [inner_add_right, hΓ, s101P, s101_inner_mk,
      s101Q, s101_inner_mk, hΓ, HRS.MS.S52.s52y1,
      HRS.MS.S52.s52_inner_mk, HRS.MS.S52.s52_mk_A₀,
      HRS.MS.S52.s52_mk_A', HRS.MS.S52.s52_mk_B]
    rw [s101Ind, he]
    simp only [inner_zero_right, zero_add]
    rw [inner_neg_right]
    simp only [HRS.MS.S52.s52_mk_A₀, HRS.MS.S52.s52_mk_A']
    ring
  have hBmem : Memℓp (fun β : MultiIndex d =>
      if a < v then oscTestFun m β x else 0) 2 := by
    apply s101_memℓp_of_bound hD.summable
    intro β
    by_cases hav : a < v
    · have hb := hD.bddU β v hv v ⟨le_rfl, hv.2⟩ 0 (by norm_num) x
      have habs : |oscTestFun m β x| ≤ cData β := by
        rw [← hterminal v hv β x]
        simpa only [norm_iteratedFDeriv_zero, Real.norm_eq_abs] using hb
      simpa [hav] using habs
    · simpa [hav] using hD.nonneg β
  have hQ : inner ℝ (fp81s21_window_feature C m H a v x) (s101Q m H α) =
      if a < v then oscTestFun m α x else 0 := by
    have hΓ : fp81s21_window_feature C m H a v x =
        KSpace.mk (fp81s21_window_feature C m H a v x).A₀
          (fp81s21_window_feature C m H a v x).A'
          (fp81s21_window_feature C m H a v x).B := rfl
    rw [hΓ, s101Q, s101_inner_mk]
    simp only [inner_zero_right, zero_add]
    exact fp81s21_window_feature_B_coord hBmem α
  by_cases hcut : v ≤ a + t
  · have hfull : inner ℝ (fp81s21_window_feature C m H a v x)
        (s101P m H t α + s101Q m H α) =
        propagatorW C v (a + t) (oscTestFun m α) x := by
      rw [hY, hrec]
      simp [hcut]
    simpa [hcut] using hfull
  · have hav : a < v := by
      have : a + t < v := lt_of_not_ge hcut
      linarith [ht.1]
    have hsum : inner ℝ (fp81s21_window_feature C m H a v x)
        (s101P m H t α) +
          inner ℝ (fp81s21_window_feature C m H a v x) (s101Q m H α) =
        oscTestFun m α x := by
      rw [← inner_add_right, hY, hrec]
      simp [hcut]
    have hPzero : inner ℝ (fp81s21_window_feature C m H a v x)
        (s101P m H t α) = 0 := by
      rw [hQ, if_pos hav] at hsum
      linarith
    simp [hcut, hPzero]

#print axioms fp81s21_window_feature_B_cancellation

end HRS.Fp81.S21

end
