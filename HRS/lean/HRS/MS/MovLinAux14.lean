import HRS.MS.MovLinAux13

/-!
# MOV-LIN, part 5: from short-time smoothing and `L²` decay to `MovSmoothingBounds`

Namespace `HRS.MS.MovLin`, helpers `movlin_`.  Infrastructure for S6.2 (`W:lem:r2mov-linear`); not a manuscript row.
-/

noncomputable section

open MeasureTheory Filter Topology Finset
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MovLin

open HRS HRS.Whole HRS.MS.MovOsc HRS.MS.MovC1

variable {d : ℕ}

section Abstract

variable {ρ : Euc d → ℝ}

set_option maxHeartbeats 1000000 in
/-- Decay at a level `r ≥ 0`. -/
lemma movlin_dec_level (U : ℝ → (MovL2Zero ρ →L[ℝ] MovL2Zero ρ)) (lam C0 : ℝ) (hlam : 0 < lam)
    (hC0 : 1 ≤ C0) (hU0 : U 0 = 1) (hadd : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → U (a + b) = U a * U b)
    (hdec : ∀ t : ℝ, 0 ≤ t → ∀ v : MovL2Zero ρ, ‖U t v‖ ≤ C0 * Real.exp (-lam * t) * ‖v‖)
    (Hs : HsOK U) {r : ℝ} (hr : 0 ≤ r) :
    ∃ Cr : ℝ, 0 ≤ Cr ∧ ∀ t : ℝ, 0 ≤ t → ∀ v : MovL2Zero ρ, MemOsc r (movFun v) →
      MemOsc r (movFun (U t v)) ∧
        oscNorm r (movFun (U t v)) ≤ Cr * Real.exp (-lam * t) * oscNorm r (movFun v) := by
  obtain ⟨C1, hC1, h1⟩ := Hs r r hr le_rfl
  obtain ⟨C2, hC2, h2⟩ := Hs 0 r le_rfl hr
  set N : ℝ := max C1 1 with hN
  have hN1 : 1 ≤ N := le_max_right _ _
  have hN0 : 0 ≤ N := by linarith
  have hnn : ∀ (r' : ℝ) (f : Euc d → ℝ), 0 ≤ oscNorm r' f := HRS.MS.MovC1.movc1_osc_nonneg
  -- short times
  have hsmall : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ v : MovL2Zero ρ, MemOsc r (movFun v) →
      MemOsc r (movFun (U t v)) ∧ oscNorm r (movFun (U t v)) ≤ N * oscNorm r (movFun v) := by
    intro t ht v hv
    rcases ht.1.eq_or_lt with h0 | hpos
    · subst h0
      rw [hU0]
      exact ⟨hv, by
        show oscNorm r (movFun v) ≤ N * oscNorm r (movFun v)
        exact le_mul_of_one_le_left (hnn _ _) hN1⟩
    · obtain ⟨hm, hb⟩ := h1 t ⟨hpos, ht.2⟩ v hv
      refine ⟨hm, hb.trans ?_⟩
      simp only [sub_self, zero_div, neg_zero, Real.rpow_zero, mul_one]
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) (hnn _ _)
  -- times in [0,2]
  have hmid : ∀ t ∈ Set.Icc (0 : ℝ) 2, ∀ v : MovL2Zero ρ, MemOsc r (movFun v) →
      MemOsc r (movFun (U t v)) ∧ oscNorm r (movFun (U t v)) ≤ N * N * oscNorm r (movFun v) := by
    intro t ht v hv
    have hh : t / 2 ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have e : U t = U (t / 2) * U (t / 2) := by
      rw [← hadd _ _ (by linarith [ht.1]) (by linarith [ht.1])]; congr 1; ring
    obtain ⟨m1, b1⟩ := hsmall _ hh v hv
    obtain ⟨m2, b2⟩ := hsmall _ hh _ m1
    rw [e]
    refine ⟨m2, b2.trans ?_⟩
    calc N * oscNorm r (movFun (U (t / 2) v)) ≤ N * (N * oscNorm r (movFun v)) :=
          mul_le_mul_of_nonneg_left b1 hN0
      _ = N * N * oscNorm r (movFun v) := by ring
  -- large times
  have hlarge : ∀ t : ℝ, 2 ≤ t → ∀ v : MovL2Zero ρ, MemOsc r (movFun v) →
      MemOsc r (movFun (U t v)) ∧
        oscNorm r (movFun (U t v)) ≤ C2 * C0 * N * Real.exp (2 * lam) * Real.exp (-lam * t) * oscNorm r (movFun v) := by
    intro t ht v hv
    obtain ⟨m1, b1⟩ := hsmall 1 ⟨zero_le_one, le_rfl⟩ v hv
    have hL1 : ‖U 1 v‖ ≤ oscNorm r (movFun (U 1 v)) := by
      rw [← (movlin_norm_osc0 (U 1 v)).2]
      exact (mo_mono hr m1).2
    have hL2 : ‖U (t - 2) (U 1 v)‖ ≤ C0 * Real.exp (-lam * (t - 2)) * ‖U 1 v‖ :=
      hdec _ (by linarith) _
    obtain ⟨m3, b3⟩ := h2 1 ⟨zero_lt_one, le_rfl⟩ (U (t - 2) (U 1 v)) (movlin_norm_osc0 _).1
    have e : U t = U 1 * (U (t - 2) * U 1) := by
      rw [← hadd (t - 2) 1 (by linarith) zero_le_one, ← hadd 1 (t - 2 + 1) zero_le_one (by linarith)]
      congr 1; ring
    have hm : U t v = U 1 (U (t - 2) (U 1 v)) := by
      rw [e, ContinuousLinearMap.mul_apply, ContinuousLinearMap.mul_apply]
    rw [hm]
    refine ⟨m3, ?_⟩
    simp only [Real.one_rpow, mul_one] at b3
    rw [(movlin_norm_osc0 (U (t - 2) (U 1 v))).2] at b3
    have hexp : Real.exp (-lam * (t - 2)) = Real.exp (2 * lam) * Real.exp (-lam * t) := by
      rw [← Real.exp_add]; congr 1; ring
    calc oscNorm r (movFun (U 1 (U (t - 2) (U 1 v)))) ≤ C2 * ‖U (t - 2) (U 1 v)‖ := b3
      _ ≤ C2 * (C0 * Real.exp (-lam * (t - 2)) * ‖U 1 v‖) := mul_le_mul_of_nonneg_left hL2 hC2
      _ ≤ C2 * (C0 * Real.exp (-lam * (t - 2)) * (N * oscNorm r (movFun v))) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hL1.trans b1) (by positivity)) hC2
      _ = C2 * C0 * N * Real.exp (2 * lam) * Real.exp (-lam * t) * oscNorm r (movFun v) := by
          rw [hexp]; ring
  refine ⟨N * N * Real.exp (2 * lam) + C2 * C0 * N * Real.exp (2 * lam), by positivity, fun t ht v hv => ?_⟩
  by_cases h2t : t ≤ 2
  · obtain ⟨m, b⟩ := hmid t ⟨ht, h2t⟩ v hv
    refine ⟨m, b.trans ?_⟩
    have hge : 1 ≤ Real.exp (2 * lam) * Real.exp (-lam * t) := by
      rw [← Real.exp_add]; exact Real.one_le_exp (by nlinarith)
    have h0 := hnn r (movFun v)
    calc N * N * oscNorm r (movFun v) ≤ N * N * (Real.exp (2 * lam) * Real.exp (-lam * t)) * oscNorm r (movFun v) :=
          by nlinarith [mul_nonneg hN0 hN0, mul_nonneg (mul_nonneg hN0 hN0) h0]
      _ ≤ (N * N * Real.exp (2 * lam) + C2 * C0 * N * Real.exp (2 * lam)) * Real.exp (-lam * t) * oscNorm r (movFun v) := by
          have h3 : 0 ≤ C2 * C0 * N * Real.exp (2 * lam) * Real.exp (-lam * t) * oscNorm r (movFun v) := by positivity
          nlinarith
  · push_neg at h2t
    obtain ⟨m, b⟩ := hlarge t h2t.le v hv
    refine ⟨m, b.trans ?_⟩
    have h0 := hnn r (movFun v)
    have h3 : 0 ≤ N * N * Real.exp (2 * lam) * Real.exp (-lam * t) * oscNorm r (movFun v) := by positivity
    nlinarith

set_option maxHeartbeats 1000000 in
/-- **From decay and short-time smoothing to `MovSmoothingBounds`** (for every `m ≥ a`). -/
theorem movlin_abstract (s : ℝ) (U : ℝ → (MovL2Zero ρ →L[ℝ] MovL2Zero ρ)) (lam C0 : ℝ) (hlam : 0 < lam)
    (hC0 : 1 ≤ C0) (hU0 : U 0 = 1) (hadd : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → U (a + b) = U a * U b)
    (hdec : ∀ t : ℝ, 0 ≤ t → ∀ v : MovL2Zero ρ, ‖U t v‖ ≤ C0 * Real.exp (-lam * t) * ‖v‖)
    (Hs : HsOK U) {m : ℝ} (hm : movA d s ≤ m) :
    ∃ C : ℝ, MovSmoothingBounds d s ρ m lam C U := by
  have ha1 : 1 ≤ movA d s := le_max_left _ _
  have hm0 : 0 ≤ m := by linarith
  have hma0 : 0 ≤ m - movA d s := by linarith
  have hnn : ∀ (r' : ℝ) (f : Euc d → ℝ), 0 ≤ oscNorm r' f := HRS.MS.MovC1.movc1_osc_nonneg
  obtain ⟨Cm, hCm0, hCm⟩ := movlin_dec_level U lam C0 hlam hC0 hU0 hadd hdec Hs hm0
  obtain ⟨Cn, hCn0, hCn⟩ := movlin_dec_level U lam C0 hlam hC0 hU0 hadd hdec Hs hma0
  obtain ⟨C3, hC30, hC3⟩ := Hs (m - movA d s) m hma0 (by linarith)
  have hexp : (-((m - (m - movA d s)) / 2)) = -(movA d s) / 2 := by ring
  rw [hexp] at hC3
  refine ⟨max (max Cm (C3 * Real.exp lam)) (C3 * Cn * Real.exp lam), ?_, ?_⟩
  · intro t ht v hv
    obtain ⟨h1, h2⟩ := hCm t ht v hv
    refine ⟨h1, h2.trans ?_⟩
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      ((le_max_left _ _).trans (le_max_left _ _)) (Real.exp_pos _).le) (hnn _ _)
  · intro t ht v hv
    set C : ℝ := max (max Cm (C3 * Real.exp lam)) (C3 * Cn * Real.exp lam) with hC
    have hC1 : C3 * Real.exp lam ≤ C := (le_max_right _ _).trans (le_max_left _ _)
    have hC2 : C3 * Cn * Real.exp lam ≤ C := le_max_right _ _
    have hrp : 0 ≤ t ^ (-(movA d s) / 2) := Real.rpow_nonneg ht.le _
    have h0 := hnn (m - movA d s) (movFun v)
    by_cases h1t : t ≤ 1
    · obtain ⟨h1, h2⟩ := hC3 t ⟨ht, h1t⟩ v hv
      refine ⟨h1, h2.trans ?_⟩
      have hge : Real.exp lam * Real.exp (-lam * t) ≥ 1 := by
        rw [← Real.exp_add]; exact Real.one_le_exp (by nlinarith)
      have hE := (Real.exp_pos (-lam * t)).le
      calc C3 * t ^ (-(movA d s) / 2) * oscNorm (m - movA d s) (movFun v)
          ≤ C3 * Real.exp lam * Real.exp (-lam * t) * t ^ (-(movA d s) / 2) * oscNorm (m - movA d s) (movFun v) := by
            have : C3 * t ^ (-(movA d s) / 2) ≤ C3 * Real.exp lam * Real.exp (-lam * t) * t ^ (-(movA d s) / 2) := by
              have := mul_le_mul_of_nonneg_left hge (mul_nonneg hC30 hrp)
              nlinarith
            exact mul_le_mul_of_nonneg_right this h0
        _ ≤ C * (1 + t ^ (-(movA d s) / 2)) * Real.exp (-lam * t) * oscNorm (m - movA d s) (movFun v) := by
            have hCe : 0 ≤ C := (mul_nonneg hC30 (Real.exp_pos _).le).trans hC1
            have h4 : C3 * Real.exp lam * Real.exp (-lam * t) * t ^ (-(movA d s) / 2) ≤
                C * (1 + t ^ (-(movA d s) / 2)) * Real.exp (-lam * t) := by
              have h5 : C3 * Real.exp lam * t ^ (-(movA d s) / 2) ≤ C * (1 + t ^ (-(movA d s) / 2)) := by
                nlinarith [mul_le_mul_of_nonneg_right hC1 hrp]
              nlinarith [mul_le_mul_of_nonneg_right h5 hE]
            exact mul_le_mul_of_nonneg_right h4 h0
    · push_neg at h1t
      obtain ⟨hw1, hw2⟩ := hCn (t - 1) (by linarith) v hv
      have e : U t = U 1 * U (t - 1) := by
        rw [← hadd 1 (t - 1) zero_le_one (by linarith)]; congr 1; ring
      obtain ⟨h1, h2⟩ := hC3 1 ⟨zero_lt_one, le_rfl⟩ (U (t - 1) v) hw1
      rw [e]
      simp only [ContinuousLinearMap.mul_apply]
      refine ⟨h1, h2.trans ?_⟩
      simp only [Real.one_rpow, mul_one]
      have hexp2 : Real.exp (-lam * (t - 1)) = Real.exp lam * Real.exp (-lam * t) := by
        rw [← Real.exp_add]; congr 1; ring
      have hE := (Real.exp_pos (-lam * t)).le
      calc C3 * oscNorm (m - movA d s) (movFun (U (t - 1) v))
          ≤ C3 * (Cn * Real.exp (-lam * (t - 1)) * oscNorm (m - movA d s) (movFun v)) :=
            mul_le_mul_of_nonneg_left hw2 hC30
        _ = C3 * Cn * Real.exp lam * Real.exp (-lam * t) * oscNorm (m - movA d s) (movFun v) := by
            rw [hexp2]; ring
        _ ≤ C * (1 + t ^ (-(movA d s) / 2)) * Real.exp (-lam * t) * oscNorm (m - movA d s) (movFun v) := by
            have hCe : 0 ≤ C := (mul_nonneg (mul_nonneg hC30 hCn0) (Real.exp_pos _).le).trans hC2
            have h4 : C3 * Cn * Real.exp lam * Real.exp (-lam * t) ≤ C * (1 + t ^ (-(movA d s) / 2)) * Real.exp (-lam * t) := by
              refine mul_le_mul_of_nonneg_right ?_ hE
              nlinarith [mul_nonneg hCe hrp]
            exact mul_le_mul_of_nonneg_right h4 h0

end Abstract

end HRS.MS.MovLin
