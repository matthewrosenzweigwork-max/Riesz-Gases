import HRS.MS.R26T8AP11int

/-!
# S8.2 nonlocal layer: pole bound for the centre jets of the fibre function (P11e, part 3b, piece B1)
`r26t8a_loc_Fjet`: `‖D^j_y (y ↦ F(y+v,y))‖ <= c ‖v‖^(-s)` uniformly for `y` in a unit ball (the `y`-derivatives of `F(y+v,y)` are centre
derivatives of `midPair F`, which cost nothing).
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

theorem r26t8a_loc_Fjet (d : ℕ) (k b : ℕ) (M sigma : ℝ) (hM : 0 ≤ M) (hsd : sigma < d) (hd : 2 ≤ d) :
    ∃ s : ℝ, 0 < s ∧ s < d ∧ ∀ A : ℝ, 0 ≤ A → ∀ F : Euc d → Euc d → ℝ, Conormal k b M sigma A F →
      ∀ (y0 : Euc d) (j : ℕ), j ≤ k → ∃ c : ℝ, 0 ≤ c ∧ ∀ y : Euc d, ‖y - y0‖ ≤ 1 → ∀ v : Euc d, 0 < ‖v‖ → ‖v‖ ≤ 2 →
        ‖iteratedFDeriv ℝ j (fun y' : Euc d => F (y' + v) y') y‖ ≤ c * ‖v‖ ^ (-s) := by
  set sp : ℝ := max sigma 0 with hsp
  have hsp0 : 0 ≤ sp := le_max_right _ _
  have hspd : sp < d := max_lt hsd (by exact_mod_cast (by omega : 0 < d))
  set s : ℝ := sp + ((d : ℝ) - sp) / 2 with hs
  have hs0 : 0 < s := by rw [hs]; linarith
  have hsd' : s < d := by rw [hs]; linarith
  have hε : 0 < s - sp := by rw [hs]; linarith
  set Mm : ℝ := r26t8a_p06_M (s - sp) b with hMm
  have hMm0 : 0 ≤ Mm := by rw [hMm, r26t8a_p06_M]; have := hε; positivity
  refine ⟨s, hs0, hsd', ?_⟩
  intro A hA F hF y0 j hj
  -- envelope bound
  have hE : ∀ v : Euc d, 0 < ‖v‖ → ‖v‖ ≤ 2 →
      1 + (min 1 ‖v‖) ^ (-(sigma + ((0 : ℕ) : ℝ))) * (1 + |Real.log (min 1 ‖v‖)|) ^ b ≤
        (1 + Mm + 2 * 2 ^ s) * ‖v‖ ^ (-s) := by
    intro v hv hv2
    have hvs : 0 < ‖v‖ ^ (-s) := Real.rpow_pos_of_pos hv _
    have hL : 1 ≤ (1 + |Real.log (min 1 ‖v‖)|) ^ b :=
      one_le_pow₀ (by linarith [abs_nonneg (Real.log (min 1 ‖v‖))])
    rcases le_total ‖v‖ 1 with h1 | h1
    · rw [min_eq_right h1]
      simp only [Nat.cast_zero, add_zero]
      have hneg : (1 : ℝ) ≤ ‖v‖ ^ (-s) :=
        Real.one_le_rpow_of_pos_of_le_one_of_nonpos hv h1 (by linarith)
      have h2 : ‖v‖ ^ (-sigma) ≤ ‖v‖ ^ (-sp) :=
        Real.rpow_le_rpow_of_exponent_ge hv h1 (by rw [hsp]; linarith [le_max_left sigma 0])
      have h3 : ‖v‖ ^ (-sp) * (1 + |Real.log ‖v‖|) ^ b ≤ Mm * ‖v‖ ^ (-s) := by
        have := r26t8a_p06_slog b hε hv h1
        have e : ‖v‖ ^ (-sp) = ‖v‖ ^ (-s) * ‖v‖ ^ (s - sp) := by
          rw [← Real.rpow_add hv]; congr 1; ring
        calc ‖v‖ ^ (-sp) * (1 + |Real.log ‖v‖|) ^ b
            = ‖v‖ ^ (-s) * (‖v‖ ^ (s - sp) * (1 + |Real.log ‖v‖|) ^ b) := by rw [e]; ring
          _ ≤ ‖v‖ ^ (-s) * Mm := mul_le_mul_of_nonneg_left this hvs.le
          _ = Mm * ‖v‖ ^ (-s) := mul_comm _ _
      have h4 : ‖v‖ ^ (-sigma) * (1 + |Real.log ‖v‖|) ^ b ≤ Mm * ‖v‖ ^ (-s) :=
        (mul_le_mul_of_nonneg_right h2 (by positivity)).trans h3
      nlinarith [hneg, h4, mul_nonneg (by positivity : (0:ℝ) ≤ 2 * 2 ^ s) hvs.le]
    · rw [min_eq_left h1]
      simp only [Nat.cast_zero, add_zero, Real.one_rpow, Real.log_one, abs_zero, add_zero, one_pow, mul_one]
      have h5 : (2 : ℝ) ^ (-s) ≤ ‖v‖ ^ (-s) :=
        Real.rpow_le_rpow_of_nonpos hv hv2 (by linarith)
      have h6 : (2 : ℝ) ^ s * 2 ^ (-s) = 1 := by
        rw [← Real.rpow_add (by norm_num)]; simp
      have h7 : (1 : ℝ) ≤ 2 ^ s * ‖v‖ ^ (-s) := by
        calc (1 : ℝ) = 2 ^ s * 2 ^ (-s) := h6.symm
          _ ≤ 2 ^ s * ‖v‖ ^ (-s) := mul_le_mul_of_nonneg_left h5 (by positivity)
      nlinarith [Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 2) s]
  have hjy0 : 0 < jbracket y0 := s83_jb_pos y0
  have hp1 : 0 ≤ (12 * jbracket y0) ^ M := Real.rpow_nonneg (by linarith) _
  have hp2 : 0 ≤ (3 * jbracket y0) ^ M := Real.rpow_nonneg (by linarith) _
  have hcE : 0 ≤ 1 + Mm + 2 * 2 ^ s := by
    have := Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 2) s; linarith
  set c0 : ℝ := A * (12 * jbracket y0) ^ M * (3 * jbracket y0) ^ M * (1 + Mm + 2 * 2 ^ s) with hc0
  refine ⟨c0, mul_nonneg (mul_nonneg (mul_nonneg hA hp1) hp2) hcE, ?_⟩
  intro y hy v hv hv2
  have hX : y + (1 / 2 : ℝ) • v + (1 / 2 : ℝ) • v = y + v := by module
  have hX' : y + (1 / 2 : ℝ) • v - (1 / 2 : ℝ) • v = y := by module
  have h0 := hF.2 j 0 (by omega) (y + (1 / 2 : ℝ) • v) v (norm_pos_iff.1 hv)
  rw [hX, hX'] at h0
  have hfun : (fun y' : Euc d => F (y' + v) y') =
      fun y' => (fun Y : Euc d => midPair F Y v) (y' + (1 / 2 : ℝ) • v) := by
    funext y'
    have e1 : y' + (1 / 2 : ℝ) • v + (1 / 2 : ℝ) • v = y' + v := by module
    have e2 : y' + (1 / 2 : ℝ) • v - (1 / 2 : ℝ) • v = y' := by module
    show F (y' + v) y' = F (y' + (1 / 2 : ℝ) • v + (1 / 2 : ℝ) • v) (y' + (1 / 2 : ℝ) • v - (1 / 2 : ℝ) • v)
    rw [e1, e2]
  have hnorm : ‖iteratedFDeriv ℝ j (fun y' : Euc d => F (y' + v) y') y‖ =
      ‖mixedJet j 0 F (y + (1 / 2 : ℝ) • v) v‖ := by
    have h1 : iteratedFDeriv ℝ j (fun y' : Euc d => F (y' + v) y') y =
        iteratedFDeriv ℝ j (fun Y : Euc d => midPair F Y v) (y + (1 / 2 : ℝ) • v) := by
      rw [hfun]
      exact iteratedFDeriv_comp_add_right (f := fun Y : Euc d => midPair F Y v) j ((1 / 2 : ℝ) • v) y
    rw [h1]
    have := r26t8a_nest_zero (E := Euc d) j (fun Yw : Euc d × Euc d => midPair F Yw.1 Yw.2)
      (y + (1 / 2 : ℝ) • v) v
    exact this.symm
  rw [hnorm]
  refine h0.trans ?_
  have hjb1 : jbracket y ≤ 3 * jbracket y0 := by
    have e : y = y0 + (y - y0) := by abel
    have := r26t8a_jb_shift' y0 (y - y0)
    rw [← e] at this
    have h2 : (2 + ‖y - y0‖) ≤ 3 := by linarith
    nlinarith [s83_jb_pos y0]
  have hjb2 : jbracket (y + v) ≤ 12 * jbracket y0 := by
    refine (r26t8a_jb_shift' y v).trans ?_
    nlinarith [s83_jb_pos y]
  have hpw : pairWeight M (y + v) y ≤ (12 * jbracket y0) ^ M * (3 * jbracket y0) ^ M := by
    unfold pairWeight
    exact mul_le_mul (Real.rpow_le_rpow (s83_jb_pos _).le hjb2 hM) (Real.rpow_le_rpow (s83_jb_pos _).le hjb1 hM)
      (Real.rpow_nonneg (s83_jb_pos _).le _) hp1
  have hE' := hE v hv hv2
  calc A * pairWeight M (y + v) y * (1 + (min 1 ‖v‖) ^ (-(sigma + ((0 : ℕ) : ℝ))) *
        (1 + |Real.log (min 1 ‖v‖)|) ^ b)
      ≤ A * ((12 * jbracket y0) ^ M * (3 * jbracket y0) ^ M) * ((1 + Mm + 2 * 2 ^ s) * ‖v‖ ^ (-s)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hpw hA) hE'
          (add_nonneg zero_le_one (mul_nonneg (Real.rpow_nonneg (le_min zero_le_one hv.le) _)
            (pow_nonneg (by linarith [abs_nonneg (Real.log (min 1 ‖v‖))]) _)))
          (mul_nonneg hA (mul_nonneg hp1 hp2))
    _ = c0 * ‖v‖ ^ (-s) := by rw [hc0]; ring

end HRS.MS.R26T8A
