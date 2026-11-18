import HRS.MS.WadAux80

/-!
# S8.3, packet S8E-3, part 2: the mild form of the flow-shifted difference

`s8e_shift_mild`: `u_r = P_{t-r} u_t + ∫_r^t P_{s-r} qu_s ds` for `u_s(y) = w_s(y + z_s) - w_s(y)` and
`qu_s(y) = 𝓑 w_s (y + z_s) - 𝓑 w_s (y)`, for a mild solution `w` (`S84Sol`) and `‖ζ‖ < 1/4`.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal

namespace HRS.MS.Wad

open HRS HRS.Whole

variable {d : ℕ}

theorem s8e_shift_mild {ρ : Euc d → ℝ} {a ν t M Φ : ℝ} {w : ℝ → Euc d → ℝ} (ha : 0 < a) (hν : 0 < ν)
    (hM : 0 ≤ M) (sol : S84Sol ρ a ν t M Φ w) {ζ : Euc d} (hζ : ‖ζ‖ < 1 / 4) {r : ℝ}
    (hr : r ∈ Set.Icc 0 t) (x : Euc d) :
    s8e_u a ζ w r x = s83_P a ν (t - r) (s8e_u a ζ w t) x +
      ∫ s in r..t, s83_P a ν (s - r) (fun y => s84_Bop ρ (w s) (y + s8e_zs a ζ s) - s84_Bop ρ (w s) y) x := by
  have hzs : ∀ s, 0 ≤ s → ‖s8e_zs a ζ s‖ < 1 / 4 := fun s hs =>
    lt_of_le_of_lt (s8e_zs_norm ha.le hs ζ) hζ
  have hr0 := hr.1
  have hrt := hr.2
  obtain ⟨Kq, pq, hKq⟩ := sol.hqb
  have hKq0 : 0 ≤ Kq := by
    have := (abs_nonneg (s84_Bop ρ (w 0) 0)).trans (hKq 0 ⟨le_rfl, hr0.trans hrt⟩ 0)
    simpa using this
  have hqmem : ∀ s ∈ Set.Icc 0 t, s ∈ Set.Icc 0 t := fun s hs => hs
  -- the two shifted pieces
  have hP1 : s83_P a ν (t - r) (w t) (x + s8e_zs a ζ r) =
      s83_P a ν (t - r) (fun y => w t (y + s8e_zs a ζ t)) x := by
    rw [s8e_P_shift]; simp only [s8e_zs_flow]
  have hP2 : ∀ s : ℝ, s83_P a ν (s - r) (fun y => s84_Bop ρ (w s) y) (x + s8e_zs a ζ r) =
      s83_P a ν (s - r) (fun y => s84_Bop ρ (w s) (y + s8e_zs a ζ s)) x := fun s => by
    rw [s8e_P_shift]; simp only [s8e_zs_flow]
  have hint2 := s84_hint ha hν sol hr x
  have hint1 : IntervalIntegrable (fun s => s83_P a ν (s - r)
      (fun y => s84_Bop ρ (w s) (y + s8e_zs a ζ s)) x) volume r t := by
    refine (s84_hint ha hν sol hr (x + s8e_zs a ζ r)).congr ?_
    exact fun s _ => hP2 s
  -- additivity of `P` inside the integral
  have hsub : ∀ s ∈ Set.Icc r t, s83_P a ν (s - r) (fun y => s84_Bop ρ (w s) (y + s8e_zs a ζ s) -
      s84_Bop ρ (w s) y) x = s83_P a ν (s - r) (fun y => s84_Bop ρ (w s) (y + s8e_zs a ζ s)) x -
      s83_P a ν (s - r) (fun y => s84_Bop ρ (w s) y) x := fun s hs => by
    have hs' : s ∈ Set.Icc 0 t := ⟨hr0.trans hs.1, hs.2⟩
    have hc := s84_sol_qcont sol hs'
    have hw0 : Wt (pq : ℝ) (Kq * 2 ^ pq) (fun y => s84_Bop ρ (w s) y) := s8e_wt_poly hKq0 (hKq s hs')
    have hw1 := s8e_wt_shift (Nat.cast_nonneg pq) hw0 (hzs s (hr0.trans hs.1))
    exact s8e_P_sub (hc.comp (continuous_id.add continuous_const)) hc (Nat.cast_nonneg pq) hw1 hw0 ha hν.le
      (by linarith [hs.1]) x
  have hdt : s83_P a ν (t - r) (s8e_u a ζ w t) x = s83_P a ν (t - r) (fun y => w t (y + s8e_zs a ζ t)) x -
      s83_P a ν (t - r) (w t) x := by
    have hwt := sol.term_wt
    have hw1 := s8e_wt_shift hM hwt (hzs t (hr0.trans hrt))
    exact s8e_P_sub (sol.term_cont.comp (continuous_id.add continuous_const)) sol.term_cont hM hw1 hwt ha hν.le
      (by linarith) x
  rw [hdt, intervalIntegral.integral_congr (g := fun s => s83_P a ν (s - r) (fun y => s84_Bop ρ (w s)
    (y + s8e_zs a ζ s)) x - s83_P a ν (s - r) (fun y => s84_Bop ρ (w s) y) x)
    (fun s hs => hsub s (by rwa [Set.uIcc_of_le hrt] at hs)), intervalIntegral.integral_sub hint1 hint2]
  unfold s8e_u
  rw [sol.mild r hr (x + s8e_zs a ζ r), sol.mild r hr x, hP1]
  rw [intervalIntegral.integral_congr (g := fun s => s83_P a ν (s - r) (fun y => s84_Bop ρ (w s)
    (y + s8e_zs a ζ s)) x) (fun s _ => hP2 s)]
  ring

end HRS.MS.Wad
