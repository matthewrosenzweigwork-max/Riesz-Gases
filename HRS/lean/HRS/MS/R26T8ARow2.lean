import HRS.MS.R26T8ARow1
import HRS.MS.R26T8AP05a
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

/-!
# S8.2 row lemma, step 2: the integrable majorant
`r26t8a_row_env`: the conormal envelope at `q = 0` is `<= cE |u|^(-s)` for `0 < |u| <= 2`, some `0 < s < d`.
`r26t8a_row_maj`: `Wmaj x u = 2 (1+|x-u|)^(-(d+1)) + cE 1_{|u|<=2} |u|^(-s)` is integrable with integral `<= Cint` uniformly in `x`, and dominates
`(1+|x-u|)^(-(d+1)) * envelope(u)` for `u != 0`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ContDiff
open HRS HRS.Whole HRS.MS.Phase2S82

namespace HRS.MS.R26T8A

variable {d : ℕ}

theorem r26t8a_row_env (hd : 2 ≤ d) (b : ℕ) (σ : ℝ) (hσd : σ < d) :
    ∃ s cE : ℝ, 0 < s ∧ s < d ∧ 0 ≤ cE ∧ ∀ u : Euc d, 0 < ‖u‖ → ‖u‖ ≤ 2 →
      1 + (min 1 ‖u‖) ^ (-(σ + ((0 : ℕ) : ℝ))) * (1 + |Real.log (min 1 ‖u‖)|) ^ b ≤ cE * ‖u‖ ^ (-s) := by
  set sp : ℝ := max σ 0 with hsp
  have hsp0 : 0 ≤ sp := le_max_right _ _
  have hspd : sp < d := max_lt hσd (by exact_mod_cast (by omega : 0 < d))
  set s : ℝ := sp + ((d : ℝ) - sp) / 2 with hs
  have hs0 : 0 < s := by rw [hs]; linarith
  have hsd' : s < d := by rw [hs]; linarith
  have hε : 0 < s - sp := by rw [hs]; linarith
  set Mm : ℝ := r26t8a_p06_M (s - sp) b with hMm
  have hMm0 : 0 ≤ Mm := by rw [hMm, r26t8a_p06_M]; have := hε; positivity
  have hcE : 0 ≤ 1 + Mm + 2 * 2 ^ s := by
    have := Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 2) s; linarith
  refine ⟨s, 1 + Mm + 2 * 2 ^ s, hs0, hsd', hcE, fun v hv hv2 => ?_⟩
  have hvs : 0 < ‖v‖ ^ (-s) := Real.rpow_pos_of_pos hv _
  have hL : 1 ≤ (1 + |Real.log (min 1 ‖v‖)|) ^ b :=
    one_le_pow₀ (by linarith [abs_nonneg (Real.log (min 1 ‖v‖))])
  rcases le_total ‖v‖ 1 with h1 | h1
  · rw [min_eq_right h1]
    simp only [Nat.cast_zero, add_zero]
    have hneg : (1 : ℝ) ≤ ‖v‖ ^ (-s) :=
      Real.one_le_rpow_of_pos_of_le_one_of_nonpos hv h1 (by linarith)
    have h2 : ‖v‖ ^ (-σ) ≤ ‖v‖ ^ (-sp) :=
      Real.rpow_le_rpow_of_exponent_ge hv h1 (by rw [hsp]; linarith [le_max_left σ 0])
    have h3 : ‖v‖ ^ (-sp) * (1 + |Real.log ‖v‖|) ^ b ≤ Mm * ‖v‖ ^ (-s) := by
      have := r26t8a_p06_slog b hε hv h1
      have e : ‖v‖ ^ (-sp) = ‖v‖ ^ (-s) * ‖v‖ ^ (s - sp) := by
        rw [← Real.rpow_add hv]; congr 1; ring
      calc ‖v‖ ^ (-sp) * (1 + |Real.log ‖v‖|) ^ b
          = ‖v‖ ^ (-s) * (‖v‖ ^ (s - sp) * (1 + |Real.log ‖v‖|) ^ b) := by rw [e]; ring
        _ ≤ ‖v‖ ^ (-s) * Mm := mul_le_mul_of_nonneg_left this hvs.le
        _ = Mm * ‖v‖ ^ (-s) := mul_comm _ _
    have h4 : ‖v‖ ^ (-σ) * (1 + |Real.log ‖v‖|) ^ b ≤ Mm * ‖v‖ ^ (-s) :=
      (mul_le_mul_of_nonneg_right h2 (by positivity)).trans h3
    nlinarith [hneg, h4, mul_nonneg (by positivity : (0:ℝ) ≤ 2 * 2 ^ s) hvs.le]
  · rw [min_eq_left h1]
    simp only [Nat.cast_zero, add_zero, Real.one_rpow, Real.log_one, abs_zero, add_zero, one_pow, mul_one]
    have h5 : (2 : ℝ) ^ (-s) ≤ ‖v‖ ^ (-s) := Real.rpow_le_rpow_of_nonpos hv hv2 (by linarith)
    have h6 : (2 : ℝ) ^ s * 2 ^ (-s) = 1 := by rw [← Real.rpow_add (by norm_num)]; simp
    have h7 : (1 : ℝ) ≤ 2 ^ s * ‖v‖ ^ (-s) := by
      calc (1 : ℝ) = 2 ^ s * 2 ^ (-s) := h6.symm
        _ ≤ 2 ^ s * ‖v‖ ^ (-s) := mul_le_mul_of_nonneg_left h5 (by positivity)
    nlinarith [Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 2) s]

theorem r26t8a_row_maj (hd : 2 ≤ d) (b : ℕ) (σ : ℝ) (hσd : σ < d) :
    ∃ s cE Cint : ℝ, 0 < s ∧ s < d ∧ 0 ≤ cE ∧ 0 ≤ Cint ∧ ∀ x : Euc d,
      Integrable (fun u : Euc d => 2 * (1 + ‖x - u‖) ^ (-((d : ℝ) + 1)) +
        cE * (closedBall (0 : Euc d) 2).indicator (fun u => ‖u‖ ^ (-s)) u) ∧
      (∫ u, (2 * (1 + ‖x - u‖) ^ (-((d : ℝ) + 1)) +
        cE * (closedBall (0 : Euc d) 2).indicator (fun u => ‖u‖ ^ (-s)) u)) ≤ Cint ∧
      ∀ u : Euc d, 0 < ‖u‖ → (1 + ‖x - u‖) ^ (-((d : ℝ) + 1)) *
        (1 + (min 1 ‖u‖) ^ (-(σ + ((0 : ℕ) : ℝ))) * (1 + |Real.log (min 1 ‖u‖)|) ^ b) ≤
        2 * (1 + ‖x - u‖) ^ (-((d : ℝ) + 1)) + cE * (closedBall (0 : Euc d) 2).indicator (fun u => ‖u‖ ^ (-s)) u := by
  obtain ⟨s, cE, hs0, hsd, hcE, hE⟩ := r26t8a_row_env hd b σ hσd
  have hdd : ((Module.finrank ℝ (Euc d) : ℕ) : ℝ) < (d : ℝ) + 1 := by
    rw [finrank_euclideanSpace_fin]; linarith
  have hJ : Integrable (fun v : Euc d => (1 + ‖v‖) ^ (-((d : ℝ) + 1))) := integrable_one_add_norm hdd
  have hI : IntegrableOn (fun u : Euc d => ‖u‖ ^ (-s)) (closedBall (0 : Euc d) 2) := by
    have := r26t8a_integrableOn_ball_rpow (d := d) (by omega) hsd 3
    exact this.mono_set (closedBall_subset_ball (by norm_num))
  have hIi : Integrable ((closedBall (0 : Euc d) 2).indicator (fun u => ‖u‖ ^ (-s))) :=
    (integrable_indicator_iff measurableSet_closedBall).2 hI
  set J : ℝ := ∫ v : Euc d, (1 + ‖v‖) ^ (-((d : ℝ) + 1)) with hJdef
  set I : ℝ := ∫ u, (closedBall (0 : Euc d) 2).indicator (fun u => ‖u‖ ^ (-s)) u with hIdef
  refine ⟨s, cE, 2 * J + cE * I, hs0, hsd, hcE, ?_, fun x => ⟨?_, ?_, fun u hu => ?_⟩⟩
  · have hJ0 : 0 ≤ J := integral_nonneg fun v => Real.rpow_nonneg (by positivity) _
    have hI0 : 0 ≤ I := integral_nonneg fun u => Set.indicator_nonneg (fun u _ => Real.rpow_nonneg (norm_nonneg u) _) u
    positivity
  · exact ((hJ.comp_sub_left x).const_mul 2).add (hIi.const_mul cE)
  · have h1 : ∫ u, (1 + ‖x - u‖) ^ (-((d : ℝ) + 1)) = J := by
      rw [hJdef]; exact integral_sub_left_eq_self (fun v : Euc d => (1 + ‖v‖) ^ (-((d : ℝ) + 1))) volume x
    rw [integral_add ((hJ.comp_sub_left x).const_mul 2) (hIi.const_mul cE), integral_const_mul, integral_const_mul, h1]
  · have hpos : 0 < (1 + ‖x - u‖) ^ (-((d : ℝ) + 1)) := Real.rpow_pos_of_pos (by positivity) _
    have hle1 : (1 + ‖x - u‖) ^ (-((d : ℝ) + 1)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by linarith [norm_nonneg (x - u)]) (by linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)])
    by_cases hu2 : ‖u‖ ≤ 2
    · rw [Set.indicator_of_mem (by simpa using hu2)]
      have := hE u hu hu2
      calc (1 + ‖x - u‖) ^ (-((d : ℝ) + 1)) * (1 + (min 1 ‖u‖) ^ (-(σ + ((0 : ℕ) : ℝ))) * (1 + |Real.log (min 1 ‖u‖)|) ^ b)
          ≤ 1 * (cE * ‖u‖ ^ (-s)) := mul_le_mul hle1 this (by positivity) zero_le_one
        _ ≤ _ := by nlinarith [mul_nonneg (le_of_lt hpos) (by positivity : (0:ℝ) ≤ 1)]
    · rw [Set.indicator_of_notMem (by simpa using hu2), mul_zero, add_zero]
      have h1u : (1 : ℝ) ≤ ‖u‖ := by linarith [not_le.1 hu2]
      rw [min_eq_left h1u]
      simp only [Real.one_rpow, Real.log_one, abs_zero, add_zero, one_pow, mul_one]
      nlinarith

end HRS.MS.R26T8A
