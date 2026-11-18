import Mathlib

/-!
# Packet COV211, growth facts for the root-`N` failure (`V:eq:response-log-ratios`)
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

noncomputable section

namespace HRS.MD.Cov211

theorem log_exp_mul_pos {N : ℕ} (hN : 1 ≤ N) : 1 ≤ Real.log (Real.exp 1 * N) := by
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  rw [Real.log_mul (Real.exp_pos 1).ne' (by linarith), Real.log_exp]
  have := Real.log_nonneg hN'
  linarith

/-- `N^a / log (eN) → ∞` for `a > 0`. -/
theorem tendsto_rpow_div_log (a : ℝ) (ha : 0 < a) :
    Tendsto (fun N : ℕ => (N : ℝ) ^ a / Real.log (Real.exp 1 * N)) atTop atTop := by
  set c : ℝ := 2 * Real.exp (a / 2) / a with hc
  have hcpos : 0 < c := by positivity
  have hlim : Tendsto (fun N : ℕ => (N : ℝ) ^ (a / 2) / c) atTop atTop :=
    ((tendsto_rpow_atTop (by positivity : 0 < a / 2)).comp tendsto_natCast_atTop_atTop).atTop_div_const hcpos
  refine tendsto_atTop_mono' atTop ?_ hlim
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hlog : 1 ≤ Real.log (Real.exp 1 * N) := log_exp_mul_pos hN
  have h1 : Real.log (Real.exp 1 * N) ≤ c * (N : ℝ) ^ (a / 2) := by
    have := Real.log_le_rpow_div (x := Real.exp 1 * N) (ε := a / 2) (by positivity) (by positivity)
    rw [Real.mul_rpow (Real.exp_pos 1).le (by positivity), ← Real.exp_mul] at this
    calc Real.log (Real.exp 1 * N) ≤ _ := this
      _ = c * (N : ℝ) ^ (a / 2) := by
        rw [hc]; field_simp
  have h2 : (N : ℝ) ^ a = (N : ℝ) ^ (a / 2) * (N : ℝ) ^ (a / 2) := by
    rw [← Real.rpow_add (by linarith)]; congr 1; ring
  rw [div_le_div_iff₀ hcpos (by linarith)]
  calc (N : ℝ) ^ (a / 2) * Real.log (Real.exp 1 * N) ≤ (N : ℝ) ^ (a / 2) * (c * (N : ℝ) ^ (a / 2)) := by
        gcongr
    _ = (N : ℝ) ^ a * c := by rw [h2]; ring

theorem tendsto_rpow_div_sqrt_log (a : ℝ) (ha : 0 < a) :
    Tendsto (fun N : ℕ => (N : ℝ) ^ a / Real.sqrt (Real.log (Real.exp 1 * N))) atTop atTop := by
  have h := (Real.tendsto_sqrt_atTop).comp (tendsto_rpow_div_log (2 * a) (by positivity))
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hlog : 0 < Real.log (Real.exp 1 * N) := by have := log_exp_mul_pos hN; linarith
  simp only [Function.comp]
  have e : (N : ℝ) ^ (2 * a) = ((N : ℝ) ^ a) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN'.le]; congr 1; push_cast; ring
  rw [Real.sqrt_div (by positivity), e, Real.sqrt_sq (by positivity)]

/-- A frequent lower bound at a scale tending to infinity forces `limsup = ⊤`. -/
theorem limsup_top_of_frequent {T : ℕ → ℝ≥0∞} {w : ℕ → ℝ} {q : ℝ} (hq : 0 < q)
    (hw : ∀ N, 2 ≤ N → 0 < w N)
    (hfreq : ∀ L : ℕ, ∃ N, L ≤ N ∧ 2 ≤ N ∧ ENNReal.ofReal q ≤ ENNReal.ofReal (w N) * T N)
    (hgrow : Tendsto (fun N : ℕ => Real.sqrt N / w N) atTop atTop) :
    limsup (fun N : ℕ => ENNReal.ofReal (Real.sqrt N) * T N) atTop = ⊤ := by
  refine ENNReal.eq_top_of_forall_nnreal_le fun r => ?_
  refine Filter.le_limsup_of_frequently_le ?_
  rw [Filter.frequently_atTop]
  intro L
  have hev : ∀ᶠ N : ℕ in atTop, (r : ℝ) / q ≤ Real.sqrt N / w N := hgrow.eventually_ge_atTop _
  obtain ⟨L', hL'⟩ := Filter.eventually_atTop.1 hev
  obtain ⟨N, hN, hN2, hN3⟩ := hfreq (max L L')
  refine ⟨N, (le_max_left _ _).trans hN, ?_⟩
  have hwN := hw N hN2
  have hgN := hL' N ((le_max_right _ _).trans hN)
  calc (r : ℝ≥0∞) ≤ ENNReal.ofReal (Real.sqrt N / w N) * ENNReal.ofReal q := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        have : (r : ℝ) ≤ Real.sqrt N / w N * q := by
          calc (r : ℝ) = (r : ℝ) / q * q := by field_simp
            _ ≤ _ := by gcongr
        calc (r : ℝ≥0∞) = ENNReal.ofReal (r : ℝ) := (ENNReal.ofReal_coe_nnreal).symm
          _ ≤ _ := ENNReal.ofReal_le_ofReal this
    _ ≤ ENNReal.ofReal (Real.sqrt N / w N) * (ENNReal.ofReal (w N) * T N) := by gcongr
    _ = ENNReal.ofReal (Real.sqrt N) * T N := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
        congr 2
        field_simp

end HRS.MD.Cov211
