import HRS.MS.Fp81S21GaussG4U82
import HRS.MS.Fp81S21GaussG4U32
import HRS.MS.ProClosureS111OscillatorCb

/-! Oscillator tests have finite G4 cost, so cost convergence applies to
Hermite approximations. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal ContDiff
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.FixEq
open HRS.MS.ProClosureS111 HRS.MS.S111K4AT

/-- Oscillator tests at the physical index have finite G4 weighted norm. -/
theorem fp81s21_g4_osc_cost_finite {d : ℕ} {f : Euc d → ℝ}
    (hf : IsOscTest (wholeSpaceIndex d : ℝ) f) :
    weightedSobolevE 2 (2 * (d : ℝ) + 4) f < ⊤ := by
  have hn : (2 : ℝ) + (d : ℝ) / 2 < (d + 3 : ℕ) := by
    push_cast
    linarith [Nat.cast_nonneg (α := ℝ) d]
  have hm : (d : ℝ) < ((wholeSpaceIndex d : ℝ) - (d + 3 : ℕ)) / 2 := by
    unfold wholeSpaceIndex
    push_cast
    linarith [Nat.cast_nonneg (α := ℝ) d]
  obtain ⟨B, hB, hb⟩ := oscillator_derivative_norm_bound (d := d)
    (m := (wholeSpaceIndex d : ℝ)) 2 (d + 3) hn hm
  have hbound := hb f hf
  have hnonneg : 0 ≤ B * oscNorm (wholeSpaceIndex d : ℝ) f :=
    (norm_nonneg _).trans (hbound 0 (by omega) 0)
  have hP : (d : ℝ) < 2 * (2 * (d : ℝ) + 4) := by
    linarith [Nat.cast_nonneg (α := ℝ) d]
  exact lt_of_le_of_lt (s57p_E_le_cb hP hnonneg hbound) ENNReal.ofReal_lt_top

/-- The G4 cost itself converges when oscillator-test differences converge
in G4 cost. -/
theorem fp81s21_g4_osc_cost_continuous {d : ℕ} (f : Euc d → ℝ)
    (F : ℕ → Euc d → ℝ)
    (hf : IsOscTest (wholeSpaceIndex d : ℝ) f)
    (hF : ∀ n, IsOscTest (wholeSpaceIndex d : ℝ) (F n))
    (hconv : Tendsto (fun n => fp81s21_g4_J d (F n - f)) atTop (𝓝 0)) :
    Tendsto (fun n => fp81s21_g4_J d (F n)) atTop (𝓝 (fp81s21_g4_J d f)) := by
  exact fp81s21_g4_cost_continuous f F
    (hf.1.of_le (by simp))
    (fun n => (hF n).1.of_le (by simp))
    (fp81s21_g4_osc_cost_finite hf) (fun n => fp81s21_g4_osc_cost_finite (hF n)) hconv

/-- Hermite truncations converge in the value of the G4 cost. -/
theorem fp81s21_g4_cost_approx_values (p : Parameters) {f : Euc p.d → ℝ}
    (hf : IsR2Test f) :
    Tendsto (fun n => fp81s21_g4_J p.d (k4hs (wholeSpaceIndex p.d : ℝ) n f))
      atTop (𝓝 (fp81s21_g4_J p.d f)) := by
  apply fp81s21_g4_osc_cost_continuous
  · exact r2Test_isOscTest (wholeSpaceIndex p.d : ℝ) hf
  · intro n
    exact k4hs_osc (wholeSpaceIndex p.d : ℝ) n f
  · exact fp81s21_g4_cost_approx p hf

#print axioms fp81s21_g4_osc_cost_finite
#print axioms fp81s21_g4_osc_cost_continuous
#print axioms fp81s21_g4_cost_approx_values
end HRS.Fp81.S21
