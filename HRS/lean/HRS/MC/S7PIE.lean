import HRS.MC.S7PIEDrift
import HRS.MC.L2C0
import HRS.MC.RegSet

/-!
# Packet PI-E: the drift measure (`s7_PI_E_drift_measure`)

Assembly.  For `m > 3d + 8` the regime supplies `AdjointData` at the level `J = ⌈m⌉` (`l2c0_adjointData_generic` with the
proved `Regime.reg`); `S7PIEDrift.pie_drift_main` then gives the continuity of the drift path, the bound with the
uniform constant `C = sup ‖V^{t,u}‖_{E_m → E_m}` (chosen before `b`), by operator interpolation between the integer
levels `⌈m⌉ - 1` and `⌈m⌉`, duality, the Lipschitz regularity of the propagator matrix in both times, and dominated
convergence.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.PIE

open HRS HRS.Sec7

variable {d : ℕ}

/-- **PI-E (the drift measure: continuity, bounded variation, additivity; `F:eq:Dmeasure`, `F:eq:Dvariation`)**. -/
theorem s7_PI_E_drift_measure_proof (R : Regime d) (m : ℝ) (hm : 3 * (d : ℝ) + 8 < m) (T : ℝ) (hT : 0 < T)
    :
    ∃ C : ℝ, ∀ b : ℝ → NegSobolev d m, MemLp b 1 (volume.restrict (Set.Icc (0 : ℝ) T)) →
      ∀ a a' : ℝ, 0 ≤ a → a ≤ a' → a' ≤ T →
      (Continuous fun t : Set.Icc (0 : ℝ) T => ∫ u in Set.Ioc a (min a' t), Vprop R.D R.ρ m t u (b u)) ∧
      ‖driftInc R.D R.ρ m T b a a'‖ ≤ C * ∫ u in Set.Ioc a a', ‖b u‖ := by
  have hd2 : 2 ≤ d := R.hd
  have hd1 : 1 ≤ d := by omega
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd2
  have hν : 0 < R.D.invβ := by rw [R.hDβ]; exact inv_pos.2 R.hβ
  have hm0 : 0 < m := by linarith
  -- the integer levels
  set N : ℕ := ⌈m⌉₊ with hN
  have hmN : m ≤ (N : ℝ) := Nat.le_ceil m
  have hNm : (N : ℝ) < m + 1 := Nat.ceil_lt_add_one hm0.le
  have hN1 : 1 ≤ N := by
    have : (1 : ℝ) ≤ N := by linarith
    exact_mod_cast this
  obtain ⟨n₀, hn₀N⟩ : ∃ n₀ : ℕ, N = n₀ + 1 := ⟨N - 1, by omega⟩
  have hcast : (N : ℝ) = (n₀ : ℝ) + 1 := by rw [hn₀N]; push_cast; ring
  have hn₀m : (n₀ : ℝ) < m := by linarith
  have hmn₀ : m ≤ (n₀ : ℝ) + 1 := by linarith
  have hn₀1 : 1 ≤ n₀ := by
    have : (1 : ℝ) ≤ n₀ := by linarith
    exact_mod_cast this
  -- the adjoint data at the level `J = n₀ + 1`
  obtain ⟨hprob, hcont⟩ := HRS.MC.L2C0.l2c0_rho_prob_cont R
  have hA := HRS.MC.L2C0.l2c0_adjointData_generic R.D R.hM R.hV hν R.ρ hprob
    (fun j => HRS.MC.RegSet.reg_proof R j) hcont
  obtain ⟨Rg, MB, Λ, VB, ν₀, hAD⟩ := hA (n₀ + 1) (by omega) T hT
  have hmStar : PDE.mStar d ≤ n₀ + 1 := by
    have h1 : ((PDE.mStar d : ℕ) : ℝ) ≤ (d : ℝ) / 2 + 3 := by
      unfold PDE.mStar
      push_cast
      have := Nat.floor_le (show (0 : ℝ) ≤ (d : ℝ) / 2 by positivity)
      linarith
    have h2 : ((PDE.mStar d : ℕ) : ℝ) ≤ ((n₀ + 1 : ℕ) : ℝ) := by
      push_cast; linarith
    exact_mod_cast h2
  exact pie_drift_main (J := n₀ + 1) (D := R.D) (μ := R.ρ) (T := T) (m := m) (n₀ := n₀)
    ⟨⟨hd1, hmStar, Rg, MB, Λ, VB, ν₀, hAD⟩, hn₀1, le_rfl, hn₀m, hmn₀⟩

end HRS.MC.Sec7.PIE

end
