import HRS.MS.MainRdStatAux21
import HRS.MS.UlocModes

/-!
# SA2, packet 11a: the plane waves as admissible tests (for Corollary S.A.3)
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open HRS.Whole HRS.Whole.AppendixA HRS.Uniform HRS.GF HRS.Whole.AppendixALemmas
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MainRdStat

variable {d : ℕ}

theorem sa2_planeWave_re (k : Euc d) :
    (fun x => (planeWave k x).re) = fun x => Real.cos (2 * Real.pi * inner ℝ k x) := by
  funext x
  have : planeWave k x = Complex.exp (((2 * Real.pi * inner ℝ k x : ℝ) : ℂ) * Complex.I) := by
    unfold planeWave
    congr 1
    push_cast
    ring
  rw [this, Complex.exp_ofReal_mul_I_re]

theorem sa2_planeWave_im (k : Euc d) :
    (fun x => (planeWave k x).im) = fun x => Real.sin (2 * Real.pi * inner ℝ k x) := by
  funext x
  have : planeWave k x = Complex.exp (((2 * Real.pi * inner ℝ k x : ℝ) : ℂ) * Complex.I) := by
    unfold planeWave
    congr 1
    push_cast
    ring
  rw [this, Complex.exp_ofReal_mul_I_im]

theorem sa2_bracket_le (k : Euc d) : 1 + ‖k‖ ≤ Real.sqrt 2 * jbracket k := by
  unfold jbracket
  rw [← Real.sqrt_mul (by norm_num)]
  refine Real.le_sqrt_of_sq_le ?_
  nlinarith [sq_nonneg (‖k‖ - 1), norm_nonneg k]

theorem sa2_plane_data {χ : Euc d → ℝ} (hχ : IsUlocCutoff χ) :
    ∃ Cpw : ℝ, 0 ≤ Cpw ∧ ∀ {n : ℕ} (ξ : Fin (n + 1) → Euc d),
      (∀ ab, (ulocClass (mStar d) χ).mem (realImPartsRd (fun a => planeWave (ξ a)) ab)) ∧
      sa2X χ (realImPartsRd fun a => planeWave (ξ a)) ≤ Cpw * ∑ a, jbracket (ξ a) ^ mStar d := by
  obtain ⟨C, hC⟩ := HRS.MS.UlocModes.uloc_embedding_modes_proof (d := d) (mStar d) χ hχ
  set C' : ℝ := |C| with hC'
  have hC'0 : 0 ≤ C' := abs_nonneg _
  have hb : ∀ k : Euc d,
      ulocNormE (mStar d) χ (fun x => Real.cos (2 * Real.pi * inner ℝ k x)) ≤
        ENNReal.ofReal (C' * (1 + ‖k‖) ^ mStar d) ∧
      ulocNormE (mStar d) χ (fun x => Real.sin (2 * Real.pi * inner ℝ k x)) ≤
        ENNReal.ofReal (C' * (1 + ‖k‖) ^ mStar d) := fun k => by
    obtain ⟨h1, h2⟩ := hC k
    have hmono : ENNReal.ofReal (C * (1 + ‖k‖) ^ mStar d) ≤ ENNReal.ofReal (C' * (1 + ‖k‖) ^ mStar d) :=
      ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))
    exact ⟨h1.trans hmono, h2.trans hmono⟩
  have hbj : ∀ k : Euc d, (1 + ‖k‖) ^ mStar d ≤ (Real.sqrt 2) ^ mStar d * jbracket k ^ mStar d := fun k => by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (sa2_bracket_le k) _
  have hn : ∀ (k : Euc d) (u : Euc d → ℝ), ulocNormE (mStar d) χ u ≤ ENNReal.ofReal (C' * (1 + ‖k‖) ^ mStar d) →
      (ulocNormE (mStar d) χ u).toReal ≤ C' * ((Real.sqrt 2) ^ mStar d * jbracket k ^ mStar d) :=
    fun k u h => by
    refine (ENNReal.toReal_le_of_le_ofReal (by positivity) h).trans ?_
    exact mul_le_mul_of_nonneg_left (hbj k) hC'0
  refine ⟨2 * C' * (Real.sqrt 2) ^ mStar d, by positivity, fun {n} ξ => ⟨?_, ?_⟩⟩
  · rintro ⟨a, b⟩
    obtain ⟨h1, h2⟩ := hb (ξ a)
    cases b
    · have e : realImPartsRd (fun a => planeWave (ξ a)) (a, false) =
          fun x => Real.cos (2 * Real.pi * inner ℝ (ξ a) x) := by
        rw [← sa2_planeWave_re]; funext x; simp [realImPartsRd]
      rw [e]
      exact ⟨by fun_prop, lt_of_le_of_lt h1 ENNReal.ofReal_lt_top⟩
    · have e : realImPartsRd (fun a => planeWave (ξ a)) (a, true) =
          fun x => Real.sin (2 * Real.pi * inner ℝ (ξ a) x) := by
        rw [← sa2_planeWave_im]; funext x; simp [realImPartsRd]
      rw [e]
      exact ⟨by fun_prop, lt_of_le_of_lt h2 ENNReal.ofReal_lt_top⟩
  · unfold sa2X
    rw [Fintype.sum_prod_type, Finset.mul_sum]
    refine Finset.sum_le_sum fun a _ => ?_
    rw [Fintype.sum_bool]
    obtain ⟨h1, h2⟩ := hb (ξ a)
    have e1 : realImPartsRd (fun a => planeWave (ξ a)) (a, false) =
        fun x => Real.cos (2 * Real.pi * inner ℝ (ξ a) x) := by
      rw [← sa2_planeWave_re]; funext x; simp [realImPartsRd]
    have e2 : realImPartsRd (fun a => planeWave (ξ a)) (a, true) =
        fun x => Real.sin (2 * Real.pi * inner ℝ (ξ a) x) := by
      rw [← sa2_planeWave_im]; funext x; simp [realImPartsRd]
    rw [e1, e2]
    have n1 := hn (ξ a) _ h1
    have n2 := hn (ξ a) _ h2
    calc _ ≤ C' * ((Real.sqrt 2) ^ mStar d * jbracket (ξ a) ^ mStar d) +
          C' * ((Real.sqrt 2) ^ mStar d * jbracket (ξ a) ^ mStar d) := add_le_add n2 n1
      _ = _ := by ring

end HRS.MS.MainRdStat
