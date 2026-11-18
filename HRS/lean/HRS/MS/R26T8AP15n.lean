import HRS.MS.R26T8AP15m

/-!
# S8.2 T8A P15n: conormal bound of `nu Σ dx dx Q + Σ α_i(x) dx Q`
If `Q` is `Conormal (k+2) b M s A` then `(x,y) ↦ nu Σ_i dx_i dx_i Q + Σ_i α_i(x) dx_i Q` is `Conormal k b (M+1) (s+2) (c A)`
with `c` independent of `Q` (the drift coordinates satisfy `‖D^j α_i‖ ≤ B jb` for `j ≤ k`).
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

variable {d : ℕ}

theorem r26t8a_LxP_conormal {chi : Euc d → ℝ} (hchi : NewtonCutoff chi) (k b : ℕ) (M s ν B : ℝ) (hB : 0 ≤ B)
    (α : Fin d → Euc d → ℝ) (hα : ∀ i, ContDiff ℝ (k : WithTop ℕ∞) (α i))
    (hαb : ∀ i, ∀ j ≤ k, ∀ x, ‖iteratedFDeriv ℝ j (α i) x‖ ≤ B * jbracket x) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ (Q : Euc d → Euc d → ℝ) (A : ℝ), 0 ≤ A → Conormal (k + 2) b M s A Q →
      Conormal k b (M + 1) (s + 2) (c * A)
        (fun x y => ν * ∑ i : Fin d, r26t8a_dx i (r26t8a_dx i Q) x y + ∑ i : Fin d, α i x * r26t8a_dx i Q x y) := by
  set c1 : ℝ := 2 ^ k * (((k : ℝ) + 1) ^ 2 * |ν| * (d * (2 * 2))) with hc1
  set c2 : ℝ := d * (2 ^ k * (((k : ℝ) + 1) ^ 2 * B * 2)) with hc2
  refine ⟨c1 + c2, by positivity, fun Q A hA hQ => ?_⟩
  have h1 : ∀ i : Fin d, Conormal (k + 1) b M (s + 1) (2 * A) (r26t8a_dx i Q) := fun i =>
    r26t8a_f8_dx_conormal hchi hA (k := k + 1) hQ i
  have h2 : ∀ i : Fin d, Conormal k b M (s + 1 + 1) (2 * (2 * A)) (r26t8a_dx i (r26t8a_dx i Q)) := fun i =>
    r26t8a_f8_dx_conormal hchi (by positivity) (h1 i) i
  have h3 := r26t8a_conormal_sum hchi Finset.univ (A := fun _ : Fin d => 2 * (2 * A))
    (F := fun i => r26t8a_dx i (r26t8a_dx i Q)) (fun i _ => h2 i)
  have h4 := r26t8a_conormal_const_mul hchi (by simp [Finset.sum_const]; positivity) ν h3
  have h4' : Conormal k b (M + 1) (s + 2) (c1 * A)
      (fun x y => ν * ∑ i : Fin d, r26t8a_dx i (r26t8a_dx i Q) x y) := by
    refine r26t8a_conormal_mono_M (by positivity) (by linarith : M ≤ M + 1)
      (r26t8a_conormal_mono_sA (by simp [Finset.sum_const]; positivity) (le_of_eq ?_) (le_of_eq (by ring)) h4)
    rw [hc1]; simp [Finset.sum_const]; ring
  have h5 : ∀ i : Fin d, Conormal k b (M + 1) (s + 1) (2 ^ k * (((k : ℝ) + 1) ^ 2 * B * (2 * A)))
      (fun x y => α i x * r26t8a_dx i Q x y) := fun i =>
    r26t8a_conormal_mul_xw hchi (by positivity) hB (hα i) (hαb i)
      (r26t8a_conormal_mono (Nat.le_succ k) (h1 i))
  have h6 := r26t8a_conormal_sum hchi Finset.univ (A := fun _ : Fin d => 2 ^ k * (((k : ℝ) + 1) ^ 2 * B * (2 * A)))
    (F := fun i x y => α i x * r26t8a_dx i Q x y) (fun i _ => h5 i)
  have h6' : Conormal k b (M + 1) (s + 2) (c2 * A)
      (fun x y => ∑ i : Fin d, α i x * r26t8a_dx i Q x y) :=
    r26t8a_conormal_mono_sA (by simp [Finset.sum_const]; positivity) (le_of_eq (by rw [hc2]; simp [Finset.sum_const]; ring))
      (by linarith) h6
  have := r26t8a_conormal_add hchi h4' h6'
  refine r26t8a_conormal_mono_sA (by positivity) (le_of_eq (by ring)) le_rfl this

end HRS.MS.R26T8A
