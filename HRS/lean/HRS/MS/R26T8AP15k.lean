import HRS.MS.R26T8AP15j
import HRS.MS.R26T8AP14b

/-!
# S8.2 T8A P15k: conormal bounds for the local part of the defect
For `R` with `Conormal (k+2) b M s A R` (order `s = σ - 2`): uniform-constant conormal bounds of
* `ν ZZ R` (order `s+2`), `ν PP R` (order `s`),
* `Σ_i (α_i x + α_i y) pdir (e_i,0) R` (order `s`, weight `M+1`),
* `Σ_i (α_i x - α_i y) pdir (0,e_i) R` (order `s`, weight `M+1`; the difference gains the separation factor).
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

variable {d : ℕ}

theorem r26t8a_ZZ_conormal {chi : Euc d → ℝ} (hchi : NewtonCutoff chi) (k b : ℕ) (M σ ν : ℝ) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ (R : Euc d → Euc d → ℝ) (A : ℝ), 0 ≤ A → Conormal (k + 2) b M σ A R →
      Conormal k b M (σ + 2) (c * A) (fun x y => ν * r26t8a_ZZ R x y) := by
  refine ⟨2 ^ k * (((k : ℝ) + 1) ^ 2 * |ν| * d), by positivity, fun R A hA hR => ?_⟩
  have h1 : ∀ i : Fin d, Conormal (k + 1) b M (σ + 1) A (r26t8a_pdir (0, r26t8a_e d i) R) := fun i =>
    r26t8a_pdir_conormal_Z hchi hA (k := k + 1) hR _ (le_of_eq (by simp [r26t8a_e_norm]))
  have h2 : ∀ i : Fin d, Conormal k b M (σ + 1 + 1) A
      (r26t8a_pdir (0, r26t8a_e d i) (r26t8a_pdir (0, r26t8a_e d i) R)) := fun i =>
    r26t8a_pdir_conormal_Z hchi hA (h1 i) _ (le_of_eq (by simp [r26t8a_e_norm]))
  have h3 := r26t8a_conormal_sum hchi Finset.univ (A := fun _ : Fin d => A)
    (F := fun i => r26t8a_pdir (0, r26t8a_e d i) (r26t8a_pdir (0, r26t8a_e d i) R)) (fun i _ => h2 i)
  have h4 := r26t8a_conormal_const_mul hchi (by simp [Finset.sum_const]; positivity) ν h3
  refine r26t8a_conormal_mono_sA (by simp [Finset.sum_const]; positivity) (le_of_eq ?_) (le_of_eq (by ring)) h4
  simp [Finset.sum_const]; ring

theorem r26t8a_PP_conormal {chi : Euc d → ℝ} (hchi : NewtonCutoff chi) (k b : ℕ) (M σ ν : ℝ) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ (R : Euc d → Euc d → ℝ) (A : ℝ), 0 ≤ A → Conormal (k + 2) b M σ A R →
      Conormal k b M σ (c * A) (fun x y => ν * r26t8a_PP R x y) := by
  refine ⟨2 ^ k * (((k : ℝ) + 1) ^ 2 * |ν| * d), by positivity, fun R A hA hR => ?_⟩
  have h1 : ∀ i : Fin d, Conormal (k + 1) b M σ A (r26t8a_pdir (r26t8a_e d i, 0) R) := fun i =>
    r26t8a_pdir_conormal_X hchi hA (k := k + 1) hR _ (le_of_eq (r26t8a_e_norm i))
  have h2 : ∀ i : Fin d, Conormal k b M σ A
      (r26t8a_pdir (r26t8a_e d i, 0) (r26t8a_pdir (r26t8a_e d i, 0) R)) := fun i =>
    r26t8a_pdir_conormal_X hchi hA (h1 i) _ (le_of_eq (r26t8a_e_norm i))
  have h3 := r26t8a_conormal_sum hchi Finset.univ (A := fun _ : Fin d => A)
    (F := fun i => r26t8a_pdir (r26t8a_e d i, 0) (r26t8a_pdir (r26t8a_e d i, 0) R)) (fun i _ => h2 i)
  have h4 := r26t8a_conormal_const_mul hchi (by simp [Finset.sum_const]; positivity) ν h3
  refine r26t8a_conormal_mono_sA (by simp [Finset.sum_const]; positivity) (le_of_eq ?_) le_rfl h4
  simp [Finset.sum_const]; ring

theorem r26t8a_Sdrift_conormal {chi : Euc d → ℝ} (hchi : NewtonCutoff chi) (k b : ℕ) (M σ B : ℝ) (hB : 0 ≤ B)
    (α : Fin d → Euc d → ℝ) (hα : ∀ i, ContDiff ℝ ((k + 1 : ℕ) : WithTop ℕ∞) (α i))
    (hαb : ∀ i, ∀ j ≤ k + 1, ∀ x, ‖iteratedFDeriv ℝ j (α i) x‖ ≤ B * jbracket x) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ (R : Euc d → Euc d → ℝ) (A : ℝ), 0 ≤ A → Conormal (k + 1) b M σ A R →
      Conormal k b (M + 1) σ (c * A)
        (fun x y => ∑ i : Fin d, (1 / 2 : ℝ) * ((α i x + α i y) * r26t8a_pdir (r26t8a_e d i, 0) R x y)) := by
  refine ⟨d * (2 ^ k * (((k : ℝ) + 1) ^ 2 * (1 / 2 : ℝ) * (2 ^ k * (((k : ℝ) + 1) ^ 2 * (2 * B))))), by positivity,
    fun R A hA hR => ?_⟩
  have hαk : ∀ i, ContDiff ℝ (k : WithTop ℕ∞) (α i) := fun i => (hα i).of_le (by exact_mod_cast Nat.le_succ k)
  have h1 : ∀ i : Fin d, Conormal k b M σ A (r26t8a_pdir (r26t8a_e d i, 0) R) := fun i =>
    r26t8a_pdir_conormal_X hchi hA hR _ (le_of_eq (r26t8a_e_norm i))
  have h2 : ∀ i : Fin d, Conormal k b (M + 1) σ (2 ^ k * (((k : ℝ) + 1) ^ 2 * (2 * B) * A))
      (fun x y => (α i x + α i y) * r26t8a_pdir (r26t8a_e d i, 0) R x y) := fun i =>
    r26t8a_conormal_mul_sum hchi hA hB (hαk i) (fun j hj x => hαb i j (by omega) x) (h1 i)
  have h3 : ∀ i : Fin d, Conormal k b (M + 1) σ (2 ^ k * (((k : ℝ) + 1) ^ 2 * |(1 / 2 : ℝ)| *
      (2 ^ k * (((k : ℝ) + 1) ^ 2 * (2 * B) * A))))
      (fun x y => (1 / 2 : ℝ) * ((α i x + α i y) * r26t8a_pdir (r26t8a_e d i, 0) R x y)) := fun i =>
    r26t8a_conormal_const_mul hchi (by positivity) (1 / 2 : ℝ) (h2 i)
  have h4 := r26t8a_conormal_sum hchi Finset.univ (A := fun _ : Fin d => 2 ^ k * (((k : ℝ) + 1) ^ 2 * |(1 / 2 : ℝ)| *
      (2 ^ k * (((k : ℝ) + 1) ^ 2 * (2 * B) * A))))
    (F := fun i x y => (1 / 2 : ℝ) * ((α i x + α i y) * r26t8a_pdir (r26t8a_e d i, 0) R x y)) (fun i _ => h3 i)
  refine r26t8a_conormal_mono_sA (by positivity) (le_of_eq ?_) le_rfl h4
  norm_num [Finset.sum_const, abs_of_pos]; ring

theorem r26t8a_Ddrift_conormal {chi : Euc d → ℝ} (hchi : NewtonCutoff chi) (k b : ℕ) (M σ B : ℝ) (hB : 0 ≤ B)
    (α : Fin d → Euc d → ℝ) (hα : ∀ i, ContDiff ℝ ((k + 1 : ℕ) : WithTop ℕ∞) (α i))
    (hαb : ∀ i, ∀ j ≤ k + 1, ∀ x, ‖iteratedFDeriv ℝ j (α i) x‖ ≤ B * jbracket x) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ (R : Euc d → Euc d → ℝ) (A : ℝ), 0 ≤ A → Conormal (k + 1) b M σ A R →
      Conormal k b (M + 1) σ (c * A)
        (fun x y => ∑ i : Fin d, (α i x - α i y) * r26t8a_pdir (0, r26t8a_e d i) R x y) := by
  refine ⟨d * (2 ^ k * (((k : ℝ) + 1) ^ 2 * (2 * B))), by positivity, fun R A hA hR => ?_⟩
  have h1 : ∀ i : Fin d, Conormal k b M (σ + 1) A (r26t8a_pdir (0, r26t8a_e d i) R) := fun i =>
    r26t8a_pdir_conormal_Z hchi hA hR _ (le_of_eq (by simp [r26t8a_e_norm]))
  have h2 : ∀ i : Fin d, Conormal k b (M + 1) (σ + 1 - 1) (2 ^ k * (((k : ℝ) + 1) ^ 2 * (2 * B) * A))
      (fun x y => (α i x - α i y) * r26t8a_pdir (0, r26t8a_e d i) R x y) := fun i =>
    r26t8a_conormal_mul_diff hchi hA hB (hα i) (hαb i) (h1 i)
  have h4 := r26t8a_conormal_sum hchi Finset.univ (A := fun _ : Fin d => 2 ^ k * (((k : ℝ) + 1) ^ 2 * (2 * B) * A))
    (F := fun i x y => (α i x - α i y) * r26t8a_pdir (0, r26t8a_e d i) R x y) (fun i _ => h2 i)
  refine r26t8a_conormal_mono_sA (by positivity) (le_of_eq ?_) (le_of_eq (by ring)) h4
  simp [Finset.sum_const]; ring

end HRS.MS.R26T8A
