import HRS.Uniform.Q45Cov6

/-!
# Q45 (Lemma 3.20): two-block partitions and `L²`-convergence of functionals of Riemann sums
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.Uniform.Q45

section Part

/-- Two blocks of `M` equal cells: on `[0,t₁]` and on `[t₁,t₂]`. -/
def part (t1 t2 : ℝ) (M : ℕ) (i : ℕ) : ℝ :=
  t1 * (min (i : ℝ) M) / M + (t2 - t1) * (max ((i : ℝ) - M) 0) / M

variable {t1 t2 : ℝ} {M : ℕ}

lemma part_zero (t1 t2 : ℝ) (M : ℕ) : part t1 t2 M 0 = 0 := by simp [part]

lemma part_of_le {i : ℕ} (hi : i ≤ M) : part t1 t2 M i = t1 * i / M := by
  have hle : (i : ℝ) ≤ M := by exact_mod_cast hi
  have h1 : min (i : ℝ) M = i := min_eq_left hle
  have h2 : max ((i : ℝ) - M) 0 = 0 := max_eq_right (by linarith)
  simp [part, h1, h2]

lemma part_M (hM : 0 < M) : part t1 t2 M M = t1 := by
  rw [part_of_le le_rfl]
  have : (M : ℝ) ≠ 0 := by positivity
  field_simp

lemma part_2M (hM : 0 < M) : part t1 t2 M (2 * M) = t2 := by
  have hM' : (M : ℝ) ≠ 0 := by positivity
  have h1 : min ((2 * M : ℕ) : ℝ) M = M := min_eq_right (by push_cast; linarith [(Nat.cast_nonneg M : (0:ℝ) ≤ M)])
  have h2 : max (((2 * M : ℕ) : ℝ) - M) 0 = M := by
    rw [max_eq_left (by push_cast; linarith [(Nat.cast_nonneg M : (0:ℝ) ≤ M)])]
    push_cast; ring
  simp only [part, h1, h2]
  field_simp
  ring

lemma part_mono (h1 : 0 ≤ t1) (h12 : t1 ≤ t2) (M : ℕ) : Monotone (part t1 t2 M) := by
  intro i j hij
  have hij' : (i : ℝ) ≤ j := by exact_mod_cast hij
  unfold part
  have hM : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  gcongr

lemma part_nonneg (h1 : 0 ≤ t1) (h12 : t1 ≤ t2) (M : ℕ) (i : ℕ) : 0 ≤ part t1 t2 M i := by
  rw [← part_zero t1 t2 M]
  exact part_mono h1 h12 M (Nat.zero_le i)

lemma part_le (h1 : 0 ≤ t1) (h12 : t1 ≤ t2) (hM : 0 < M) {i : ℕ} (hi : i ≤ 2 * M) :
    part t1 t2 M i ≤ t2 := by
  calc part t1 t2 M i ≤ part t1 t2 M (2 * M) := part_mono h1 h12 M hi
    _ = t2 := part_2M hM

lemma part_step (h1 : 0 ≤ t1) (h12 : t1 ≤ t2) (hM : 0 < M) (i : ℕ) :
    part t1 t2 M (i + 1) - part t1 t2 M i ≤ t2 / M := by
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hmin : min (((i + 1 : ℕ) : ℝ)) M ≤ min (i : ℝ) M + 1 := by
    push_cast
    calc min ((i : ℝ) + 1) M ≤ min ((i : ℝ) + 1) (M + 1) := min_le_min le_rfl (by linarith)
      _ = min (i : ℝ) M + 1 := min_add_add_right _ _ _
  have hmax : max (((i + 1 : ℕ) : ℝ) - M) 0 ≤ max ((i : ℝ) - M) 0 + 1 := by
    push_cast
    refine max_le ?_ ?_
    · linarith [le_max_left ((i : ℝ) - M) 0]
    · linarith [le_max_right ((i : ℝ) - M) 0]
  have e : part t1 t2 M (i + 1) - part t1 t2 M i =
      (t1 * (min (((i + 1 : ℕ) : ℝ)) M - min (i : ℝ) M) +
        (t2 - t1) * (max (((i + 1 : ℕ) : ℝ) - M) 0 - max ((i : ℝ) - M) 0)) / M := by
    unfold part; ring
  rw [e]
  refine div_le_div_of_nonneg_right ?_ hMr.le
  nlinarith [mul_le_mul_of_nonneg_left (show min (((i + 1 : ℕ) : ℝ)) M - min (i : ℝ) M ≤ 1 by linarith) h1,
    mul_le_mul_of_nonneg_left (show max (((i + 1 : ℕ) : ℝ) - M) 0 - max ((i : ℝ) - M) 0 ≤ 1 by linarith)
      (sub_nonneg.2 h12)]

end Part

end HRS.Uniform.Q45
