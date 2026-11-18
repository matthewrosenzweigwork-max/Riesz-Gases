import HRS.Main.GFB3Aux9

/-!
# Packet GFB3, part 10: uniform partitions, uniform time-continuity of the adjoint gradient
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.GF

open HRS

/-- The uniform partition `r_i = t i / n` of `[0,t]`. -/
def gfb3_part (t : ℝ) (n : ℕ) : Fin (n + 1) → ℝ := fun i => t * (i : ℕ) / n

section Part

variable {t : ℝ} {n : ℕ}

lemma gfb3_part_zero : gfb3_part t n 0 = 0 := by simp [gfb3_part]

lemma gfb3_part_last (hn : 1 ≤ n) : gfb3_part t n (Fin.last n) = t := by
  have : (n : ℝ) ≠ 0 := by positivity
  simp [gfb3_part]
  field_simp

lemma gfb3_part_mono (ht : 0 ≤ t) : Monotone (gfb3_part t n) := by
  intro i j hij
  unfold gfb3_part
  have : ((i : ℕ) : ℝ) ≤ (j : ℕ) := by exact_mod_cast hij
  gcongr

lemma gfb3_part_step (hn : 1 ≤ n) (i : Fin n) :
    gfb3_part t n i.succ - gfb3_part t n i.castSucc = t / n := by
  have : (n : ℝ) ≠ 0 := by positivity
  simp [gfb3_part]
  field_simp
  ring

lemma gfb3_part_nonneg (ht : 0 ≤ t) (i : Fin (n + 1)) : 0 ≤ gfb3_part t n i := by
  unfold gfb3_part; positivity

lemma gfb3_part_le (ht : 0 ≤ t) (hn : 1 ≤ n) (i : Fin (n + 1)) : gfb3_part t n i ≤ t := by
  have h := gfb3_part_mono (n := n) ht (Fin.le_last i)
  rwa [gfb3_part_last hn] at h

lemma gfb3_part_cover (ht : 0 ≤ t) (hn : 1 ≤ n) {s : ℝ} (hs : s ∈ Set.Ioc 0 t) :
    ∃ i : Fin n, s ∈ Set.Ioc (gfb3_part t n i.castSucc) (gfb3_part t n i.succ) := by
  have htpos : 0 < t := lt_of_lt_of_le hs.1 hs.2
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  set x : ℝ := n * s / t with hx
  have hx0 : 0 < x := div_pos (mul_pos hnpos hs.1) htpos
  have hxn : x ≤ n := by
    rw [hx, div_le_iff₀ htpos]; nlinarith [hs.2]
  have hc1 : 1 ≤ ⌈x⌉₊ := Nat.one_le_iff_ne_zero.2 (Nat.ceil_pos.2 hx0).ne'
  have hc2 : ⌈x⌉₊ ≤ n := Nat.ceil_le.2 hxn
  refine ⟨⟨⌈x⌉₊ - 1, by omega⟩, ?_, ?_⟩
  · have h1 : ((⌈x⌉₊ - 1 : ℕ) : ℝ) < x := by
      have := Nat.lt_ceil.1 (show ⌈x⌉₊ - 1 < ⌈x⌉₊ by omega)
      exact this
    simp only [gfb3_part, Fin.val_castSucc]
    rw [div_lt_iff₀ hnpos]
    have : ((⌈x⌉₊ - 1 : ℕ) : ℝ) * t < n * s := by
      have := mul_lt_mul_of_pos_right h1 htpos
      rwa [hx, div_mul_cancel₀ _ htpos.ne'] at this
    nlinarith
  · have h1 : x ≤ ((⌈x⌉₊ - 1 : ℕ) : ℝ) + 1 := by
      have := Nat.le_ceil x
      have h2 : ((⌈x⌉₊ - 1 : ℕ) : ℝ) + 1 = ⌈x⌉₊ := by
        rw [← Nat.cast_succ]; congr 1; omega
      linarith
    simp only [gfb3_part, Fin.val_succ]
    rw [le_div_iff₀ hnpos]
    have : n * s ≤ (((⌈x⌉₊ - 1 : ℕ) + 1 : ℕ) : ℝ) * t := by
      have := mul_le_mul_of_nonneg_right h1 htpos.le
      rw [hx, div_mul_cancel₀ _ htpos.ne'] at this
      push_cast
      exact this
    nlinarith

lemma gfb3_part_disjoint (ht : 0 ≤ t) {i j : Fin n} (hij : i ≠ j) {s : ℝ}
    (hs : s ∈ Set.Ioc (gfb3_part t n i.castSucc) (gfb3_part t n i.succ)) :
    s ∉ Set.Ioc (gfb3_part t n j.castSucc) (gfb3_part t n j.succ) := by
  intro hs'
  rcases lt_or_gt_of_ne hij with h | h
  · have : gfb3_part t n i.succ ≤ gfb3_part t n j.castSucc :=
      gfb3_part_mono ht (by simp [Fin.le_def]; omega)
    linarith [hs.2, hs'.1]
  · have : gfb3_part t n j.succ ≤ gfb3_part t n i.castSucc :=
      gfb3_part_mono ht (by simp [Fin.le_def]; omega)
    linarith [hs.1, hs'.2]

end Part

end HRS.GF
