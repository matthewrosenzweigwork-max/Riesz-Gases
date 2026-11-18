import HRS.MS.Fp81S21IntervalRS2

/-!
# HRS S2.1(iii), packet 17b: restriction of an interval Riemann--Stieltjes value

Cauchy-criterion proof that an `IsR2RS` value on `[0,H]` restricts to a value on
`[q,r]` (`fp81s21_rs_restrict`).  Partitions are handled in an index form with
`ℕ`-indexed vertices (`fp81s21_RAdm`, `fp81s21_RMesh`): finite partitions are
converted to that form, fine partitions of the complementary intervals are
concatenated, and the completed sums are compared through `IsR2RS H`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.R2Interp

/-- Admissible `ℕ`-indexed tagged partition of `[a,b]` with `n` cells. -/
def fp81s21_RAdm (a b : ℝ) (n : ℕ) (v t : ℕ → ℝ) : Prop :=
  v 0 = a ∧ v n = b ∧ (∀ i j : ℕ, i < j → j ≤ n → v i < v j) ∧
    (∀ i : ℕ, i < n → v i ≤ t i ∧ t i ≤ v (i + 1))

/-- Every cell of the `ℕ`-indexed partition has length `< δ`. -/
def fp81s21_RMesh (δ : ℝ) (n : ℕ) (v : ℕ → ℝ) : Prop :=
  ∀ i : ℕ, i < n → v (i + 1) - v i < δ

/-- Index-clamped vertices of a finite partition, shifted by `c`. -/
def fp81s21_vC {n : ℕ} (u : Fin (n + 1) → ℝ) (c : ℝ) (k : ℕ) : ℝ :=
  c + u ⟨min k n, Nat.lt_succ_of_le (min_le_right k n)⟩

/-- Tags of a finite partition, shifted by `c` (only indices `< n` are used). -/
def fp81s21_tC {n : ℕ} (τ : Fin n → ℝ) (c : ℝ) (k : ℕ) : ℝ :=
  if h : k < n then c + τ ⟨k, h⟩ else c

theorem fp81s21_vC_of_le {n : ℕ} (u : Fin (n + 1) → ℝ) (c : ℝ) {k : ℕ} (hk : k ≤ n) :
    fp81s21_vC u c k = c + u ⟨k, by omega⟩ := by
  unfold fp81s21_vC
  have hfin : (⟨min k n, Nat.lt_succ_of_le (min_le_right k n)⟩ : Fin (n + 1)) =
      ⟨k, by omega⟩ :=
    Fin.ext (min_eq_left hk)
  rw [hfin]

theorem fp81s21_vC_zero {n : ℕ} (u : Fin (n + 1) → ℝ) (c : ℝ) :
    fp81s21_vC u c 0 = c + u 0 := by
  simp [fp81s21_vC]

theorem fp81s21_vC_last {n : ℕ} (u : Fin (n + 1) → ℝ) (c : ℝ) :
    fp81s21_vC u c n = c + u (Fin.last n) := by
  simp [fp81s21_vC, Fin.last]

theorem fp81s21_rR_sum {n : ℕ} (u : Fin (n + 1) → ℝ) (τ : Fin n → ℝ) (c : ℝ)
    (G : ℝ → ℝ → ℝ → ℝ) :
    ∑ i : Fin n, G (c + τ i) (c + u i.castSucc) (c + u i.succ) =
      ∑ k ∈ Finset.range n, G (fp81s21_tC τ c k) (fp81s21_vC u c k)
        (fp81s21_vC u c (k + 1)) := by
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i _
  have hi : (i : ℕ) < n := i.isLt
  have hv0 : fp81s21_vC u c (i : ℕ) = c + u i.castSucc :=
    (fp81s21_vC_of_le u c (show (i : ℕ) ≤ n by omega)).trans rfl
  have hv1 : fp81s21_vC u c ((i : ℕ) + 1) = c + u i.succ :=
    (fp81s21_vC_of_le u c (show (i : ℕ) + 1 ≤ n by omega)).trans rfl
  have ht : fp81s21_tC τ c (i : ℕ) = c + τ i := by
    unfold fp81s21_tC
    simp [hi]
  show G (c + τ i) (c + u i.castSucc) (c + u i.succ) =
    G (fp81s21_tC τ c (i : ℕ)) (fp81s21_vC u c (i : ℕ)) (fp81s21_vC u c ((i : ℕ) + 1))
  rw [hv0, hv1, ht]

theorem fp81s21_rR_adm {a b c : ℝ} {n : ℕ} {u : Fin (n + 1) → ℝ} {τ : Fin n → ℝ}
    (hu : StrictMono u) (hA : c + u 0 = a) (hB : c + u (Fin.last n) = b)
    (htag : ∀ i : Fin n, u i.castSucc ≤ τ i ∧ τ i ≤ u i.succ) :
    fp81s21_RAdm a b n (fp81s21_vC u c) (fp81s21_tC τ c) := by
  unfold fp81s21_RAdm
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [fp81s21_vC_zero, hA]
  · rw [fp81s21_vC_last, hB]
  · intro i j hij hj
    rw [fp81s21_vC_of_le u c (show i ≤ n by omega), fp81s21_vC_of_le u c hj]
    have h := hu (show (⟨i, by omega⟩ : Fin (n + 1)) < ⟨j, by omega⟩ from Fin.mk_lt_mk.mpr hij)
    linarith
  · intro i hi
    obtain ⟨h1, h2⟩ := htag ⟨i, hi⟩
    have e1 : u (Fin.castSucc (⟨i, hi⟩ : Fin n)) = u ⟨i, by omega⟩ := rfl
    have e2 : u (Fin.succ (⟨i, hi⟩ : Fin n)) = u ⟨i + 1, by omega⟩ := rfl
    rw [e1] at h1
    rw [e2] at h2
    rw [fp81s21_vC_of_le u c (show i ≤ n by omega),
      fp81s21_vC_of_le u c (show i + 1 ≤ n by omega)]
    unfold fp81s21_tC
    rw [dif_pos hi]
    constructor <;> linarith

theorem fp81s21_rR_mesh {δ c : ℝ} {n : ℕ} {u : Fin (n + 1) → ℝ}
    (hm : ∀ i : Fin n, u i.succ - u i.castSucc < δ) :
    fp81s21_RMesh δ n (fp81s21_vC u c) := by
  unfold fp81s21_RMesh
  intro k hk
  have h := hm ⟨k, hk⟩
  have e1 : u (Fin.succ (⟨k, hk⟩ : Fin n)) = u ⟨k + 1, by omega⟩ := rfl
  have e2 : u (Fin.castSucc (⟨k, hk⟩ : Fin n)) = u ⟨k, by omega⟩ := rfl
  rw [e1, e2] at h
  rw [fp81s21_vC_of_le u c (show k + 1 ≤ n by omega),
    fp81s21_vC_of_le u c (show k ≤ n by omega)]
  linarith

/-- Fine admissible partitions of any `[a,b]` with `a ≤ b` and mesh `< δ`. -/
theorem fp81s21_rR_fine {a b δ : ℝ} (hab : a ≤ b) (hδ : 0 < δ) :
    ∃ (n : ℕ) (v t : ℕ → ℝ), fp81s21_RAdm a b n v t ∧ fp81s21_RMesh δ n v := by
  rcases eq_or_lt_of_le hab with h | h
  · refine ⟨0, fun _ => a, fun _ => a, ?_, ?_⟩
    · unfold fp81s21_RAdm
      refine ⟨rfl, h, ?_, ?_⟩
      · intro i j hij hj
        exact absurd (lt_of_lt_of_le hij hj) (Nat.not_lt_zero i)
      · intro i hi
        exact absurd hi (Nat.not_lt_zero i)
    · unfold fp81s21_RMesh
      intro i hi
      exact absurd hi (Nat.not_lt_zero i)
  · obtain ⟨n, u, τ, hu, hu0, huT, htag, hmesh⟩ :=
      HRS.MC.Sec7.S7PIS2.S7PIS2_exists_partition (sub_pos.mpr h) hδ
    have hA : a + u 0 = a := by rw [hu0, add_zero]
    have hB : a + u (Fin.last n) = b := by rw [huT]; ring
    exact ⟨n, fp81s21_vC u a, fp81s21_tC τ a, fp81s21_rR_adm hu hA hB htag,
      fp81s21_rR_mesh hmesh⟩

/-- The `IsR2RS` value on `[0,H]` is also a limit along `ℕ`-indexed admissible partitions. -/
theorem fp81s21_rR_nat_of_IsR2RS {H I : ℝ} {S : ℝ → ℝ → ℝ → ℝ} (hS : IsR2RS H S I) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ (n : ℕ) (v t : ℕ → ℝ),
      fp81s21_RAdm 0 H n v t → fp81s21_RMesh δ n v →
      |∑ k ∈ Finset.range n, S (t k) (v k) (v (k + 1)) - I| < ε := by
  intro ε hε
  obtain ⟨δ, hδ, h⟩ := hS ε hε
  refine ⟨δ, hδ, ?_⟩
  intro n v t hadm hmesh
  unfold fp81s21_RAdm at hadm
  obtain ⟨h0, hH, hmono, htag⟩ := hadm
  unfold fp81s21_RMesh at hmesh
  have hu : StrictMono (fun i : Fin (n + 1) => v (i : ℕ)) := by
    intro i j hij
    exact hmono i j (Fin.lt_def.mp hij) (by have := j.isLt; omega)
  have hu0 : (fun i : Fin (n + 1) => v (i : ℕ)) 0 = 0 := by simpa using h0
  have huT : (fun i : Fin (n + 1) => v (i : ℕ)) (Fin.last n) = H := by simpa using hH
  have htg : ∀ i : Fin n, v (i : ℕ) ≤ t (i : ℕ) ∧ t (i : ℕ) ≤ v ((i : ℕ) + 1) :=
    fun i => htag (i : ℕ) i.isLt
  have hmesh' : ∀ i : Fin n, v ((i : ℕ) + 1) - v (i : ℕ) < δ :=
    fun i => hmesh (i : ℕ) i.isLt
  have key := h n (fun i : Fin (n + 1) => v (i : ℕ)) (fun i : Fin n => t (i : ℕ))
    hu hu0 huT htg hmesh'
  rw [← Fin.sum_univ_eq_sum_range]
  exact key

/-- Concatenation vertices: the first block up to index `n₁`, then the second block. -/
def fp81s21_vCat (n₁ : ℕ) (v₁ v₂ : ℕ → ℝ) (k : ℕ) : ℝ :=
  if k ≤ n₁ then v₁ k else v₂ (k - n₁)

/-- Concatenation tags: the first block below `n₁`, then the second block. -/
def fp81s21_tCat (n₁ : ℕ) (t₁ t₂ : ℕ → ℝ) (k : ℕ) : ℝ :=
  if k < n₁ then t₁ k else t₂ (k - n₁)

theorem fp81s21_vCat_le {n₁ : ℕ} {v₁ v₂ : ℕ → ℝ} {k : ℕ} (hk : k ≤ n₁) :
    fp81s21_vCat n₁ v₁ v₂ k = v₁ k := by
  unfold fp81s21_vCat
  rw [if_pos hk]

theorem fp81s21_vCat_ge {n₁ : ℕ} {v₁ v₂ : ℕ → ℝ} (hjunc : v₁ n₁ = v₂ 0) {k : ℕ}
    (hk : n₁ ≤ k) :
    fp81s21_vCat n₁ v₁ v₂ k = v₂ (k - n₁) := by
  unfold fp81s21_vCat
  by_cases h : k ≤ n₁
  · have hk' : k = n₁ := le_antisymm h hk
    subst hk'
    rw [if_pos le_rfl, Nat.sub_self, hjunc]
  · rw [if_neg h]

theorem fp81s21_tCat_lt {n₁ : ℕ} {t₁ t₂ : ℕ → ℝ} {k : ℕ} (hk : k < n₁) :
    fp81s21_tCat n₁ t₁ t₂ k = t₁ k := by
  unfold fp81s21_tCat
  rw [if_pos hk]

theorem fp81s21_tCat_ge {n₁ : ℕ} {t₁ t₂ : ℕ → ℝ} {k : ℕ} (hk : n₁ ≤ k) :
    fp81s21_tCat n₁ t₁ t₂ k = t₂ (k - n₁) := by
  unfold fp81s21_tCat
  rw [if_neg (show ¬ (k < n₁) by omega)]

/-- Two-block concatenation of admissible partitions `[a,b]` and `[b,c]`. -/
theorem fp81s21_rR_concat {a b c δ : ℝ} {n₁ n₂ : ℕ} {v₁ t₁ v₂ t₂ : ℕ → ℝ}
    (h₁ : fp81s21_RAdm a b n₁ v₁ t₁) (h₂ : fp81s21_RAdm b c n₂ v₂ t₂)
    (m₁ : fp81s21_RMesh δ n₁ v₁) (m₂ : fp81s21_RMesh δ n₂ v₂) :
    ∃ (v t : ℕ → ℝ), fp81s21_RAdm a c (n₁ + n₂) v t ∧ fp81s21_RMesh δ (n₁ + n₂) v ∧
      ∀ G : ℝ → ℝ → ℝ → ℝ,
        ∑ k ∈ Finset.range (n₁ + n₂), G (t k) (v k) (v (k + 1)) =
          ∑ k ∈ Finset.range n₁, G (t₁ k) (v₁ k) (v₁ (k + 1)) +
            ∑ k ∈ Finset.range n₂, G (t₂ k) (v₂ k) (v₂ (k + 1)) := by
  unfold fp81s21_RAdm at h₁ h₂
  unfold fp81s21_RMesh at m₁ m₂
  obtain ⟨h₁0, h₁n, h₁m, h₁t⟩ := h₁
  obtain ⟨h₂0, h₂n, h₂m, h₂t⟩ := h₂
  have hjunc : v₁ n₁ = v₂ 0 := by rw [h₁n, h₂0]
  have hmono₁ : ∀ i j : ℕ, i ≤ j → j ≤ n₁ → v₁ i ≤ v₁ j := by
    intro i j hij hj
    rcases eq_or_lt_of_le hij with h | h
    · rw [h]
    · exact (h₁m i j h hj).le
  refine ⟨fp81s21_vCat n₁ v₁ v₂, fp81s21_tCat n₁ t₁ t₂, ?_, ?_, ?_⟩
  · unfold fp81s21_RAdm
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [fp81s21_vCat_le (Nat.zero_le n₁)]
      exact h₁0
    · rw [fp81s21_vCat_ge hjunc (Nat.le_add_right n₁ n₂), Nat.add_sub_cancel_left]
      exact h₂n
    · intro i j hij hj
      by_cases hjn : j ≤ n₁
      · rw [fp81s21_vCat_le (show i ≤ n₁ by omega), fp81s21_vCat_le hjn]
        exact h₁m i j hij hjn
      · by_cases hin : i ≤ n₁
        · rw [fp81s21_vCat_le hin, fp81s21_vCat_ge hjunc (show n₁ ≤ j by omega)]
          have hA : v₁ i ≤ v₂ 0 := (hmono₁ i n₁ hin le_rfl).trans hjunc.le
          have hB : v₂ 0 < v₂ (j - n₁) := h₂m 0 (j - n₁) (by omega) (by omega)
          linarith
        · rw [fp81s21_vCat_ge hjunc (show n₁ ≤ i by omega),
            fp81s21_vCat_ge hjunc (show n₁ ≤ j by omega)]
          exact h₂m (i - n₁) (j - n₁) (by omega) (by omega)
    · intro i hi
      by_cases hin : i < n₁
      · rw [fp81s21_tCat_lt hin, fp81s21_vCat_le (show i ≤ n₁ by omega),
          fp81s21_vCat_le (show i + 1 ≤ n₁ by omega)]
        exact h₁t i hin
      · rw [fp81s21_tCat_ge (show n₁ ≤ i by omega),
          fp81s21_vCat_ge hjunc (show n₁ ≤ i by omega),
          fp81s21_vCat_ge hjunc (show n₁ ≤ i + 1 by omega),
          show i + 1 - n₁ = (i - n₁) + 1 by omega]
        exact h₂t (i - n₁) (by omega)
  · unfold fp81s21_RMesh
    intro i hi
    by_cases hin : i < n₁
    · rw [fp81s21_vCat_le (show i ≤ n₁ by omega), fp81s21_vCat_le (show i + 1 ≤ n₁ by omega)]
      exact m₁ i hin
    · rw [fp81s21_vCat_ge hjunc (show n₁ ≤ i by omega),
        fp81s21_vCat_ge hjunc (show n₁ ≤ i + 1 by omega),
        show i + 1 - n₁ = (i - n₁) + 1 by omega]
      exact m₂ (i - n₁) (by omega)
  · intro G
    rw [Finset.sum_range_add]
    congr 1
    · apply Finset.sum_congr rfl
      intro k hk
      have hk' : k < n₁ := Finset.mem_range.mp hk
      rw [fp81s21_tCat_lt hk', fp81s21_vCat_le (show k ≤ n₁ by omega),
        fp81s21_vCat_le (show k + 1 ≤ n₁ by omega)]
    · apply Finset.sum_congr rfl
      intro k hk
      have hk' : k < n₂ := Finset.mem_range.mp hk
      show G (fp81s21_tCat n₁ t₁ t₂ (n₁ + k)) (fp81s21_vCat n₁ v₁ v₂ (n₁ + k))
          (fp81s21_vCat n₁ v₁ v₂ (n₁ + k + 1)) = G (t₂ k) (v₂ k) (v₂ (k + 1))
      rw [fp81s21_tCat_ge (show n₁ ≤ n₁ + k by omega),
        fp81s21_vCat_ge hjunc (show n₁ ≤ n₁ + k by omega),
        fp81s21_vCat_ge hjunc (show n₁ ≤ n₁ + k + 1 by omega),
        show n₁ + k - n₁ = k by omega, show n₁ + k + 1 - n₁ = k + 1 by omega]

/-- Cauchy estimate in index form: two admissible fine partitions of `[q,r]` with mesh `< δ`
have sums within `ε` (the completions by fixed fine partitions of `[0,q]` and `[r,H]`). -/
theorem fp81s21_rR_cauchy_nat {H q r I : ℝ} {S : ℝ → ℝ → ℝ → ℝ} (hS : IsR2RS H S I)
    (hq : 0 ≤ q) (hr : r ≤ H) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (n₁ : ℕ) (v₁ t₁ : ℕ → ℝ) (n₂ : ℕ) (v₂ t₂ : ℕ → ℝ),
      fp81s21_RAdm q r n₁ v₁ t₁ → fp81s21_RMesh δ n₁ v₁ →
      fp81s21_RAdm q r n₂ v₂ t₂ → fp81s21_RMesh δ n₂ v₂ →
      |∑ k ∈ Finset.range n₁, S (t₁ k) (v₁ k) (v₁ (k + 1)) -
        ∑ k ∈ Finset.range n₂, S (t₂ k) (v₂ k) (v₂ (k + 1))| < ε := by
  obtain ⟨δ, hδ, hN⟩ := fp81s21_rR_nat_of_IsR2RS hS (ε / 2) (half_pos hε)
  refine ⟨δ, hδ, ?_⟩
  intro n₁ v₁ t₁ n₂ v₂ t₂ hP1 hm1 hP2 hm2
  obtain ⟨nA, vA, tA, hQA, hmA⟩ := fp81s21_rR_fine hq hδ
  obtain ⟨nB, vB, tB, hQB, hmB⟩ := fp81s21_rR_fine hr hδ
  obtain ⟨vP1, tP1, hAP1, hmP1, hsP1⟩ := fp81s21_rR_concat hP1 hQB hm1 hmB
  obtain ⟨vP2, tP2, hAP2, hmP2, hsP2⟩ := fp81s21_rR_concat hP2 hQB hm2 hmB
  obtain ⟨vC1, tC1, hAC1, hmC1, hsC1⟩ := fp81s21_rR_concat hQA hAP1 hmA hmP1
  obtain ⟨vC2, tC2, hAC2, hmC2, hsC2⟩ := fp81s21_rR_concat hQA hAP2 hmA hmP2
  have e1 := hN _ _ _ hAC1 hmC1
  have e2 := hN _ _ _ hAC2 hmC2
  rw [hsC1 S, hsP1 S] at e1
  rw [hsC2 S, hsP2 S] at e2
  obtain ⟨e1a, e1b⟩ := abs_lt.mp e1
  obtain ⟨e2a, e2b⟩ := abs_lt.mp e2
  rw [abs_lt]
  constructor <;> linarith

/-- Cauchy estimate for finite shifted tagged partitions of `[0, r-q]` (absolute times `q + ·`). -/
theorem fp81s21_rs_restrict_cauchy {H q r I : ℝ} {S : ℝ → ℝ → ℝ → ℝ} (hS : IsR2RS H S I)
    (hq : 0 ≤ q) (hr : r ≤ H) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (n₁ : ℕ) (u₁ : Fin (n₁ + 1) → ℝ) (τ₁ : Fin n₁ → ℝ) (n₂ : ℕ)
      (u₂ : Fin (n₂ + 1) → ℝ) (τ₂ : Fin n₂ → ℝ),
      StrictMono u₁ → u₁ 0 = 0 → u₁ (Fin.last n₁) = r - q →
      (∀ i : Fin n₁, u₁ i.castSucc ≤ τ₁ i ∧ τ₁ i ≤ u₁ i.succ) →
      (∀ i : Fin n₁, u₁ i.succ - u₁ i.castSucc < δ) →
      StrictMono u₂ → u₂ 0 = 0 → u₂ (Fin.last n₂) = r - q →
      (∀ i : Fin n₂, u₂ i.castSucc ≤ τ₂ i ∧ τ₂ i ≤ u₂ i.succ) →
      (∀ i : Fin n₂, u₂ i.succ - u₂ i.castSucc < δ) →
      |∑ i : Fin n₁, S (q + τ₁ i) (q + u₁ i.castSucc) (q + u₁ i.succ) -
        ∑ i : Fin n₂, S (q + τ₂ i) (q + u₂ i.castSucc) (q + u₂ i.succ)| < ε := by
  obtain ⟨δ, hδ, hC⟩ := fp81s21_rR_cauchy_nat hS hq hr hε
  refine ⟨δ, hδ, ?_⟩
  intro n₁ u₁ τ₁ n₂ u₂ τ₂ hu₁ hu₁0 hu₁T ht₁ hm₁ hu₂ hu₂0 hu₂T ht₂ hm₂
  have hA₁ : q + u₁ 0 = q := by rw [hu₁0, add_zero]
  have hB₁ : q + u₁ (Fin.last n₁) = r := by rw [hu₁T]; ring
  have hA₂ : q + u₂ 0 = q := by rw [hu₂0, add_zero]
  have hB₂ : q + u₂ (Fin.last n₂) = r := by rw [hu₂T]; ring
  have hR₁ := fp81s21_rR_adm hu₁ hA₁ hB₁ ht₁
  have hR₂ := fp81s21_rR_adm hu₂ hA₂ hB₂ ht₂
  have hM₁ := fp81s21_rR_mesh (c := q) hm₁
  have hM₂ := fp81s21_rR_mesh (c := q) hm₂
  have e := hC n₁ _ _ n₂ _ _ hR₁ hM₁ hR₂ hM₂
  rw [fp81s21_rR_sum u₁ τ₁ q S, fp81s21_rR_sum u₂ τ₂ q S]
  exact e

/-- Restriction of an `IsR2RS` value on `[0,H]` to a subinterval `[q,r]` by the Cauchy criterion. -/
theorem fp81s21_rs_restrict {H q r I : ℝ} {S : ℝ → ℝ → ℝ → ℝ} (hH : 0 < H) (hS : IsR2RS H S I)
    (hq : 0 ≤ q) (hqr : q ≤ r) (hr : r ≤ H) : ∃ J : ℝ, fp81s21_IsRSOn q r S J := by
  rcases eq_or_lt_of_le hqr with h | h
  · exact ⟨0, by rw [h]; exact fp81s21_isRSOn_zero r S⟩
  · have hT : 0 < r - q := sub_pos.mpr h
    have hex : ∀ k : ℕ, ∃ (n : ℕ) (u : Fin (n + 1) → ℝ) (τ : Fin n → ℝ), StrictMono u ∧
        u 0 = 0 ∧ u (Fin.last n) = r - q ∧
        (∀ i : Fin n, u i.castSucc ≤ τ i ∧ τ i ≤ u i.succ) ∧
        (∀ i : Fin n, u i.succ - u i.castSucc < 1 / ((k : ℝ) + 1)) := by
      intro k
      exact HRS.MC.Sec7.S7PIS2.S7PIS2_exists_partition hT (by positivity)
    choose N U Tg hU hU0 hUT hTg hMesh using hex
    obtain ⟨s, hs⟩ : ∃ s : ℕ → ℝ, ∀ k, s k =
        ∑ i : Fin (N k), S (q + Tg k i) (q + U k i.castSucc) (q + U k i.succ) :=
      ⟨_, fun k => rfl⟩
    have hcs : CauchySeq s := by
      rw [Metric.cauchySeq_iff]
      intro ε hε
      obtain ⟨δ, hδ, hC⟩ := fp81s21_rs_restrict_cauchy hS hq hr hε
      obtain ⟨M, hM⟩ := exists_nat_one_div_lt hδ
      have hsmall : ∀ j : ℕ, M ≤ j → ∀ i : Fin (N j), U j i.succ - U j i.castSucc < δ := by
        intro j hj i
        have h1 : (1 : ℝ) / ((j : ℝ) + 1) ≤ 1 / ((M : ℝ) + 1) := by
          apply one_div_le_one_div_of_le (by positivity)
          have : (M : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
          linarith
        exact lt_of_lt_of_le (hMesh j i) (le_trans h1 hM.le)
      refine ⟨M, fun m hm n hn => ?_⟩
      have h1 := hC (N m) (U m) (Tg m) (N n) (U n) (Tg n) (hU m) (hU0 m) (hUT m) (hTg m)
        (hsmall m hm) (hU n) (hU0 n) (hUT n) (hTg n) (hsmall n hn)
      rw [Real.dist_eq, hs m, hs n]
      exact h1
    obtain ⟨J, hJ⟩ := cauchySeq_tendsto_of_complete hcs
    refine ⟨J, ?_⟩
    unfold fp81s21_IsRSOn IsR2RS
    intro ε hε
    obtain ⟨δ, hδ, hC⟩ := fp81s21_rs_restrict_cauchy hS hq hr (half_pos hε)
    obtain ⟨M, hM⟩ := exists_nat_one_div_lt hδ
    obtain ⟨N₂, hN₂⟩ := Metric.tendsto_atTop.mp hJ (ε / 2) (half_pos hε)
    refine ⟨δ, hδ, ?_⟩
    intro n u τ hu hu0 huT htag hmesh
    obtain ⟨k, hk1, hk2⟩ : ∃ k : ℕ, M ≤ k ∧ N₂ ≤ k :=
      ⟨max M N₂, le_max_left _ _, le_max_right _ _⟩
    have hmk : ∀ i : Fin (N k), U k i.succ - U k i.castSucc < δ := by
      intro i
      have h1 : (1 : ℝ) / ((k : ℝ) + 1) ≤ 1 / ((M : ℝ) + 1) := by
        apply one_div_le_one_div_of_le (by positivity)
        have : (M : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
        linarith
      exact lt_of_lt_of_le (hMesh k i) (le_trans h1 hM.le)
    have h1 := hC n u τ (N k) (U k) (Tg k) hu hu0 huT htag hmesh (hU k) (hU0 k) (hUT k)
      (hTg k) hmk
    have h2 := hN₂ k hk2
    rw [Real.dist_eq, hs k] at h2
    have h3 := abs_sub_le (∑ i : Fin n, S (q + τ i) (q + u i.castSucc) (q + u i.succ))
      (∑ i : Fin (N k), S (q + Tg k i) (q + U k i.castSucc) (q + U k i.succ)) J
    show |∑ i : Fin n, S (q + τ i) (q + u i.castSucc) (q + u i.succ) - J| < ε
    linarith

#print axioms fp81s21_rs_restrict

end HRS.Fp81.S21

end
