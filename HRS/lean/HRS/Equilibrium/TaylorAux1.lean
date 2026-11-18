/-
# HRS.Equilibrium.TaylorAux1 — Bernstein-type even-moment inequality (Lemma 4.7, packet TAYLOR)

For independent centered variables `X_j` with `|X_j| ≤ M` and `E X_j² ≤ σ²`,
`E (∑_{j∈J} X_j)^{2q} ≤ kb q (|J| σ² + M²)^q` with the explicit constant `kb q = 4^{q(q+1)/2}`.
This is the bounded-summand form of the even-moment inequality `R:eq:even-moment` (source line
4328); the truncation level of the summands is built into `M`.
-/
import Mathlib

open MeasureTheory ProbabilityTheory
open scoped ENNReal

set_option linter.unusedSectionVars false

noncomputable section

namespace HRS.TaylorAux

/-- The explicit constant `kb q = 4^{q(q+1)/2}`. -/
def taylor_kb : ℕ → ℝ
  | 0 => 1
  | (q + 1) => 4 ^ (q + 1) * taylor_kb q

theorem taylor_kb_one_le (q : ℕ) : 1 ≤ taylor_kb q := by
  induction q with
  | zero => simp [taylor_kb]
  | succ q ih =>
    simp only [taylor_kb]
    have : (1 : ℝ) ≤ 4 ^ (q + 1) := one_le_pow₀ (by norm_num)
    nlinarith

theorem taylor_kb_mono : Monotone taylor_kb := by
  refine monotone_nat_of_le_succ fun q => ?_
  simp only [taylor_kb]
  have h1 := taylor_kb_one_le q
  have : (1 : ℝ) ≤ 4 ^ (q + 1) := one_le_pow₀ (by norm_num)
  nlinarith

section Abstract

variable {Ω ι : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  [DecidableEq ι]

/-- The partial sum over a finite index set. -/
def taylor_S (X : ι → Ω → ℝ) (J : Finset ι) (ω : Ω) : ℝ := ∑ j ∈ J, X j ω

theorem taylor_S_measurable {X : ι → Ω → ℝ} (hm : ∀ j, Measurable (X j)) (J : Finset ι) :
    Measurable (taylor_S X J) :=
  Finset.measurable_sum _ fun j _ => hm j

theorem taylor_S_bdd {X : ι → Ω → ℝ} {M : ℝ} (hb : ∀ j ω, |X j ω| ≤ M) (J : Finset ι)
    (ω : Ω) : |taylor_S X J ω| ≤ J.card * M := by
  unfold taylor_S
  calc |∑ j ∈ J, X j ω| ≤ ∑ j ∈ J, |X j ω| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j ∈ J, M := Finset.sum_le_sum fun j _ => hb j ω
    _ = _ := by simp

theorem taylor_integrable_of_bdd {f : Ω → ℝ} (hf : Measurable f) {B : ℝ} (hb : ∀ ω, |f ω| ≤ B) :
    Integrable f P :=
  Integrable.of_bound hf.aestronglyMeasurable B (Filter.Eventually.of_forall fun ω => by
    simpa [Real.norm_eq_abs] using hb ω)

variable {X : ι → Ω → ℝ}

/-- Moment of a single bounded summand: `|x|^k ≤ M^{k-2} x²` for `k ≥ 2`. -/
theorem taylor_abs_pow_le {x M : ℝ} (hx : |x| ≤ M) (k : ℕ) (hk : 2 ≤ k) :
    |x| ^ k ≤ M ^ (k - 2) * x ^ 2 := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
  simp only [Nat.add_sub_cancel]
  rw [pow_add, sq_abs]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) hx m) (sq_nonneg _)

/-- One step of the recursion. -/
theorem taylor_step (hX : iIndepFun X P) (hm : ∀ j, Measurable (X j)) {M σ2 : ℝ}
    (hM : 0 < M) (hσ : 0 ≤ σ2) (hb : ∀ j ω, |X j ω| ≤ M) (h0 : ∀ j, ∫ ω, X j ω ∂P = 0)
    (hv : ∀ j, ∫ ω, X j ω ^ 2 ∂P ≤ σ2) (r : ℕ)
    (hlow : ∀ j ≤ 2 * r, ∀ J : Finset ι,
      ∫ ω, |taylor_S X J ω| ^ j ∂P ≤ taylor_kb r * Real.sqrt (J.card * σ2 + M ^ 2) ^ j)
    (J : Finset ι) (a : ι) (ha : a ∉ J)
    (hJ : ∫ ω, taylor_S X J ω ^ (2 * r + 2) ∂P ≤
      taylor_kb (r + 1) * Real.sqrt (J.card * σ2 + M ^ 2) ^ (2 * r + 2)) :
    ∫ ω, taylor_S X (insert a J) ω ^ (2 * r + 2) ∂P ≤
      taylor_kb (r + 1) * Real.sqrt ((insert a J).card * σ2 + M ^ 2) ^ (2 * r + 2) := by
  set m : ℕ := 2 * r + 2 with hmdef
  set t : ℝ := Real.sqrt (J.card * σ2 + M ^ 2) with ht
  have hu : 0 ≤ (J.card : ℝ) * σ2 + M ^ 2 := by positivity
  have ht2 : t ^ 2 = J.card * σ2 + M ^ 2 := Real.sq_sqrt hu
  have hMt : M ≤ t := by
    rw [ht]; apply Real.le_sqrt_of_sq_le
    nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) J.card) hσ]
  have ht0 : 0 < t := lt_of_lt_of_le hM hMt
  have hcard : ((insert a J).card : ℝ) = J.card + 1 := by
    rw [Finset.card_insert_of_notMem ha]; push_cast; ring
  -- notation
  set S := taylor_S X J with hS
  have hSm : Measurable S := taylor_S_measurable hm J
  have hSb : ∀ ω, |S ω| ≤ J.card * M := taylor_S_bdd hb J
  have hins : ∀ ω, taylor_S X (insert a J) ω = X a ω + S ω := by
    intro ω; unfold taylor_S; rw [Finset.sum_insert ha]; rfl
  have hind : S ⟂ᵢ[P] X a := by
    have h1 := hX.indepFun_finsetSum_of_notMem hm ha
    have h2 : S = ∑ j ∈ J, X j := by
      ext ω; simp [hS, taylor_S]
    rw [h2]; exact h1
  -- expansion
  have hexp : ∀ ω, taylor_S X (insert a J) ω ^ m =
      ∑ k ∈ Finset.range (m + 1), (X a ω ^ k * S ω ^ (m - k) * (m.choose k : ℝ)) := by
    intro ω; rw [hins, add_pow]
  have hint : ∀ k, Integrable (fun ω => X a ω ^ k * S ω ^ (m - k) * (m.choose k : ℝ)) P := by
    intro k
    refine taylor_integrable_of_bdd (((hm a).pow_const k).mul ((hSm).pow_const _) |>.mul_const _)
      (B := M ^ k * ((J.card : ℝ) * M) ^ (m - k) * (m.choose k : ℝ)) fun ω => ?_
    rw [abs_mul, abs_mul, abs_pow, abs_pow, Nat.abs_cast]
    gcongr
    · exact hb a ω
    · exact hSb ω
  have hsplit : ∫ ω, taylor_S X (insert a J) ω ^ m ∂P =
      ∑ k ∈ Finset.range (m + 1), (m.choose k : ℝ) * ((∫ ω, X a ω ^ k ∂P) *
        ∫ ω, S ω ^ (m - k) ∂P) := by
    simp_rw [hexp]
    rw [integral_finsetSum _ fun k _ => hint k]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hik : IndepFun (fun ω => X a ω ^ k) (fun ω => S ω ^ (m - k)) P :=
      (hind.symm).comp (measurable_id.pow_const k) (measurable_id.pow_const (m - k))
    have e1 : ∫ ω, X a ω ^ k * S ω ^ (m - k) * (m.choose k : ℝ) ∂P =
        (∫ ω, X a ω ^ k * S ω ^ (m - k) ∂P) * (m.choose k : ℝ) := integral_mul_const _ _
    rw [e1, hik.integral_fun_mul_eq_mul_integral
      (((hm a).pow_const k).aestronglyMeasurable) ((hSm.pow_const _).aestronglyMeasurable)]
    ring
  -- bound the terms
  have hk0 : (∫ ω, X a ω ^ 0 ∂P) * ∫ ω, S ω ^ (m - 0) ∂P = ∫ ω, S ω ^ m ∂P := by simp
  have hk1 : (∫ ω, X a ω ^ 1 ∂P) * ∫ ω, S ω ^ (m - 1) ∂P = 0 := by simp [h0 a]
  have hterm : ∀ k ∈ Finset.Icc 2 m, (m.choose k : ℝ) * ((∫ ω, X a ω ^ k ∂P) *
        ∫ ω, S ω ^ (m - k) ∂P) ≤ (m.choose k : ℝ) * (σ2 * taylor_kb r * t ^ (m - 2)) := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
    have hXk : |∫ ω, X a ω ^ k ∂P| ≤ M ^ (k - 2) * σ2 := by
      calc |∫ ω, X a ω ^ k ∂P| ≤ ∫ ω, |X a ω ^ k| ∂P := abs_integral_le_integral_abs
        _ = ∫ ω, |X a ω| ^ k ∂P := by simp_rw [abs_pow]
        _ ≤ ∫ ω, M ^ (k - 2) * X a ω ^ 2 ∂P := by
            refine integral_mono ?_ ?_ fun ω => taylor_abs_pow_le (hb a ω) k hk.1
            · exact taylor_integrable_of_bdd (((hm a).abs).pow_const k) (B := M ^ k)
                fun ω => by
                  rw [abs_pow, abs_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hb a ω) k
            · exact taylor_integrable_of_bdd (((hm a).pow_const 2).const_mul _) (B := M ^ (k - 2) * M ^ 2)
                fun ω => by
                  rw [abs_mul, abs_pow, abs_pow]
                  gcongr
                  · exact abs_of_nonneg hM.le |>.le
                  · exact hb a ω
        _ = M ^ (k - 2) * ∫ ω, X a ω ^ 2 ∂P := integral_const_mul _ _
        _ ≤ M ^ (k - 2) * σ2 := mul_le_mul_of_nonneg_left (hv a) (by positivity)
    have hSk : |∫ ω, S ω ^ (m - k) ∂P| ≤ taylor_kb r * t ^ (m - k) := by
      calc |∫ ω, S ω ^ (m - k) ∂P| ≤ ∫ ω, |S ω ^ (m - k)| ∂P := abs_integral_le_integral_abs
        _ = ∫ ω, |S ω| ^ (m - k) ∂P := by simp_rw [abs_pow]
        _ ≤ _ := hlow (m - k) (by omega) J
    calc (∫ ω, X a ω ^ k ∂P) * ∫ ω, S ω ^ (m - k) ∂P
        ≤ |(∫ ω, X a ω ^ k ∂P) * ∫ ω, S ω ^ (m - k) ∂P| := le_abs_self _
      _ = |∫ ω, X a ω ^ k ∂P| * |∫ ω, S ω ^ (m - k) ∂P| := abs_mul _ _
      _ ≤ (M ^ (k - 2) * σ2) * (taylor_kb r * t ^ (m - k)) :=
          mul_le_mul hXk hSk (abs_nonneg _) (by positivity)
      _ = σ2 * taylor_kb r * (M ^ (k - 2) * t ^ (m - k)) := by ring
      _ ≤ σ2 * taylor_kb r * t ^ (m - 2) := by
          refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hσ (by linarith [taylor_kb_one_le r]))
          calc M ^ (k - 2) * t ^ (m - k) ≤ t ^ (k - 2) * t ^ (m - k) := by gcongr
            _ = t ^ (m - 2) := by rw [← pow_add]; congr 1; omega
  -- assemble
  have hsum : ∫ ω, taylor_S X (insert a J) ω ^ m ∂P ≤
      ∫ ω, S ω ^ m ∂P + σ2 * taylor_kb r * t ^ (m - 2) * 4 ^ (r + 1) := by
    rw [hsplit]
    have hrange : Finset.range (m + 1) = insert 0 (insert 1 (Finset.Icc 2 m)) := by
      ext k; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega
    rw [hrange, Finset.sum_insert (by simp), Finset.sum_insert (by simp)]
    simp only [Nat.choose_zero_right, Nat.cast_one, one_mul, Nat.choose_one_right, hk0, hk1,
      mul_zero, zero_add]
    gcongr
    calc ∑ k ∈ Finset.Icc 2 m, (m.choose k : ℝ) * ((∫ ω, X a ω ^ k ∂P) * ∫ ω, S ω ^ (m - k) ∂P)
        ≤ ∑ k ∈ Finset.Icc 2 m, (m.choose k : ℝ) * (σ2 * taylor_kb r * t ^ (m - 2)) :=
          Finset.sum_le_sum hterm
      _ = (∑ k ∈ Finset.Icc 2 m, (m.choose k : ℝ)) * (σ2 * taylor_kb r * t ^ (m - 2)) := by
          rw [Finset.sum_mul]
      _ ≤ 4 ^ (r + 1) * (σ2 * taylor_kb r * t ^ (m - 2)) := by
          refine mul_le_mul_of_nonneg_right ?_ (by
            have := taylor_kb_one_le r
            positivity)
          have h1 : ∑ k ∈ Finset.Icc 2 m, (m.choose k : ℝ) ≤ ∑ k ∈ Finset.range (m + 1), (m.choose k : ℝ) := by
            refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => Nat.cast_nonneg _
            intro k hk; simp only [Finset.mem_Icc, Finset.mem_range] at hk ⊢; omega
          have h2 : ∑ k ∈ Finset.range (m + 1), (m.choose k : ℝ) = 2 ^ m := by
            exact_mod_cast Nat.sum_range_choose m
          have h3 : (2 : ℝ) ^ m = 4 ^ (r + 1) := by
            rw [hmdef, show 2 * r + 2 = 2 * (r + 1) by ring, pow_mul]; norm_num
          linarith
      _ = _ := by ring
  -- final comparison
  have hkb : taylor_kb (r + 1) = 4 ^ (r + 1) * taylor_kb r := rfl
  have hcast : ((insert a J).card : ℝ) * σ2 + M ^ 2 = t ^ 2 + σ2 := by rw [hcard, ht2]; ring
  have hsq : Real.sqrt ((insert a J).card * σ2 + M ^ 2) ^ m = (t ^ 2 + σ2) ^ (r + 1) := by
    rw [hcast, hmdef, show 2 * r + 2 = 2 * (r + 1) by ring, pow_mul, Real.sq_sqrt (by positivity)]
  rw [hsq]
  have hpow : t ^ (2 * r + 2) + σ2 * t ^ (m - 2) ≤ (t ^ 2 + σ2) ^ (r + 1) := by
    have e1 : t ^ (2 * r + 2) = (t ^ 2) ^ (r + 1) := by rw [← pow_mul]; ring_nf
    have e2 : t ^ (m - 2) = (t ^ 2) ^ r := by rw [hmdef, ← pow_mul]; congr 1
    rw [e1, e2, pow_succ (t ^ 2 + σ2) r]
    calc (t ^ 2) ^ (r + 1) + σ2 * (t ^ 2) ^ r = (t ^ 2) ^ r * (t ^ 2 + σ2) := by ring
      _ ≤ (t ^ 2 + σ2) ^ r * (t ^ 2 + σ2) := by
          gcongr
          linarith
  calc ∫ ω, taylor_S X (insert a J) ω ^ (2 * r + 2) ∂P
      ≤ ∫ ω, S ω ^ m ∂P + σ2 * taylor_kb r * t ^ (m - 2) * 4 ^ (r + 1) := hsum
    _ ≤ taylor_kb (r + 1) * t ^ (2 * r + 2) + σ2 * taylor_kb r * t ^ (m - 2) * 4 ^ (r + 1) := by
        gcongr
    _ = taylor_kb (r + 1) * (t ^ (2 * r + 2) + σ2 * t ^ (m - 2)) := by rw [hkb]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hpow (by linarith [taylor_kb_one_le (r + 1)])

/-- Odd moments from the two neighbouring even ones (AM-GM with the scale `t`). -/
theorem taylor_odd_moment (hm : ∀ j, Measurable (X j)) {M σ2 : ℝ}
    (hM : 0 < M) (hσ : 0 ≤ σ2) (hb : ∀ j ω, |X j ω| ≤ M) (a : ℕ) (J : Finset ι)
    (h1 : ∫ ω, taylor_S X J ω ^ (2 * a) ∂P ≤
      taylor_kb a * Real.sqrt (J.card * σ2 + M ^ 2) ^ (2 * a))
    (h2 : ∫ ω, taylor_S X J ω ^ (2 * a + 2) ∂P ≤
      taylor_kb (a + 1) * Real.sqrt (J.card * σ2 + M ^ 2) ^ (2 * a + 2)) :
    ∫ ω, |taylor_S X J ω| ^ (2 * a + 1) ∂P ≤
      taylor_kb (a + 1) * Real.sqrt (J.card * σ2 + M ^ 2) ^ (2 * a + 1) := by
  set t : ℝ := Real.sqrt (J.card * σ2 + M ^ 2) with ht
  have hu : 0 ≤ (J.card : ℝ) * σ2 + M ^ 2 := by positivity
  have ht2 : t ^ 2 = J.card * σ2 + M ^ 2 := Real.sq_sqrt hu
  have hMt : M ≤ t := by
    rw [ht]; apply Real.le_sqrt_of_sq_le
    nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) J.card) hσ]
  have ht0 : 0 < t := lt_of_lt_of_le hM hMt
  have hSm : Measurable (taylor_S X J) := taylor_S_measurable hm J
  have hSb : ∀ ω, |taylor_S X J ω| ≤ J.card * M := taylor_S_bdd hb J
  have hpt : ∀ ω, |taylor_S X J ω| ^ (2 * a + 1) ≤
      (1 / 2) * (t * taylor_S X J ω ^ (2 * a) + t⁻¹ * taylor_S X J ω ^ (2 * a + 2)) := by
    intro ω
    set s := taylor_S X J ω
    have e1 : s ^ (2 * a) = |s| ^ (2 * a) := by rw [pow_mul, pow_mul, sq_abs]
    have e2 : s ^ (2 * a + 2) = |s| ^ (2 * a) * |s| ^ 2 := by
      rw [pow_add, e1, sq_abs]
    rw [e1, e2, pow_succ]
    have hA : 0 ≤ |s| ^ (2 * a) := by positivity
    have : 2 * |s| ≤ t + t⁻¹ * |s| ^ 2 := by
      have h3 : 0 ≤ (t - |s|) ^ 2 := sq_nonneg _
      have h4 : t⁻¹ * (t - |s|) ^ 2 = t - 2 * |s| + t⁻¹ * |s| ^ 2 := by
        field_simp; ring
      have h5 : 0 ≤ t⁻¹ * (t - |s|) ^ 2 := by positivity
      linarith
    calc |s| ^ (2 * a) * |s| = (1 / 2) * (|s| ^ (2 * a) * (2 * |s|)) := by ring
      _ ≤ (1 / 2) * (|s| ^ (2 * a) * (t + t⁻¹ * |s| ^ 2)) := by gcongr
      _ = _ := by ring
  have hI1 : Integrable (fun ω => taylor_S X J ω ^ (2 * a)) P :=
    taylor_integrable_of_bdd (hSm.pow_const _) (B := ((J.card : ℝ) * M) ^ (2 * a)) fun ω => by
      rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hSb ω) _
  have hI2 : Integrable (fun ω => taylor_S X J ω ^ (2 * a + 2)) P :=
    taylor_integrable_of_bdd (hSm.pow_const _) (B := ((J.card : ℝ) * M) ^ (2 * a + 2)) fun ω => by
      rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hSb ω) _
  have hI0 : Integrable (fun ω => |taylor_S X J ω| ^ (2 * a + 1)) P :=
    taylor_integrable_of_bdd (hSm.abs.pow_const _) (B := ((J.card : ℝ) * M) ^ (2 * a + 1)) fun ω => by
      rw [abs_pow, abs_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hSb ω) _
  calc ∫ ω, |taylor_S X J ω| ^ (2 * a + 1) ∂P
      ≤ ∫ ω, (1 / 2) * (t * taylor_S X J ω ^ (2 * a) + t⁻¹ * taylor_S X J ω ^ (2 * a + 2)) ∂P :=
        integral_mono hI0 (((hI1.const_mul t).add (hI2.const_mul t⁻¹)).const_mul _) hpt
    _ = (1 / 2) * (t * ∫ ω, taylor_S X J ω ^ (2 * a) ∂P +
          t⁻¹ * ∫ ω, taylor_S X J ω ^ (2 * a + 2) ∂P) := by
        rw [integral_const_mul, integral_add (hI1.const_mul t) (hI2.const_mul t⁻¹),
          integral_const_mul, integral_const_mul]
    _ ≤ (1 / 2) * (t * (taylor_kb a * t ^ (2 * a)) +
          t⁻¹ * (taylor_kb (a + 1) * t ^ (2 * a + 2))) := by
        gcongr
    _ = (1 / 2) * (taylor_kb a + taylor_kb (a + 1)) * t ^ (2 * a + 1) := by
        field_simp; ring
    _ ≤ taylor_kb (a + 1) * t ^ (2 * a + 1) := by
        have := taylor_kb_mono (Nat.le_succ a)
        have h0 : 0 ≤ t ^ (2 * a + 1) := by positivity
        nlinarith

/-- The Bernstein-type even-moment inequality (abstract form). -/
theorem taylor_moment_all (hX : iIndepFun X P) (hm : ∀ j, Measurable (X j)) {M σ2 : ℝ}
    (hM : 0 < M) (hσ : 0 ≤ σ2) (hb : ∀ j ω, |X j ω| ≤ M) (h0 : ∀ j, ∫ ω, X j ω ∂P = 0)
    (hv : ∀ j, ∫ ω, X j ω ^ 2 ∂P ≤ σ2) :
    ∀ r : ℕ, ∀ J : Finset ι, ∫ ω, taylor_S X J ω ^ (2 * r) ∂P ≤
      taylor_kb r * Real.sqrt (J.card * σ2 + M ^ 2) ^ (2 * r) := by
  intro r
  induction r using Nat.strong_induction_on with
  | _ r ih =>
    rcases r with _ | r'
    · intro J; simp [taylor_kb]
    · have hlow : ∀ j ≤ 2 * r', ∀ J : Finset ι,
          ∫ ω, |taylor_S X J ω| ^ j ∂P ≤ taylor_kb r' * Real.sqrt (J.card * σ2 + M ^ 2) ^ j := by
        intro j hj J
        have ht0 : 0 ≤ Real.sqrt (J.card * σ2 + M ^ 2) := Real.sqrt_nonneg _
        obtain ⟨a, rfl | rfl⟩ := Nat.even_or_odd' j
        · have h := ih a (by omega) J
          have e : ∀ ω, |taylor_S X J ω| ^ (2 * a) = taylor_S X J ω ^ (2 * a) := fun ω => by
            rw [pow_mul, pow_mul, sq_abs]
          simp_rw [e]
          refine h.trans ?_
          have := taylor_kb_mono (show a ≤ r' by omega)
          gcongr
        · have h1 := ih a (by omega) J
          have h2 := ih (a + 1) (by omega) J
          have := taylor_odd_moment hm hM hσ hb a J h1 (by rw [show 2 * (a + 1) = 2 * a + 2 by ring] at h2; exact h2)
          refine this.trans ?_
          have := taylor_kb_mono (show a + 1 ≤ r' by omega)
          gcongr
      intro J
      induction J using Finset.induction_on with
      | empty =>
        have e0 : ∀ ω, taylor_S X ∅ ω = 0 := fun ω => by simp [taylor_S]
        simp only [e0]
        have := taylor_kb_one_le (r' + 1)
        simp only [Finset.card_empty, Nat.cast_zero, zero_mul, zero_add]
        rw [zero_pow (by omega), integral_zero]
        positivity
      | insert a J ha ihJ =>
        exact taylor_step hX hm hM hσ hb h0 hv r' hlow J a ha ihJ

/-- Final form: `E (∑_{j∈J} X_j)^{2q} ≤ kb q (|J| σ² + M²)^q`. -/
theorem taylor_bernstein (hX : iIndepFun X P) (hm : ∀ j, Measurable (X j)) {M σ2 : ℝ}
    (hM : 0 < M) (hσ : 0 ≤ σ2) (hb : ∀ j ω, |X j ω| ≤ M) (h0 : ∀ j, ∫ ω, X j ω ∂P = 0)
    (hv : ∀ j, ∫ ω, X j ω ^ 2 ∂P ≤ σ2) (q : ℕ) (J : Finset ι) :
    ∫ ω, taylor_S X J ω ^ (2 * q) ∂P ≤ taylor_kb q * (J.card * σ2 + M ^ 2) ^ q := by
  have := taylor_moment_all hX hm hM hσ hb h0 hv q J
  rwa [pow_mul, Real.sq_sqrt (by positivity)] at this

end Abstract

section Pi

variable {α : Type*} [MeasurableSpace α]

theorem taylor_integral_eval (μ : Measure α) [IsProbabilityMeasure μ] (n : ℕ) (j : Fin n)
    {g : α → ℝ} (hg : AEStronglyMeasurable g μ) :
    ∫ Y, g (Y j) ∂(Measure.pi fun _ : Fin n => μ) = ∫ a, g a ∂μ := by
  have h := (measurePreserving_eval (fun _ : Fin n => μ) j).map_eq
  have h2 := integral_map (μ := Measure.pi fun _ : Fin n => μ) (φ := Function.eval j)
    (measurable_pi_apply j).aemeasurable (f := g) (by rwa [h])
  rw [h] at h2
  exact h2.symm

theorem taylor_lintegral_eval (μ : Measure α) [IsProbabilityMeasure μ] (n : ℕ) (j : Fin n)
    {g : α → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ Y, g (Y j) ∂(Measure.pi fun _ : Fin n => μ) = ∫⁻ a, g a ∂μ := by
  have h := (measurePreserving_eval (fun _ : Fin n => μ) j).map_eq
  have h2 := lintegral_map (μ := Measure.pi fun _ : Fin n => μ) (f := g) (g := Function.eval j)
    hg (measurable_pi_apply j)
  rw [h] at h2
  exact h2.symm

/-- Bernstein-type inequality for i.i.d. sums over a subset `J` of the coordinates of a product
probability space. -/
theorem taylor_bernstein_pi (μ : Measure α) [IsProbabilityMeasure μ] (n : ℕ) (f : α → ℝ)
    (hf : Measurable f) {M σ2 : ℝ} (hM : 0 < M) (hσ : 0 ≤ σ2) (hb : ∀ a, |f a| ≤ M)
    (h0 : ∫ a, f a ∂μ = 0) (hv : ∫ a, f a ^ 2 ∂μ ≤ σ2) (q : ℕ) (J : Finset (Fin n)) :
    ∫ Y, (∑ j ∈ J, f (Y j)) ^ (2 * q) ∂(Measure.pi fun _ : Fin n => μ) ≤
      taylor_kb q * (J.card * σ2 + M ^ 2) ^ q := by
  have hX : iIndepFun (fun (j : Fin n) (Y : Fin n → α) => f (Y j)) (Measure.pi fun _ : Fin n => μ) :=
    iIndepFun_pi (X := fun _ => f) (fun _ => hf.aemeasurable)
  refine taylor_bernstein (X := fun (j : Fin n) (Y : Fin n → α) => f (Y j)) hX
    (fun j => hf.comp (measurable_pi_apply j)) hM hσ (fun j Y => hb _) (fun j => ?_)
    (fun j => ?_) q J
  · rw [taylor_integral_eval μ n j (g := f) hf.aestronglyMeasurable, h0]
  · rw [taylor_integral_eval μ n j (g := fun a => f a ^ 2) (hf.pow_const 2).aestronglyMeasurable]
    exact hv

end Pi

end HRS.TaylorAux
