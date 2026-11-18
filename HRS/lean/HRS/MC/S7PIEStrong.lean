import HRS.MC.S7PIEInterp
import HRS.MC.S7PIETail

/-!
# Packet PI-E, part 7: strong continuity of the transposed action in a matrix parameter

Abstract statement.  Let `T x` be matrices, indexed by a parameter `x` along a filter `l`, converging coordinatewise
to `T0`, such that the weighted matrices `w^σ T w^{-σ}` have finite-section `ℓ²` bounds uniformly in `x` at the two
exponents `n < m`.  Then for every `a` with `(w^{-m} a) ∈ ℓ²` the transposed actions `(w^{-m} ∑'_j a_j T x j k)_k`
converge in `ℓ²` to the one of `T0` (truncate `a`, use the coordinatewise convergence and the higher exponent `n`
for the finite part, and the uniform bound at `m` for the tail).
-/

open Filter Topology Finset

noncomputable section

namespace HRS.MC.Sec7.PIE

variable {ι : Type*}

/-- the row `(a_j T_{jk})_j` is summable under a finite-section bound -/
lemma pie_row_summable {w : ι → ℝ} (hw : ∀ i, 0 < w i) {T : ι → ι → ℝ} {σ A : ℝ}
    (hH : pieFinBd (pieWmat w T σ) A) (a : ι → ℝ) (ha : Summable fun j => (w j ^ (-σ) * a j) ^ 2) (k : ι) :
    Summable fun j => a j * T j k := by
  set S := pieWmat w T σ with hSdef
  set c : ι → ℝ := fun j => w j ^ (-σ) * a j with hc
  have hcolsum : Summable fun j => c j * S j k := by
    refine Summable.of_norm_bounded (g := fun j => (c j ^ 2 + S j k ^ 2) / 2)
      (((ha.add (pie_col_summable hH k))).div_const 2) fun j => ?_
    rw [Real.norm_eq_abs]
    refine abs_le.2 ⟨?_, ?_⟩ <;> nlinarith [sq_nonneg (c j - S j k), sq_nonneg (c j + S j k)]
  have hkk : w k ^ σ * w k ^ (-σ) = 1 := by
    rw [← Real.rpow_add (hw k)]; simp
  refine (hcolsum.mul_left (w k ^ σ)).congr fun j => ?_
  have hjj : w j ^ (-σ) * w j ^ σ = 1 := by
    rw [← Real.rpow_add (hw j)]; simp
  simp only [hc, hSdef, pieWmat]
  calc w k ^ σ * (w j ^ (-σ) * a j * (w j ^ σ * T j k * w k ^ (-σ)))
      = (w j ^ (-σ) * w j ^ σ) * (w k ^ σ * w k ^ (-σ)) * (a j * T j k) := by ring
    _ = a j * T j k := by rw [hjj, hkk]; ring

lemma pie_sq_add_le (p q : ℝ) : (p + q) ^ 2 ≤ 2 * p ^ 2 + 2 * q ^ 2 := by
  nlinarith [sq_nonneg (p - q)]

lemma pie_summable_add_sq {f g : ι → ℝ} (hf : Summable fun k => f k ^ 2) (hg : Summable fun k => g k ^ 2) :
    Summable (fun k => (f k + g k) ^ 2) ∧
      ∑' k, (f k + g k) ^ 2 ≤ 2 * ∑' k, f k ^ 2 + 2 * ∑' k, g k ^ 2 := by
  have hs : Summable fun k => 2 * f k ^ 2 + 2 * g k ^ 2 := (hf.mul_left 2).add (hg.mul_left 2)
  have h1 : Summable fun k => (f k + g k) ^ 2 :=
    Summable.of_nonneg_of_le (fun k => sq_nonneg _) (fun k => pie_sq_add_le _ _) hs
  refine ⟨h1, ?_⟩
  calc ∑' k, (f k + g k) ^ 2 ≤ ∑' k, (2 * f k ^ 2 + 2 * g k ^ 2) :=
        Summable.tsum_le_tsum (fun k => pie_sq_add_le _ _) h1 hs
    _ = _ := by rw [Summable.tsum_add (hf.mul_left 2) (hg.mul_left 2), tsum_mul_left, tsum_mul_left]

lemma pie_summable_sub_sq {f g : ι → ℝ} (hf : Summable fun k => f k ^ 2) (hg : Summable fun k => g k ^ 2) :
    Summable (fun k => (f k - g k) ^ 2) ∧
      ∑' k, (f k - g k) ^ 2 ≤ 2 * ∑' k, f k ^ 2 + 2 * ∑' k, g k ^ 2 := by
  have hg' : Summable fun k => (-g k) ^ 2 := hg.congr fun k => (neg_sq (g k)).symm
  have := pie_summable_add_sq hf hg'
  simpa [sub_eq_add_neg, neg_sq] using this

open Classical in
/-- Strong continuity of the transposed action in a matrix parameter (see the module doc). -/
theorem pie_strong_abs {X : Type*} (l : Filter X) (w : ι → ℝ) (hw1 : ∀ i, 1 ≤ w i)
    (hfin : ∀ R : ℝ, {i | w i ≤ R}.Finite) (T : X → ι → ι → ℝ) (T0 : ι → ι → ℝ) {m n : ℝ} (hnm : n < m)
    {A A' : ℝ} (hA : 0 ≤ A) (hA' : 0 ≤ A')
    (hAm : ∀ᶠ x in l, pieFinBd (pieWmat w (T x) m) A) (hAm0 : pieFinBd (pieWmat w T0 m) A)
    (hAn : ∀ᶠ x in l, pieFinBd (pieWmat w (T x) n) A') (hAn0 : pieFinBd (pieWmat w T0 n) A')
    (hc : ∀ j k, Tendsto (fun x => T x j k) l (𝓝 (T0 j k)))
    (a : ι → ℝ) (ha : Summable fun j => (w j ^ (-m) * a j) ^ 2) :
    Tendsto (fun x => ∑' k, (w k ^ (-m) * ((∑' j, a j * T x j k) - ∑' j, a j * T0 j k)) ^ 2) l (𝓝 0) := by
  have hw : ∀ i, 0 < w i := fun i => lt_of_lt_of_le one_pos (hw1 i)
  set c : ι → ℝ := fun j => w j ^ (-m) * a j with hcdef
  let aK : Finset ι → ι → ℝ := fun K j => if j ∈ K then a j else 0
  let bK : Finset ι → ι → ℝ := fun K j => if j ∈ K then 0 else a j
  have hab : ∀ K j, a j = aK K j + bK K j := by
    intro K j; simp only [aK, bK]; split_ifs <;> simp
  have haKs : ∀ K, Summable fun j => (w j ^ (-m) * aK K j) ^ 2 := fun K =>
    Summable.of_nonneg_of_le (fun _ => sq_nonneg _) (fun j => by
      by_cases hj : j ∈ K <;> simp [aK, hj, sq_nonneg]) ha
  have hbKs : ∀ K, Summable fun j => (w j ^ (-m) * bK K j) ^ 2 := fun K =>
    Summable.of_nonneg_of_le (fun _ => sq_nonneg _) (fun j => by
      by_cases hj : j ∈ K <;> simp [bK, hj, sq_nonneg]) ha
  rw [Metric.tendsto_nhds]
  intro ε hε
  set δ : ℝ := ε / (16 * (A ^ 2 + 1)) with hδ
  have hδ0 : 0 < δ := by positivity
  set Ctot : ℝ := ∑' j, c j ^ 2 with hCtot
  obtain ⟨K, hK⟩ : ∃ K : Finset ι, Ctot - δ < ∑ j ∈ K, c j ^ 2 := by
    have h := (tendsto_order.1 ha.hasSum).1 (Ctot - δ) (by linarith)
    exact h.exists
  -- the tail
  have hτ : ∑' j, (w j ^ (-m) * bK K j) ^ 2 < δ := by
    have e1 : ∀ j, (w j ^ (-m) * bK K j) ^ 2 = c j ^ 2 - (w j ^ (-m) * aK K j) ^ 2 := by
      intro j
      by_cases hj : j ∈ K <;> simp [aK, bK, hj, hcdef]
    have e2 : ∑' j, (w j ^ (-m) * aK K j) ^ 2 = ∑ j ∈ K, c j ^ 2 := by
      rw [tsum_eq_sum (s := K) (fun j hj => by simp [aK, hj])]
      refine Finset.sum_congr rfl fun j hj => ?_
      simp [aK, hj, hcdef]
    rw [tsum_congr e1, Summable.tsum_sub ha (haKs K), e2]
    linarith
  -- the finite part
  have hsupp : ∀ (s : ι → ℝ) (σ : ℝ), (∀ j, j ∉ K → s j = 0) → Summable fun j => (w j ^ (-σ) * s j) ^ 2 :=
    fun s σ hs => summable_of_ne_finset_zero (s := K) fun j hj => by simp [hs j hj]
  have hakK : ∀ j, j ∉ K → aK K j = 0 := fun j hj => by simp [aK, hj]
  have hP : ∀ (M : ι → ι → ℝ) k, ∑' j, aK K j * M j k = ∑ j ∈ K, a j * M j k := by
    intro M k
    rw [tsum_eq_sum (s := K) (fun j hj => by simp [aK, hj])]
    refine Finset.sum_congr rfl fun j hj => ?_
    simp [aK, hj]
  set p : ℝ := m - n with hp
  have hp0 : 0 < p := by linarith
  set B : ℝ := A' ^ 2 * ∑' j, (w j ^ (-n) * aK K j) ^ 2 with hB
  have hpm : ∀ k, w k ^ p * w k ^ (-m) = w k ^ (-n) := fun k => by
    rw [← Real.rpow_add (hw k)]; congr 1; rw [hp]; ring
  have htail := pie_tail_tendsto l w hw1 hfin
    (fun x k => w k ^ (-m) * ∑' j, aK K j * T x j k) (fun k => w k ^ (-m) * ∑' j, aK K j * T0 j k) hp0
    (fun k => by
      simp_rw [hP]
      exact tendsto_const_nhds.mul (tendsto_finsetSum _ fun j _ => (hc j k).const_mul (a j)))
    (B := B)
    (by
      filter_upwards [hAn] with x hx
      obtain ⟨h1, h2⟩ := pie_dual hw hA' hx (aK K) (hsupp _ n hakK)
      have e : ∀ k, (w k ^ p * (w k ^ (-m) * ∑' j, aK K j * T x j k)) ^ 2 =
          (w k ^ (-n) * ∑' j, aK K j * T x j k) ^ 2 := fun k => by rw [← mul_assoc, hpm]
      simp_rw [e]
      exact ⟨h1, h2⟩)
    (by
      obtain ⟨h1, h2⟩ := pie_dual hw hA' hAn0 (aK K) (hsupp _ n hakK)
      have e : ∀ k, (w k ^ p * (w k ^ (-m) * ∑' j, aK K j * T0 j k)) ^ 2 =
          (w k ^ (-n) * ∑' j, aK K j * T0 j k) ^ 2 := fun k => by rw [← mul_assoc, hpm]
      simp_rw [e]
      exact ⟨h1, h2⟩)
  obtain ⟨hsumev, hlim⟩ := htail
  have hev1 := (tendsto_order.1 hlim).2 (ε / 4) (by positivity)
  filter_upwards [hev1, hsumev, hAm] with x hx1 hs1 hxm
  beta_reduce at hx1 hs1
  obtain ⟨hQs, hQb⟩ := pie_dual hw hA hxm (bK K) (hbKs K)
  obtain ⟨hQ0s, hQ0b⟩ := pie_dual hw hA hAm0 (bK K) (hbKs K)
  have hrow : ∀ (M : ι → ι → ℝ), pieFinBd (pieWmat w M m) A → ∀ k,
      ∑' j, a j * M j k = ∑' j, aK K j * M j k + ∑' j, bK K j * M j k := by
    intro M hM k
    rw [← Summable.tsum_add (pie_row_summable hw hM (aK K) (haKs K) k)
      (pie_row_summable hw hM (bK K) (hbKs K) k)]
    refine tsum_congr fun j => ?_
    rw [← add_mul, ← hab K j]
  have hR : ∀ k, w k ^ (-m) * ((∑' j, a j * T x j k) - ∑' j, a j * T0 j k) =
      (w k ^ (-m) * ∑' j, aK K j * T x j k - w k ^ (-m) * ∑' j, aK K j * T0 j k) +
      (w k ^ (-m) * ∑' j, bK K j * T x j k - w k ^ (-m) * ∑' j, bK K j * T0 j k) := by
    intro k
    rw [hrow (T x) hxm k, hrow T0 hAm0 k]; ring
  simp_rw [hR]
  have hs2 := pie_summable_sub_sq hQs hQ0s
  have hsum := pie_summable_add_sq hs1 hs2.1
  set τ : ℝ := ∑' j, (w j ^ (-m) * bK K j) ^ 2 with hτdef
  have hA2 : 0 ≤ A ^ 2 := sq_nonneg A
  have hδε : 16 * (A ^ 2 + 1) * δ = ε := by rw [hδ]; field_simp
  have hτ1 : A ^ 2 * τ ≤ A ^ 2 * δ := mul_le_mul_of_nonneg_left hτ.le hA2
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (tsum_nonneg fun k => sq_nonneg _)]
  have hfin : ∑' k, ((w k ^ (-m) * ∑' j, aK K j * T x j k - w k ^ (-m) * ∑' j, aK K j * T0 j k) +
      (w k ^ (-m) * ∑' j, bK K j * T x j k - w k ^ (-m) * ∑' j, bK K j * T0 j k)) ^ 2 ≤
      2 * ∑' k, (w k ^ (-m) * ∑' j, aK K j * T x j k - w k ^ (-m) * ∑' j, aK K j * T0 j k) ^ 2 +
      2 * (2 * (A ^ 2 * τ) + 2 * (A ^ 2 * τ)) := by
    refine hsum.2.trans ?_
    have := hs2.2
    nlinarith [hQb, hQ0b]
  nlinarith [hfin, hx1, hδ0, hδε, hτ1]

end HRS.MC.Sec7.PIE

end
