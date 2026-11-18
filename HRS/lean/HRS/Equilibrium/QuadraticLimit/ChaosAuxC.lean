import Mathlib
import HRS.Equilibrium.QuadraticLimit.ChaosAuxB

/-!
# Lemma 7.5: consistent Cholesky factors of a covariance matrix on `ℕ` (prefix `q08c_ch_`)

For a symmetric `C` with `0 ≤ C_n` (all finite sections), there is a lower triangular
`L : ℕ → ℕ → ℝ` with `∑_k L_ik L_jk = C_ij`. Row `n` is `∑_{i<n} c_i L_i + s e_n`, where
`∑_{i<n} c_i C_ij = C_nj` (projection onto the span of the previous rows).
-/
open MeasureTheory ProbabilityTheory Matrix
open scoped NNReal RealInnerProductSpace MatrixOrder

noncomputable section
namespace HRS.Q08

/-- Coefficients of the new Cholesky row: `∑_{i<n} c_i C_ij = C_nj` for `j < n`. -/
theorem q08c_ch_coef (C : ℕ → ℕ → ℝ) (hsymm : ∀ i j, C i j = C j i)
    (hpsd : ∀ (n : ℕ) (v : ℕ → ℝ), 0 ≤ ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, v i * v j * C i j)
    (hle : ∀ (n : ℕ) (v : ℕ → ℝ), ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, v i * v j * C i j ≤
      ∑ i ∈ Finset.range n, v i ^ 2) (n : ℕ) :
    ∃ c : ℕ → ℝ, ∀ j < n, ∑ i ∈ Finset.range n, c i * C i j = C n j := by
  set M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ := Matrix.of fun i j => C i j with hMdef
  have hM : M.PosSemidef := (q08c_ch_cov_fin C hsymm hpsd hle (n + 1)).1
  set R := CFC.sqrt M with hR
  have hRR : R * R = M := CFC.sqrt_mul_sqrt_self M hM.nonneg
  have hRt : Rᵀ = R := by
    have : IsSelfAdjoint R := (CFC.sqrt_nonneg M).isSelfAdjoint
    have h := this.star_eq
    rwa [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] at h
  set s : Fin (n + 1) → EuclideanSpace ℝ (Fin (n + 1)) := fun i => WithLp.toLp 2 (fun k => R i k) with hs
  have hinner : ∀ i j, ⟪s i, s j⟫ = C i j := by
    intro i j
    have h1 : ⟪s i, s j⟫ = (R * Rᵀ) i j := by
      simp only [hs, PiLp.inner_apply, Matrix.mul_apply, Matrix.transpose_apply]
      exact Finset.sum_congr rfl fun k _ => by simp [mul_comm]
    rw [h1, hRt, hRR]; rfl
  set W : Submodule ℝ (EuclideanSpace ℝ (Fin (n + 1))) :=
    Submodule.span ℝ (Set.range fun i : Fin n => s (Fin.castSucc i)) with hW
  set x₀ := W.starProjection (s (Fin.last n)) with hx₀
  have hmem : x₀ ∈ W := Submodule.starProjection_apply_mem W _
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 hmem
  have horth : ∀ j : Fin n, ⟪s (Fin.last n) - x₀, s (Fin.castSucc j)⟫ = 0 := by
    intro j
    have h1 := Submodule.sub_starProjection_mem_orthogonal (K := W) (s (Fin.last n))
    exact Submodule.inner_right_of_mem_orthogonal (Submodule.subset_span (Set.mem_range_self (f := fun i : Fin n => s (Fin.castSucc i)) j)) h1 |> fun h => by
      rw [real_inner_comm]; exact h
  refine ⟨fun i => if h : i < n then c ⟨i, h⟩ else 0, fun j hj => ?_⟩
  have h2 : ⟪x₀, s (Fin.castSucc ⟨j, hj⟩)⟫ = C n j := by
    have := horth ⟨j, hj⟩
    rw [inner_sub_left, sub_eq_zero] at this
    rw [← this, hinner]; rfl
  rw [← hc, sum_inner] at h2
  rw [← h2, Finset.sum_range]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_smul_left, hinner]
  simp [i.2]


/-- Invariant of the Cholesky construction after `n` rows. -/
def q08c_ch_P (C : ℕ → ℕ → ℝ) (n : ℕ) (S : ℕ → ℕ → ℝ) : Prop :=
  (∀ i k, i < k → S i k = 0) ∧
    ∀ i j, i < n → j < n → ∀ N, n ≤ N → ∑ k ∈ Finset.range N, S i k * S j k = C i j

theorem q08c_ch_pivot (C : ℕ → ℕ → ℝ) (hsymm : ∀ i j, C i j = C j i)
    (hpsd : ∀ (n : ℕ) (v : ℕ → ℝ), 0 ≤ ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, v i * v j * C i j)
    (n : ℕ) (c : ℕ → ℝ) (hc : ∀ j < n, ∑ i ∈ Finset.range n, c i * C i j = C n j) :
    0 ≤ C n n - ∑ i ∈ Finset.range n, c i * C n i := by
  set v : ℕ → ℝ := fun i => if i < n then c i else -1 with hv
  have h := hpsd (n + 1) v
  have hvn : v n = -1 := by simp [hv]
  have hvi : ∀ i ∈ Finset.range n, v i = c i := fun i hi => by simp [hv, Finset.mem_range.1 hi]
  rw [Finset.sum_range_succ] at h
  simp only [Finset.sum_range_succ, hvn] at h
  have e1 : ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, v i * v j * C i j =
      ∑ i ∈ Finset.range n, c i * C n i := by
    have : ∀ i ∈ Finset.range n, ∑ j ∈ Finset.range n, v i * v j * C i j = c i * C n i := by
      intro i hi
      have hi' : i < n := Finset.mem_range.1 hi
      rw [hvi i hi]
      have := hc i hi'
      rw [← this, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [hvi j hj, hsymm i j]; ring
    rw [Finset.sum_congr rfl this]
  have e2 : ∑ i ∈ Finset.range n, v i * (-1) * C i n = - ∑ i ∈ Finset.range n, c i * C n i := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [hvi i hi, hsymm i n]; ring
  have e3 : ∑ j ∈ Finset.range n, (-1 : ℝ) * v j * C n j = - ∑ i ∈ Finset.range n, c i * C n i := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [hvi i hi]; ring
  rw [Finset.sum_add_distrib, e1, e2, e3] at h
  nlinarith [h]


theorem q08c_ch_extend (C : ℕ → ℕ → ℝ) (hsymm : ∀ i j, C i j = C j i)
    (hpsd : ∀ (n : ℕ) (v : ℕ → ℝ), 0 ≤ ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, v i * v j * C i j)
    (hle : ∀ (n : ℕ) (v : ℕ → ℝ), ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, v i * v j * C i j ≤
      ∑ i ∈ Finset.range n, v i ^ 2) (n : ℕ) (S : ℕ → ℕ → ℝ) (hS : q08c_ch_P C n S) :
    ∃ S' : ℕ → ℕ → ℝ, q08c_ch_P C (n + 1) S' ∧ ∀ i < n, S' i = S i := by
  obtain ⟨c, hc⟩ := q08c_ch_coef C hsymm hpsd hle n
  have ht := q08c_ch_pivot C hsymm hpsd n c hc
  set t := C n n - ∑ i ∈ Finset.range n, c i * C n i with htdef
  set s := Real.sqrt t with hsdef
  have hss : s * s = t := Real.mul_self_sqrt ht
  set r : ℕ → ℝ := fun k => ∑ i ∈ Finset.range n, c i * S i k + if k = n then s else 0 with hr
  have hSn : ∀ j < n, S j n = 0 := fun j hj => hS.1 j n hj
  have g1 : ∀ j < n, ∀ N, n + 1 ≤ N → ∑ k ∈ Finset.range N, r k * S j k = C n j := by
    intro j hj N hN
    have e : ∀ k, r k * S j k = (∑ i ∈ Finset.range n, c i * (S i k * S j k)) +
        (if k = n then s * S j k else 0) := by
      intro k
      simp only [hr, add_mul, Finset.sum_mul]
      congr 1
      · exact Finset.sum_congr rfl fun i _ => by ring
      · split_ifs <;> simp
    simp_rw [e]
    rw [Finset.sum_add_distrib, Finset.sum_comm]
    have h1 : ∀ i ∈ Finset.range n, ∑ k ∈ Finset.range N, c i * (S i k * S j k) = c i * C i j := by
      intro i hi
      rw [← Finset.mul_sum, hS.2 i j (Finset.mem_range.1 hi) hj N (by omega)]
    rw [Finset.sum_congr rfl h1, hc j hj]
    have : ∑ k ∈ Finset.range N, (if k = n then s * S j k else 0) = 0 := by
      rw [Finset.sum_ite_eq' (Finset.range N) n (fun k => s * S j k)]
      rw [if_pos (Finset.mem_range.2 (by omega)), hSn j hj, mul_zero]
    rw [this, add_zero]
  have hrn : r n = s := by
    simp only [hr, if_true]
    rw [Finset.sum_eq_zero (fun i hi => by rw [hSn i (Finset.mem_range.1 hi), mul_zero]), zero_add]
  have g2 : ∀ N, n + 1 ≤ N → ∑ k ∈ Finset.range N, r k * r k = C n n := by
    intro N hN
    have e : ∀ k, r k * r k = (∑ i ∈ Finset.range n, c i * (r k * S i k)) +
        (if k = n then r k * s else 0) := by
      intro k
      have hrk : r k = ∑ i ∈ Finset.range n, c i * S i k + (if k = n then s else 0) := rfl
      calc r k * r k = r k * (∑ i ∈ Finset.range n, c i * S i k) + r k * (if k = n then s else 0) := by
            rw [← mul_add, ← hrk]
        _ = _ := by
          congr 1
          · rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
          · split_ifs <;> simp
    simp_rw [e]
    rw [Finset.sum_add_distrib, Finset.sum_comm]
    have h1 : ∀ i ∈ Finset.range n, ∑ k ∈ Finset.range N, c i * (r k * S i k) = c i * C n i := by
      intro i hi
      rw [← Finset.mul_sum, g1 i (Finset.mem_range.1 hi) N hN]
    rw [Finset.sum_congr rfl h1]
    have : ∑ k ∈ Finset.range N, (if k = n then r k * s else 0) = s * s := by
      rw [Finset.sum_ite_eq' (Finset.range N) n (fun k => r k * s)]
      rw [if_pos (Finset.mem_range.2 (by omega)), hrn]
    rw [this, hss, htdef]; ring
  refine ⟨fun i => if i = n then r else S i, ⟨?_, ?_⟩, fun i hi => by simp [hi.ne]⟩
  · intro i k hik
    by_cases hi : i = n
    · subst hi
      simp only [if_true, hr]
      rw [Finset.sum_eq_zero (fun j hj => by rw [hS.1 j k (lt_trans (Finset.mem_range.1 hj) hik), mul_zero]),
        zero_add, if_neg hik.ne']
    · simp only [hi, if_false]; exact hS.1 i k hik
  · intro i j hi hj N hN
    by_cases hin : i = n <;> by_cases hjn : j = n
    · subst hin; subst hjn; simp only [if_true]; exact g2 N hN
    · subst hin; simp only [if_true, hjn, if_false]
      exact g1 j (by omega) N hN
    · subst hjn; simp only [if_true, hin, if_false]
      rw [Finset.sum_congr rfl (fun k _ => mul_comm _ _), g1 i (by omega) N hN, hsymm]
    · simp only [hin, hjn, if_false]
      exact hS.2 i j (by omega) (by omega) N (by omega)


/-- Consistent (lower triangular) Cholesky factor of a covariance matrix on `ℕ`. -/
theorem q08c_ch_cholesky (C : ℕ → ℕ → ℝ) (hsymm : ∀ i j, C i j = C j i)
    (hpsd : ∀ (n : ℕ) (v : ℕ → ℝ), 0 ≤ ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, v i * v j * C i j)
    (hle : ∀ (n : ℕ) (v : ℕ → ℝ), ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, v i * v j * C i j ≤
      ∑ i ∈ Finset.range n, v i ^ 2) :
    ∃ L : ℕ → ℕ → ℝ, (∀ i k, i < k → L i k = 0) ∧
      ∀ i j N, i < N → j < N → ∑ k ∈ Finset.range N, L i k * L j k = C i j := by
  choose step hP hold using q08c_ch_extend C hsymm hpsd hle
  have P0 : q08c_ch_P C 0 (fun _ _ => 0) := ⟨fun _ _ _ => rfl, fun i j hi => absurd hi (Nat.not_lt_zero _)⟩
  let seq : (n : ℕ) → {S : ℕ → ℕ → ℝ // q08c_ch_P C n S} := fun n =>
    Nat.rec ⟨fun _ _ => 0, P0⟩ (fun m (S : {S : ℕ → ℕ → ℝ // q08c_ch_P C m S}) =>
      (⟨step m S.1 S.2, hP m S.1 S.2⟩ : {S : ℕ → ℕ → ℝ // q08c_ch_P C (m + 1) S})) n
  have hseq : ∀ m, (seq (m + 1)).1 = step m (seq m).1 (seq m).2 := fun m => rfl
  set L : ℕ → ℕ → ℝ := fun i => (seq (i + 1)).1 i with hL
  have stab : ∀ m i, i < m → (seq m).1 i = L i := by
    intro m i hi
    induction m, (Nat.succ_le_of_lt hi) using Nat.le_induction with
    | base => rfl
    | succ m hm ih =>
      rw [hseq, hold m (seq m).1 (seq m).2 i (by omega)]
      exact ih (by omega)
  refine ⟨L, fun i k hik => ?_, fun i j N hi hj => ?_⟩
  · exact (seq (i + 1)).2.1 i k hik
  · have := (seq N).2.2 i j hi hj N le_rfl
    rwa [stab N i hi, stab N j hj] at this

end HRS.Q08
