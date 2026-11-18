import Mathlib
import HRS.Equilibrium.QuadraticLimit.ChaosAuxA

/-!
# Lemma 7.5: second moment of Wick-centred quadratic forms (prefix `q08c_ch_`)

`E[(½ ∑ A_ij (z_i z_j - C_ij))²] ≤ ½ ∑ A_ij²` under `N(0,C)`, `0 ≤ C ≤ I`: spectral decomposition of
`A`, the pair formula of `ChaosAuxA`, and `‖C‖_op ≤ 1`.
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped NNReal RealInnerProductSpace

noncomputable section
namespace HRS.Q08

variable {n : ℕ}

theorem q08c_ch_q_smul (C : Matrix (Fin n) (Fin n) ℝ) (t : ℝ) (w : Fin n → ℝ) :
    q08c_ch_q C (t • w) = t ^ 2 * q08c_ch_q C w := by
  simp only [q08c_ch_q, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem q08c_ch_cs {C : Matrix (Fin n) (Fin n) ℝ} (hS : C.PosSemidef) (x y : Fin n → ℝ) :
    (∑ i, ∑ j, x i * y j * C i j) ^ 2 ≤ q08c_ch_q C x * q08c_ch_q C y := by
  have h := discrim_le_zero (a := q08c_ch_q C y) (b := 2 * ∑ i, ∑ j, x i * y j * C i j)
    (c := q08c_ch_q C x) (fun t => by
      have h0 := q08c_ch_lin_nonneg hS (x + t • y)
      rw [q08c_ch_q_add hS, q08c_ch_q_smul] at h0
      have e : ∑ i, ∑ j, x i * (t • y) j * C i j = t * ∑ i, ∑ j, x i * y j * C i j := by
        simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
      rw [e] at h0
      nlinarith [h0])
  unfold discrim at h
  nlinarith [h]

theorem q08c_ch_opnorm {C : Matrix (Fin n) (Fin n) ℝ} (hS : C.PosSemidef)
    (hle : ∀ w : Fin n → ℝ, q08c_ch_q C w ≤ ∑ i, w i ^ 2) (x : Fin n → ℝ) :
    ∑ j, (∑ i, x i * C i j) ^ 2 ≤ ∑ i, x i ^ 2 := by
  set y : Fin n → ℝ := fun j => ∑ i, x i * C i j with hy
  set N := ∑ j, y j ^ 2 with hN
  have hb : ∑ i, ∑ j, x i * y j * C i j = N := by
    calc ∑ i, ∑ j, x i * y j * C i j = ∑ j, ∑ i, x i * y j * C i j := Finset.sum_comm
      _ = ∑ j, y j * y j := by
        refine Finset.sum_congr rfl fun j _ => ?_
        have hyj : y j = ∑ i, x i * C i j := rfl
        calc ∑ i, x i * y j * C i j = y j * ∑ i, x i * C i j := by
              rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
          _ = y j * y j := by rw [← hyj]
      _ = N := by simp [hN, sq]
  have h1 := q08c_ch_cs hS x y
  rw [hb] at h1
  have h2 := hle x
  have h3 := hle y
  have h4 := q08c_ch_lin_nonneg hS x
  have h5 := q08c_ch_lin_nonneg hS y
  have hN0 : 0 ≤ N := Finset.sum_nonneg fun j _ => sq_nonneg _
  by_cases h0 : N = 0
  · rw [h0]; exact Finset.sum_nonneg fun j _ => sq_nonneg _
  · have hpos : 0 < N := lt_of_le_of_ne hN0 (Ne.symm h0)
    have : N * N ≤ (∑ i, x i ^ 2) * N := by
      calc N * N = N ^ 2 := by ring
        _ ≤ q08c_ch_q C x * q08c_ch_q C y := h1
        _ ≤ (∑ i, x i ^ 2) * N := mul_le_mul h2 h3 h5 (by positivity)
    exact le_of_mul_le_mul_right this hpos


theorem q08c_ch_spectral (A : Matrix (Fin n) (Fin n) ℝ) (hA : ∀ i j, A i j = A j i) :
    ∃ (U : Matrix (Fin n) (Fin n) ℝ) (l : Fin n → ℝ), U * Uᵀ = 1 ∧ Uᵀ * U = 1 ∧
      ∀ i j, A i j = ∑ m, l m * (U i m * U j m) := by
  have hH : A.IsHermitian := by
    ext i j; simp [hA i j]
  set U := hH.eigenvectorUnitary with hU
  have hst : star (U : Matrix (Fin n) (Fin n) ℝ) = (U : Matrix (Fin n) (Fin n) ℝ)ᵀ := by
    rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
  refine ⟨(U : Matrix (Fin n) (Fin n) ℝ), hH.eigenvalues, ?_, ?_, ?_⟩
  · rw [← hst]; exact Unitary.coe_mul_star_self U
  · rw [← hst]; exact Unitary.coe_star_mul_self U
  · intro i j
    have h := congrFun (congrFun hH.spectral_theorem i) j
    rw [Unitary.conjStarAlgAut_apply] at h
    rw [← hU] at h
    rw [h, Matrix.mul_apply]
    simp only [Matrix.mul_diagonal, Function.comp, RCLike.ofReal_real_eq_id, id, Matrix.star_apply, star_trivial]
    refine Finset.sum_congr rfl fun m _ => ?_
    ring


theorem q08c_ch_frob (U : Matrix (Fin n) (Fin n) ℝ) (hUtU : Uᵀ * U = 1) (l : Fin n → ℝ)
    (A : Matrix (Fin n) (Fin n) ℝ) (hAeq : ∀ i j, A i j = ∑ m, l m * (U i m * U j m)) :
    ∑ i, ∑ j, A i j ^ 2 = ∑ m, l m ^ 2 := by
  have hA : A = U * diagonal l * Uᵀ := by
    ext i j
    rw [hAeq, Matrix.mul_apply]
    simp only [Matrix.mul_diagonal, Matrix.transpose_apply]
    exact Finset.sum_congr rfl fun m _ => by ring
  have hAt : Aᵀ = A := by
    ext i j; rw [Matrix.transpose_apply, hAeq, hAeq]; exact Finset.sum_congr rfl fun m _ => by ring
  have h1 : ∑ i, ∑ j, A i j ^ 2 = (Aᵀ * A).trace := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply, sq]
    exact Finset.sum_comm
  rw [h1, hAt]
  have h2 : A * A = U * (diagonal l * diagonal l) * Uᵀ := by
    rw [hA]
    calc U * diagonal l * Uᵀ * (U * diagonal l * Uᵀ)
        = U * diagonal l * (Uᵀ * U) * diagonal l * Uᵀ := by simp only [Matrix.mul_assoc]
      _ = U * (diagonal l * diagonal l) * Uᵀ := by rw [hUtU, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  rw [h2, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hUtU, Matrix.one_mul]
  simp [Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal, sq]


theorem q08c_ch_Bsum (C U : Matrix (Fin n) (Fin n) ℝ) (m m' : Fin n) :
    (Uᵀ * C * U) m m' = ∑ i, ∑ j, U i m * U j m' * C i j := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring

theorem q08c_ch_orth (V : Matrix (Fin n) (Fin n) ℝ) (hVV : V * Vᵀ = 1) (y : Fin n → ℝ) :
    ∑ m, (∑ j, y j * V j m) ^ 2 = ∑ j, y j ^ 2 := by
  have hd : ∀ j j' : Fin n, ∑ m, V j m * V j' m = if j = j' then 1 else 0 := by
    intro j j'
    have := congrFun (congrFun hVV j) j'
    simpa [Matrix.mul_apply, Matrix.one_apply] using this
  calc ∑ m, (∑ j, y j * V j m) ^ 2
      = ∑ m, ∑ j, ∑ j', y j * V j m * (y j' * V j' m) := by
        simp_rw [sq, Finset.sum_mul_sum]
    _ = ∑ j, ∑ j', ∑ m, y j * V j m * (y j' * V j' m) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.sum_comm]
    _ = ∑ j, ∑ j', y j * y j' * (∑ m, V j m * V j' m) := by
        refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun j' _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun m _ => by ring
    _ = ∑ j, y j ^ 2 := by
        simp only [hd, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true, sq]

theorem q08c_ch_alg {C : Matrix (Fin n) (Fin n) ℝ} (hsym : ∀ i j, C i j = C j i)
    (hop : ∀ x : Fin n → ℝ, ∑ j, (∑ i, x i * C i j) ^ 2 ≤ ∑ i, x i ^ 2)
    (U : Matrix (Fin n) (Fin n) ℝ) (hUU : U * Uᵀ = 1) (hUtU : Uᵀ * U = 1) (l : Fin n → ℝ) :
    ∑ m, ∑ m', l m * l m' * (∑ i, ∑ j, U i m * U j m' * C i j) ^ 2 ≤ ∑ m, l m ^ 2 := by
  set B := Uᵀ * C * U with hB
  have hCt : Cᵀ = C := by ext i j; exact hsym j i
  have hBt : Bᵀ = B := by
    rw [hB, Matrix.transpose_mul, Matrix.transpose_mul, hCt, Matrix.transpose_transpose, Matrix.mul_assoc]
  have hBsq : ∀ m, ∑ m', B m m' ^ 2 ≤ 1 := by
    intro m
    have h1 : ∀ m', B m m' = ∑ j, (∑ i, U i m * C i j) * U j m' := by
      intro m'
      rw [hB, q08c_ch_Bsum, Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun i _ => by ring
    have h4 : ∑ i, U i m ^ 2 = 1 := by
      have := congrFun (congrFun hUtU m) m
      simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply_eq] at this
      rw [← this]; exact Finset.sum_congr rfl fun i _ => sq _
    simp_rw [h1]
    rw [q08c_ch_orth U hUU (fun j => ∑ i, U i m * C i j)]
    have := hop (fun i => U i m)
    rw [h4] at this
    exact this
  have hBs : ∀ m m', B m m' = B m' m := by
    intro m m'; exact (congrFun (congrFun hBt m) m').symm
  calc ∑ m, ∑ m', l m * l m' * (∑ i, ∑ j, U i m * U j m' * C i j) ^ 2
      = ∑ m, ∑ m', l m * l m' * B m m' ^ 2 := by
        simp only [hB, q08c_ch_Bsum]
    _ ≤ ∑ m, ∑ m', (l m ^ 2 + l m' ^ 2) / 2 * B m m' ^ 2 := by
        refine Finset.sum_le_sum fun m _ => Finset.sum_le_sum fun m' _ => ?_
        exact mul_le_mul_of_nonneg_right (by nlinarith [sq_nonneg (l m - l m')]) (sq_nonneg _)
    _ = ∑ m, l m ^ 2 * ∑ m', B m m' ^ 2 := by
        have e1 : ∑ m, ∑ m', (l m ^ 2 + l m' ^ 2) / 2 * B m m' ^ 2
            = (∑ m, ∑ m', l m ^ 2 / 2 * B m m' ^ 2) + ∑ m, ∑ m', l m' ^ 2 / 2 * B m m' ^ 2 := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun m _ => ?_
          rw [← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun m' _ => by ring
        have e2 : ∑ m, ∑ m', l m' ^ 2 / 2 * B m m' ^ 2 = ∑ m, ∑ m', l m ^ 2 / 2 * B m m' ^ 2 := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun m' _ => by rw [hBs m' m]
        rw [e1, e2, ← two_mul]
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [Finset.mul_sum, Finset.mul_sum]
        exact Finset.sum_congr rfl fun m' _ => by ring
    _ ≤ ∑ m, l m ^ 2 * 1 := Finset.sum_le_sum fun m _ => mul_le_mul_of_nonneg_left (hBsq m) (sq_nonneg _)
    _ = ∑ m, l m ^ 2 := by simp


theorem q08c_ch_var_bound {C : Matrix (Fin n) (Fin n) ℝ} (hS : C.PosSemidef)
    (hle : ∀ w : Fin n → ℝ, q08c_ch_q C w ≤ ∑ i, w i ^ 2)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : ∀ i j, A i j = A j i) :
    ∫ z, ((1 / 2) * ∑ i, ∑ j, A i j * (z i * z j - C i j)) ^ 2
        ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin n)) C) ≤ (1 / 2) * ∑ i, ∑ j, A i j ^ 2 := by
  set μ := multivariateGaussian (0 : EuclideanSpace ℝ (Fin n)) C with hμ
  have hsym : ∀ i j, C i j = C j i := fun i j => by
    have := hS.isHermitian.apply j i
    simpa using this
  obtain ⟨U, l, hUU, hUtU, hAeq⟩ := q08c_ch_spectral A hA
  set u : Fin n → Fin n → ℝ := fun m i => U i m with hu
  set q : Fin n → ℝ := fun m => q08c_ch_q C (u m) with hq
  set X : Fin n → EuclideanSpace ℝ (Fin n) → ℝ := fun m => q08c_ch_lin (u m) with hX
  set bb : Fin n → Fin n → ℝ := fun m m' => ∑ i, ∑ j, U i m * U j m' * C i j with hbb
  -- Step 1: pointwise spectral form
  have step1 : ∀ z : EuclideanSpace ℝ (Fin n),
      ∑ i, ∑ j, A i j * (z i * z j - C i j) = ∑ m, l m * (X m z ^ 2 - q m) := by
    intro z
    have e1 : ∀ i j, A i j * (z i * z j - C i j) =
        ∑ m, l m * (U i m * U j m) * (z i * z j - C i j) := fun i j => by
      rw [hAeq i j, Finset.sum_mul]
    simp_rw [e1]
    have e2 : ∀ i, ∑ j, ∑ m, l m * (U i m * U j m) * (z i * z j - C i j) =
        ∑ m, ∑ j, l m * (U i m * U j m) * (z i * z j - C i j) := fun i => Finset.sum_comm
    simp_rw [e2]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun m _ => ?_
    simp only [hX, hq, hu, q08c_ch_lin, q08c_ch_q, sq, mul_sub, Finset.sum_sub_distrib]
    congr 1
    · rw [Finset.sum_mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun x1 _ => by ring
    · rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun x1 _ => by ring
  have hX2 : ∀ m, ∫ z, X m z ^ 2 ∂μ = q m := fun m => q08c_ch_second hS (u m)
  have hX2i : ∀ m, Integrable (fun z => X m z ^ 2) μ := fun m => q08c_ch_lin_int hS (u m) 2
  have hpair : ∀ m m', ∫ z, X m z ^ 2 * X m' z ^ 2 ∂μ = q m * q m' + 2 * bb m m' ^ 2 :=
    fun m m' => q08c_ch_pair hS (u m) (u m')
  have hpairi : ∀ m m', Integrable (fun z => X m z ^ 2 * X m' z ^ 2) μ :=
    fun m m' => q08c_ch_pair_int hS (u m) (u m')
  have hexp : ∀ m m' z, (X m z ^ 2 - q m) * (X m' z ^ 2 - q m') =
      X m z ^ 2 * X m' z ^ 2 - q m' * X m z ^ 2 - q m * X m' z ^ 2 + q m * q m' := fun m m' z => by ring
  have hint : ∀ m m', Integrable (fun z => (X m z ^ 2 - q m) * (X m' z ^ 2 - q m')) μ := by
    intro m m'
    have h1 : Integrable (fun z => X m z ^ 2 * X m' z ^ 2 - q m' * X m z ^ 2) μ :=
      (hpairi m m').sub ((hX2i m).const_mul _)
    have h2 : Integrable (fun z => X m z ^ 2 * X m' z ^ 2 - q m' * X m z ^ 2 - q m * X m' z ^ 2) μ :=
      h1.sub ((hX2i m').const_mul _)
    have h3 := h2.add (integrable_const (q m * q m'))
    refine h3.congr (Filter.Eventually.of_forall fun z => ?_)
    simp only [Pi.add_apply, hexp]
  have hcov : ∀ m m', ∫ z, (X m z ^ 2 - q m) * (X m' z ^ 2 - q m') ∂μ = 2 * bb m m' ^ 2 := by
    intro m m'
    have h1 : Integrable (fun z => X m z ^ 2 * X m' z ^ 2 - q m' * X m z ^ 2) μ :=
      (hpairi m m').sub ((hX2i m).const_mul _)
    have h2 : Integrable (fun z => X m z ^ 2 * X m' z ^ 2 - q m' * X m z ^ 2 - q m * X m' z ^ 2) μ :=
      h1.sub ((hX2i m').const_mul _)
    simp_rw [hexp]
    rw [integral_add h2 (integrable_const _), integral_sub h1 ((hX2i m').const_mul _),
      integral_sub (hpairi m m') ((hX2i m).const_mul _), integral_const_mul, integral_const_mul,
      hpair, hX2, hX2]
    simp
    ring
  have hsq : ∀ z : EuclideanSpace ℝ (Fin n),
      ((1 / 2) * ∑ i, ∑ j, A i j * (z i * z j - C i j)) ^ 2 =
        (1 / 4) * ∑ m, ∑ m', l m * l m' * ((X m z ^ 2 - q m) * (X m' z ^ 2 - q m')) := by
    intro z
    rw [step1 z, mul_pow, sq (∑ m, l m * (X m z ^ 2 - q m)), Finset.sum_mul_sum]
    norm_num
    refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun m' _ => by ring
  have hmain : ∫ z, ((1 / 2) * ∑ i, ∑ j, A i j * (z i * z j - C i j)) ^ 2 ∂μ =
      (1 / 2) * ∑ m, ∑ m', l m * l m' * bb m m' ^ 2 := by
    simp_rw [hsq]
    rw [integral_const_mul, integral_finsetSum _ (fun m _ => integrable_finsetSum _ fun m' _ =>
      (hint m m').const_mul _)]
    simp_rw [integral_finsetSum _ (fun m' _ => (hint _ m').const_mul _), integral_const_mul, hcov]
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun m' _ => by ring
  rw [hmain, q08c_ch_frob U hUtU l A hAeq]
  have := q08c_ch_alg hsym (q08c_ch_opnorm hS hle) U hUU hUtU l
  linarith

/-- Finite sections of a covariance matrix `C` on `ℕ`: positive semidefinite and `≤ I`. -/
theorem q08c_ch_cov_fin (C : ℕ → ℕ → ℝ) (hsymm : ∀ i j, C i j = C j i)
    (hpsd : ∀ (n : ℕ) (v : ℕ → ℝ), 0 ≤ ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, v i * v j * C i j)
    (hle : ∀ (n : ℕ) (v : ℕ → ℝ), ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, v i * v j * C i j ≤
      ∑ i ∈ Finset.range n, v i ^ 2) (n : ℕ) :
    (Matrix.of fun i j : Fin n => C i j).PosSemidef ∧
      ∀ w : Fin n → ℝ, q08c_ch_q (Matrix.of fun i j : Fin n => C i j) w ≤ ∑ i, w i ^ 2 := by
  have key : ∀ w : Fin n → ℝ, ∃ v : ℕ → ℝ,
      ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, v i * v j * C i j =
        q08c_ch_q (Matrix.of fun i j : Fin n => C i j) w ∧
      ∑ i ∈ Finset.range n, v i ^ 2 = ∑ i, w i ^ 2 := by
    intro w
    refine ⟨fun i => if h : i < n then w ⟨i, h⟩ else 0, ?_, ?_⟩
    · rw [Finset.sum_range]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_range]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp [q08c_ch_q, i.2, j.2]
    · rw [Finset.sum_range]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp [i.2]
  refine ⟨?_, fun w => ?_⟩
  · rw [Matrix.posSemidef_iff_dotProduct_mulVec]
    refine ⟨?_, fun x => ?_⟩
    · ext i j; simp [hsymm i j]
    · obtain ⟨v, hv, -⟩ := key x
      have := hpsd n v
      rw [hv, q08c_ch_q_eq] at this
      simpa using this
  · obtain ⟨v, hv, hv2⟩ := key w
    rw [← hv, ← hv2]; exact hle n v

/-- Second-moment bound for a measurable family with Gaussian finite-dimensional law. -/
theorem q08c_ch_bound_raw {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (G : ℕ → Ω → ℝ) (hG : ∀ i, Measurable (G i)) (C : ℕ → ℕ → ℝ) (hsymm : ∀ i j, C i j = C j i)
    (hpsd : ∀ (n : ℕ) (v : ℕ → ℝ), 0 ≤ ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, v i * v j * C i j)
    (hle : ∀ (n : ℕ) (v : ℕ → ℝ), ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, v i * v j * C i j ≤
      ∑ i ∈ Finset.range n, v i ^ 2) (n : ℕ)
    (hlaw : P.map (fun ω => (WithLp.toLp 2 fun i : Fin n => G i ω : EuclideanSpace ℝ (Fin n))) =
      multivariateGaussian 0 (Matrix.of fun i j : Fin n => C i j))
    (A : Fin n → Fin n → ℝ) (hA : ∀ i j, A i j = A j i) :
    ∫ ω, ((1 / 2) * ∑ i : Fin n, ∑ j : Fin n, A i j * (G i ω * G j ω - C i j)) ^ 2 ∂P ≤
      (1 / 2) * ∑ i : Fin n, ∑ j : Fin n, A i j ^ 2 := by
  obtain ⟨hS, hle'⟩ := q08c_ch_cov_fin C hsymm hpsd hle n
  set X : Ω → EuclideanSpace ℝ (Fin n) := fun ω => WithLp.toLp 2 fun i : Fin n => G i ω with hXdef
  have hX : AEMeasurable X P := by
    have : Measurable X := by
      rw [hXdef]; fun_prop
    exact this.aemeasurable
  have hmeas : Measurable (fun z : EuclideanSpace ℝ (Fin n) =>
      ((1 / 2) * ∑ i : Fin n, ∑ j : Fin n, A i j * (z i * z j - C i j)) ^ 2) := by fun_prop
  have h1 := integral_map (μ := P) hX hmeas.aestronglyMeasurable
  rw [hlaw] at h1
  have h2 := q08c_ch_var_bound hS hle' (Matrix.of A) hA
  simp only [Matrix.of_apply] at h2
  rw [h1] at h2
  exact h2

end HRS.Q08
