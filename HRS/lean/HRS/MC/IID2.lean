import HRS.MC.S7ChaosIIDVocab
import HRS.Prob.Gaussian

/-!
# iid bridge, packet iid2, part A: `B ↦ SᵀBS` for a contraction `S`

Matrix algebra, no probability.  `S : ℕ → ℕ → ℝ` satisfies the contraction hypothesis `hbound`
(`‖Sᵀx‖ ≤ ‖x‖` on finitely supported `x`).  For a symmetric Hilbert-Schmidt `B`:

* `conj_summable`: for every `k l`, the family `(i,j) ↦ S i k * B i j * S j l` is summable on `ℕ × ℕ`;
  consequently every inner family `j ↦ S i k * B i j * S j l` and the outer family
  `i ↦ ∑' j, S i k * B i j * S j l` is summable, and `s7_conjCoeff S B k l` is the `tsum` over `ℕ × ℕ`
  (`conj_eq_tsum_prod`);
* `conj_isSymmetricHS`: `s7_conjCoeff S B` is symmetric Hilbert-Schmidt with `hsNorm ≤ hsNorm B`;
* `conj_sub`: linearity (difference);
* `trunc`: `isSymmetricHS_trunc`, `hsNorm_tail_tendsto`, `conj_trunc`, `hsNorm_conj_tail_tendsto`.
-/

open Filter Topology Finset

noncomputable section

namespace HRS.MC.IID

open HRS

/-- Contraction bound `‖Sᵀx‖ ≤ ‖x‖` for finitely supported `x`. -/
def ContrBound (S : ℕ → ℕ → ℝ) : Prop :=
  ∀ (L : ℕ) (x : ℕ → ℝ), Summable (fun k => (∑ i ∈ range L, x i * S i k) ^ 2) ∧
    ∑' k, (∑ i ∈ range L, x i * S i k) ^ 2 ≤ ∑ i ∈ range L, x i ^ 2

/-- Truncation of a matrix to the corner `[0,L) × [0,L)`. -/
def trunc (L : ℕ) (B : ℕ → ℕ → ℝ) : ℕ → ℕ → ℝ := fun i j => if i < L ∧ j < L then B i j else 0

section Algebra

variable {S : ℕ → ℕ → ℝ}

theorem col_sq_sum_le (hbound : ContrBound S) (l L : ℕ) :
    ∑ i ∈ range L, S i l ^ 2 ≤ 1 := by
  obtain ⟨hs, hle⟩ := hbound L (fun i => S i l)
  have h1 : (∑ i ∈ range L, S i l * S i l) ^ 2 ≤ ∑' k, (∑ i ∈ range L, S i l * S i k) ^ 2 :=
    hs.le_tsum l (fun j _ => sq_nonneg _)
  have h2 : ∑ i ∈ range L, S i l * S i l = ∑ i ∈ range L, S i l ^ 2 :=
    sum_congr rfl fun i _ => (sq _).symm
  rw [h2] at h1
  have h3 : ∑ i ∈ range L, S i l ^ 2 ^ 1 = ∑ i ∈ range L, S i l ^ 2 := by simp
  set a := ∑ i ∈ range L, S i l ^ 2 with ha
  have ha0 : 0 ≤ a := sum_nonneg fun i _ => sq_nonneg _
  have : a ^ 2 ≤ a := h1.trans hle
  by_contra hcon
  have hcon := not_le.1 hcon
  nlinarith

theorem col_sq_summable (hbound : ContrBound S) (l : ℕ) : Summable fun i => S i l ^ 2 :=
  summable_of_sum_range_le (fun _ => sq_nonneg _) (col_sq_sum_le hbound l)

theorem tendsto_range_prod : Tendsto (fun L : ℕ => range L ×ˢ range L) atTop atTop := by
  refine tendsto_atTop_atTop.2 fun s => ?_
  obtain ⟨n, hn⟩ := Finset.exists_nat_subset_range (s.image Prod.fst ∪ s.image Prod.snd)
  refine ⟨n, fun L hL p hp => ?_⟩
  have h1 : p.1 ∈ range n := hn (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hp))
  have h2 : p.2 ∈ range n := hn (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hp))
  simp only [mem_product, mem_range] at h1 h2 ⊢
  exact ⟨h1.trans_le hL, h2.trans_le hL⟩

theorem tendsto_sum_range_prod {f : ℕ × ℕ → ℝ} (hf : Summable f) :
    Tendsto (fun L => ∑ i ∈ range L, ∑ j ∈ range L, f (i, j)) atTop (𝓝 (∑' p, f p)) := by
  have h := hf.hasSum.comp tendsto_range_prod
  refine h.congr fun L => ?_
  simp [Function.comp, Finset.sum_product]

/-- Summability of the joint family. -/
theorem summable_conj_prod {B : ℕ → ℕ → ℝ} (hB : Summable fun p : ℕ × ℕ => B p.1 p.2 ^ 2)
    {u v : ℕ → ℝ} (hu : Summable fun i => u i ^ 2) (hv : Summable fun i => v i ^ 2) :
    Summable fun p : ℕ × ℕ => u p.1 * B p.1 p.2 * v p.2 := by
  have h1 : Summable fun p : ℕ × ℕ => (u p.1 * v p.2) ^ 2 := by
    have := Summable.mul_of_nonneg hu hv (fun _ => sq_nonneg _) (fun _ => sq_nonneg _)
    refine this.congr fun p => ?_
    simp [mul_pow]
  refine Summable.of_norm_bounded ((h1.add hB).mul_left (1 / 2)) fun p => ?_
  rw [Real.norm_eq_abs]
  have : u p.1 * B p.1 p.2 * v p.2 = (u p.1 * v p.2) * B p.1 p.2 := by ring
  rw [this]
  nlinarith [sq_nonneg (|u p.1 * v p.2| - |B p.1 p.2|), abs_mul_abs_self (u p.1 * v p.2),
    abs_mul_abs_self (B p.1 p.2), abs_mul (u p.1 * v p.2) (B p.1 p.2)]

variable {B : ℕ → ℕ → ℝ}

/-- The joint family `(i,j) ↦ S i k * B i j * S j l` of the conjugation. -/
theorem conj_summable (hbound : ContrBound S) (hB : IsSymmetricHS B) (k l : ℕ) :
    Summable fun p : ℕ × ℕ => S p.1 k * B p.1 p.2 * S p.2 l :=
  summable_conj_prod hB.2 (col_sq_summable hbound k) (col_sq_summable hbound l)

/-- Inner summability: for every `i`, `j ↦ S i k * B i j * S j l` is summable. -/
theorem conj_summable_inner (hbound : ContrBound S) (hB : IsSymmetricHS B) (k l i : ℕ) :
    Summable fun j => S i k * B i j * S j l :=
  (conj_summable hbound hB k l).prod_factor i

/-- Outer summability: `i ↦ ∑' j, S i k * B i j * S j l` is summable. -/
theorem conj_summable_outer (hbound : ContrBound S) (hB : IsSymmetricHS B) (k l : ℕ) :
    Summable fun i => ∑' j, S i k * B i j * S j l :=
  (conj_summable hbound hB k l).prod

/-- `s7_conjCoeff` is the `tsum` over `ℕ × ℕ` of the (summable) joint family. -/
theorem conj_eq_tsum_prod (hbound : ContrBound S) (hB : IsSymmetricHS B) (k l : ℕ) :
    s7_conjCoeff S B k l = ∑' p : ℕ × ℕ, S p.1 k * B p.1 p.2 * S p.2 l :=
  ((conj_summable hbound hB k l).tsum_prod).symm

theorem conj_symm (hbound : ContrBound S) (hB : IsSymmetricHS B) (k l : ℕ) :
    s7_conjCoeff S B k l = s7_conjCoeff S B l k := by
  rw [conj_eq_tsum_prod hbound hB, conj_eq_tsum_prod hbound hB,
    ← (Equiv.prodComm ℕ ℕ).tsum_eq]
  refine tsum_congr fun p => ?_
  simp only [Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap]
  rw [hB.1 p.2 p.1]
  ring

/-! ### Finite sections and the Hilbert-Schmidt bound -/

/-- The finite section `∑_{i,j<L} S_ik B_ij S_jl`. -/
def convSec (S B : ℕ → ℕ → ℝ) (L k l : ℕ) : ℝ :=
  ∑ i ∈ range L, ∑ j ∈ range L, S i k * B i j * S j l

theorem convSec_hs_bound (hbound : ContrBound S) (L N : ℕ) :
    ∑ k ∈ range N, ∑ l ∈ range N, convSec S B L k l ^ 2 ≤
      ∑ i ∈ range L, ∑ j ∈ range L, B i j ^ 2 := by
  -- step 1: fixed `l`, bound the sum over `k`
  have step1 : ∀ l, ∑ k ∈ range N, convSec S B L k l ^ 2 ≤
      ∑ i ∈ range L, (∑ j ∈ range L, B i j * S j l) ^ 2 := by
    intro l
    obtain ⟨hs, hle⟩ := hbound L (fun i => ∑ j ∈ range L, B i j * S j l)
    refine le_trans ?_ (le_trans (hs.sum_le_tsum (range N) (fun _ _ => sq_nonneg _)) hle)
    refine le_of_eq (sum_congr rfl fun k _ => ?_)
    unfold convSec
    congr 1
    refine sum_congr rfl fun i _ => ?_
    rw [mul_comm, Finset.mul_sum]
    exact sum_congr rfl fun j _ => by ring
  -- step 2: swap and bound the sum over `l` for each `i`
  have step2 : ∀ i, ∑ l ∈ range N, (∑ j ∈ range L, B i j * S j l) ^ 2 ≤
      ∑ j ∈ range L, B i j ^ 2 := by
    intro i
    obtain ⟨hs, hle⟩ := hbound L (fun j => B i j)
    exact le_trans (hs.sum_le_tsum (range N) (fun _ _ => sq_nonneg _)) hle
  calc ∑ k ∈ range N, ∑ l ∈ range N, convSec S B L k l ^ 2
      = ∑ l ∈ range N, ∑ k ∈ range N, convSec S B L k l ^ 2 := Finset.sum_comm
    _ ≤ ∑ l ∈ range N, ∑ i ∈ range L, (∑ j ∈ range L, B i j * S j l) ^ 2 :=
        sum_le_sum fun l _ => step1 l
    _ = ∑ i ∈ range L, ∑ l ∈ range N, (∑ j ∈ range L, B i j * S j l) ^ 2 := Finset.sum_comm
    _ ≤ ∑ i ∈ range L, ∑ j ∈ range L, B i j ^ 2 := sum_le_sum fun i _ => step2 i

theorem convSec_tendsto (hbound : ContrBound S) (hB : IsSymmetricHS B) (k l : ℕ) :
    Tendsto (fun L => convSec S B L k l) atTop (𝓝 (s7_conjCoeff S B k l)) := by
  rw [conj_eq_tsum_prod hbound hB]
  exact tendsto_sum_range_prod (conj_summable hbound hB k l)

theorem sum_range_prod_le_tsum {f : ℕ × ℕ → ℝ} (hf : Summable f) (h0 : ∀ p, 0 ≤ f p) (L : ℕ) :
    ∑ i ∈ range L, ∑ j ∈ range L, f (i, j) ≤ ∑' p, f p := by
  rw [← Finset.sum_product']
  exact hf.sum_le_tsum _ (fun p _ => h0 p)

/-- `SᵀBS` is symmetric Hilbert-Schmidt with `‖SᵀBS‖_HS ≤ ‖B‖_HS` (the squared form). -/
theorem conj_hs_sq (hbound : ContrBound S) (hB : IsSymmetricHS B) :
    Summable (fun p : ℕ × ℕ => s7_conjCoeff S B p.1 p.2 ^ 2) ∧
      ∑' p : ℕ × ℕ, s7_conjCoeff S B p.1 p.2 ^ 2 ≤ ∑' p : ℕ × ℕ, B p.1 p.2 ^ 2 := by
  have hbd : ∀ N : ℕ, ∑ k ∈ range N, ∑ l ∈ range N, s7_conjCoeff S B k l ^ 2 ≤
      ∑' p : ℕ × ℕ, B p.1 p.2 ^ 2 := by
    intro N
    have hlim : Tendsto (fun L => ∑ k ∈ range N, ∑ l ∈ range N, convSec S B L k l ^ 2) atTop
        (𝓝 (∑ k ∈ range N, ∑ l ∈ range N, s7_conjCoeff S B k l ^ 2)) := by
      refine tendsto_finsetSum _ fun k _ => tendsto_finsetSum _ fun l _ => ?_
      exact (convSec_tendsto hbound hB k l).pow 2
    refine le_of_tendsto hlim (Eventually.of_forall fun L => ?_)
    exact (convSec_hs_bound hbound L N).trans
      (sum_range_prod_le_tsum (f := fun p : ℕ × ℕ => B p.1 p.2 ^ 2) hB.2 (fun _ => sq_nonneg _) L)
  have hsum : Summable (fun p : ℕ × ℕ => s7_conjCoeff S B p.1 p.2 ^ 2) := by
    refine summable_of_sum_le (c := ∑' p : ℕ × ℕ, B p.1 p.2 ^ 2) (fun _ => sq_nonneg _) fun u => ?_
    obtain ⟨N, hN⟩ := (tendsto_range_prod.eventually (eventually_ge_atTop u)).exists
    calc ∑ p ∈ u, s7_conjCoeff S B p.1 p.2 ^ 2
        ≤ ∑ p ∈ range N ×ˢ range N, s7_conjCoeff S B p.1 p.2 ^ 2 :=
          sum_le_sum_of_subset_of_nonneg hN (fun _ _ _ => sq_nonneg _)
      _ = ∑ k ∈ range N, ∑ l ∈ range N, s7_conjCoeff S B k l ^ 2 := Finset.sum_product ..
      _ ≤ _ := hbd N
  refine ⟨hsum, ?_⟩
  have := (tendsto_sum_range_prod hsum)
  refine le_of_tendsto this (Eventually.of_forall fun L => ?_)
  exact (hbd L)

theorem conj_isSymmetricHS (hbound : ContrBound S) (hB : IsSymmetricHS B) :
    IsSymmetricHS (s7_conjCoeff S B) ∧ hsNorm (s7_conjCoeff S B) ≤ hsNorm B :=
  ⟨⟨conj_symm hbound hB, (conj_hs_sq hbound hB).1⟩,
    Real.sqrt_le_sqrt (conj_hs_sq hbound hB).2⟩

/-! ### Linearity -/

theorem isSymmetricHS_sub {B1 B2 : ℕ → ℕ → ℝ} (h1 : IsSymmetricHS B1) (h2 : IsSymmetricHS B2) :
    IsSymmetricHS (B1 - B2) := by
  refine ⟨fun i j => ?_, ?_⟩
  · simp only [Pi.sub_apply, h1.1 i j, h2.1 i j]
  · refine Summable.of_nonneg_of_le (fun _ => sq_nonneg _) (fun p => ?_)
      (((h1.2.add h2.2).mul_left 2))
    simp only [Pi.sub_apply]
    nlinarith [sq_nonneg (B1 p.1 p.2 + B2 p.1 p.2)]

/-- Linearity of `B ↦ SᵀBS` (difference). -/
theorem conj_sub (hbound : ContrBound S) {B1 B2 : ℕ → ℕ → ℝ} (h1 : IsSymmetricHS B1)
    (h2 : IsSymmetricHS B2) :
    s7_conjCoeff S (B1 - B2) = fun k l => s7_conjCoeff S B1 k l - s7_conjCoeff S B2 k l := by
  funext k l
  rw [conj_eq_tsum_prod hbound (isSymmetricHS_sub h1 h2), conj_eq_tsum_prod hbound h1,
    conj_eq_tsum_prod hbound h2, ← Summable.tsum_sub (conj_summable hbound h1 k l)
      (conj_summable hbound h2 k l)]
  refine tsum_congr fun p => ?_
  simp only [Pi.sub_apply]
  ring

/-! ### Truncations -/

theorem isSymmetricHS_trunc (L : ℕ) (hB : IsSymmetricHS B) : IsSymmetricHS (trunc L B) := by
  refine ⟨fun i j => ?_, ?_⟩
  · unfold trunc
    rw [hB.1 i j]
    by_cases h : i < L ∧ j < L
    · rw [if_pos h, if_pos ⟨h.2, h.1⟩]
    · rw [if_neg h, if_neg (fun h' => h ⟨h'.2, h'.1⟩)]
  · refine Summable.of_nonneg_of_le (fun _ => sq_nonneg _) (fun p => ?_) hB.2
    unfold trunc
    split_ifs
    · exact le_rfl
    · simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
      exact sq_nonneg _

theorem tail_sq (L : ℕ) (hB : IsSymmetricHS B) :
    ∑' p : ℕ × ℕ, (B p.1 p.2 - trunc L B p.1 p.2) ^ 2 =
      ∑' p : ℕ × ℕ, B p.1 p.2 ^ 2 - ∑ p ∈ range L ×ˢ range L, B p.1 p.2 ^ 2 := by
  have h1 : ∀ p : ℕ × ℕ, (B p.1 p.2 - trunc L B p.1 p.2) ^ 2 =
      B p.1 p.2 ^ 2 - if p ∈ range L ×ˢ range L then B p.1 p.2 ^ 2 else 0 := by
    intro p
    unfold trunc
    by_cases h : p.1 < L ∧ p.2 < L
    · have : p ∈ range L ×ˢ range L := by simp [h.1, h.2]
      simp [h, this]
    · have : p ∉ range L ×ˢ range L := by simpa using h
      simp [h, this]
  have hs : Summable fun p : ℕ × ℕ => if p ∈ range L ×ˢ range L then B p.1 p.2 ^ 2 else 0 :=
    summable_of_ne_finset_zero (s := range L ×ˢ range L) (fun p hp => by simp [hp])
  have hF : ∑' p : ℕ × ℕ, (if p ∈ range L ×ˢ range L then B p.1 p.2 ^ 2 else 0) =
      ∑ p ∈ range L ×ˢ range L, B p.1 p.2 ^ 2 := by
    rw [tsum_eq_sum (s := range L ×ˢ range L) (fun p hp => if_neg hp), Finset.sum_ite_mem,
      Finset.inter_self]
  rw [tsum_congr h1, Summable.tsum_sub hB.2 hs, hF]

theorem isSymmetricHS_tail (L : ℕ) (hB : IsSymmetricHS B) :
    IsSymmetricHS (fun i j => B i j - trunc L B i j) := by
  have := isSymmetricHS_sub hB (isSymmetricHS_trunc L hB)
  exact this

/-- `‖B - B_L‖_HS → 0`. -/
theorem hsNorm_tail_tendsto (hB : IsSymmetricHS B) :
    Tendsto (fun L => hsNorm (fun i j => B i j - trunc L B i j)) atTop (𝓝 0) := by
  have h := hB.2.hasSum.comp tendsto_range_prod
  have h2 : Tendsto (fun L : ℕ => ∑' p : ℕ × ℕ, B p.1 p.2 ^ 2 -
      ∑ p ∈ range L ×ˢ range L, B p.1 p.2 ^ 2) atTop (𝓝 0) := by
    have := (tendsto_const_nhds (x := ∑' p : ℕ × ℕ, B p.1 p.2 ^ 2)).sub h
    rwa [sub_self] at this
  have h3 := (Real.continuous_sqrt.tendsto 0).comp h2
  simp only [Real.sqrt_zero] at h3
  refine h3.congr fun L => ?_
  simp only [Function.comp, hsNorm]
  rw [tail_sq L hB]

/-- `SᵀB_LS` is the finite sum. -/
theorem conj_trunc (L k l : ℕ) :
    s7_conjCoeff S (trunc L B) k l = ∑ i ∈ range L, ∑ j ∈ range L, S i k * B i j * S j l := by
  unfold s7_conjCoeff trunc
  have h1 : ∀ i, ∑' j, S i k * (if i < L ∧ j < L then B i j else 0) * S j l =
      if i < L then ∑ j ∈ range L, S i k * B i j * S j l else 0 := by
    intro i
    by_cases hi : i < L
    · rw [if_pos hi, tsum_eq_sum (s := range L)]
      · refine sum_congr rfl fun j hj => ?_
        rw [if_pos ⟨hi, by simpa using hj⟩]
      · intro j hj
        have : ¬ (i < L ∧ j < L) := fun h => hj (by simpa using h.2)
        simp [this]
    · rw [if_neg hi]
      simp [hi]
  rw [tsum_congr h1, tsum_eq_sum (s := range L)]
  · exact sum_congr rfl fun i hi => if_pos (by simpa using hi)
  · intro i hi
    have : ¬ i < L := fun h => hi (by simpa using h)
    simp [this]

/-- `‖SᵀBS - SᵀB_LS‖_HS → 0`. -/
theorem hsNorm_conj_tail_tendsto (hbound : ContrBound S) (hB : IsSymmetricHS B) :
    Tendsto (fun L => hsNorm (fun k l => s7_conjCoeff S B k l - s7_conjCoeff S (trunc L B) k l))
      atTop (𝓝 0) := by
  refine squeeze_zero (fun L => Real.sqrt_nonneg _) (fun L => ?_) (hsNorm_tail_tendsto hB)
  have hsub := conj_sub hbound hB (isSymmetricHS_trunc L hB)
  have : (fun k l => s7_conjCoeff S B k l - s7_conjCoeff S (trunc L B) k l) =
      s7_conjCoeff S (B - trunc L B) := hsub.symm
  rw [this]
  exact (conj_isSymmetricHS hbound (isSymmetricHS_sub hB (isSymmetricHS_trunc L hB))).2

end Algebra

end HRS.MC.IID
