import HRS.Uniform.Q45Pair

/-!
# Q45: block transforms of a vector martingale (definitions and cell identities)

For a vector martingale `N` in `ℝ^q`, blocks `[r_k, r_{k+1}]` (`r_k = kT/Nb`) and matrices `A_k : ℝ^q → ℝ^m`, the process
`𝒮_s = ∑_k A_k (N_{s ∧ r_{k+1}} - N_{s ∧ r_k})` (the stochastic integral of a block-constant integrand).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators Matrix

namespace HRS.Uniform.Q45

open HRS HRS.LindebergAux

variable {m q : ℕ}

local notation "ℝ^" p => EuclideanSpace ℝ (Fin p)

/-- The linear map `v ↦ B v` between Euclidean spaces. -/
def actCLM (B : Matrix (Fin m) (Fin q) ℝ) : (ℝ^q) →L[ℝ] (ℝ^m) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => WithLp.toLp 2 (B.mulVec v.ofLp)
      map_add' := fun v w => by simp [Matrix.mulVec_add]
      map_smul' := fun c v => by simp [Matrix.mulVec_smul] }

lemma actCLM_apply (B : Matrix (Fin m) (Fin q) ℝ) (v : ℝ^q) (a : Fin m) :
    actCLM B v a = ∑ c, B a c * v c := by
  simp [actCLM, Matrix.mulVec, dotProduct]

lemma norm_actCLM_le (B : Matrix (Fin m) (Fin q) ℝ) {c : ℝ} (hc : 0 ≤ c)
    (hB : ∀ u : Fin q → ℝ, (B.mulVec u) ⬝ᵥ (B.mulVec u) ≤ c ^ 2 * (u ⬝ᵥ u)) (v : ℝ^q) :
    ‖actCLM B v‖ ≤ c * ‖v‖ := by
  have h1 : ‖actCLM B v‖ ^ 2 = (B.mulVec v.ofLp) ⬝ᵥ (B.mulVec v.ofLp) := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => by positivity)]
    simp [actCLM, dotProduct, sq]
  have h2 : ‖v‖ ^ 2 = v.ofLp ⬝ᵥ v.ofLp := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => by positivity)]
    simp [dotProduct, sq]
  have := hB v.ofLp
  rw [← h1, ← h2] at this
  exact le_of_sq_le_sq (by nlinarith [this]) (by positivity)

/-- The block time `r_k = kT/Nb`. -/
abbrev rr (Nb : ℕ) (T : ℝ) (k : ℕ) : ℝ := unifPart T Nb k

lemma rr_mono {Nb : ℕ} {T : ℝ} (hT : 0 ≤ T) (hNb : 1 ≤ Nb) : Monotone (rr Nb T) :=
  unifPart_mono hT Nb

lemma rr_nonneg {Nb : ℕ} {T : ℝ} (hT : 0 ≤ T) (k : ℕ) : 0 ≤ rr Nb T k := unifPart_nonneg hT Nb k

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- The block transform `𝒮_s = ∑_{k<Nb} A_k (N_{s ∧ r_{k+1}} - N_{s ∧ r_k})`. -/
def blockProc (A : ℕ → Matrix (Fin m) (Fin q) ℝ) (Nb : ℕ) (T : ℝ) (N : ℝ → Ω → ℝ^q) (s : ℝ)
    (ω : Ω) : ℝ^m :=
  ∑ k ∈ Finset.range Nb, actCLM (A k) (N (min s (rr Nb T (k + 1))) ω - N (min s (rr Nb T k)) ω)

/-- The block index of a time `σ`. -/
def blk (Nb : ℕ) (T : ℝ) (σ : ℝ) : ℕ := min ⌊σ * Nb / T⌋₊ (Nb - 1)

/-- The covariance density of the block transform: `A_{k(σ)} S A_{k(σ)}ᵀ`. -/
def blockCov (A : ℕ → Matrix (Fin m) (Fin q) ℝ) (Nb : ℕ) (T : ℝ) (S : Matrix (Fin q) (Fin q) ℝ)
    (σ : ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  A (blk Nb T σ) * S * (A (blk Nb T σ))ᵀ

lemma blockProc_zero {A : ℕ → Matrix (Fin m) (Fin q) ℝ} {Nb : ℕ} {T : ℝ} (hT : 0 ≤ T)
    (N : ℝ → Ω → ℝ^q) (ω : Ω) : blockProc A Nb T N 0 ω = 0 := by
  unfold blockProc
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [min_eq_left (rr_nonneg hT _), min_eq_left (rr_nonneg hT _), sub_self, map_zero]

/-- On a cell inside block `k` the increment of `𝒮` is `A_k` times the increment of `N`. -/
lemma blockProc_cell {A : ℕ → Matrix (Fin m) (Fin q) ℝ} {Nb : ℕ} {T : ℝ} (hT : 0 ≤ T) (hNb : 1 ≤ Nb)
    (N : ℝ → Ω → ℝ^q) {k : ℕ} (hk : k < Nb) {τ τ' : ℝ} (h1 : rr Nb T k ≤ τ) (h2 : τ ≤ τ')
    (h3 : τ' ≤ rr Nb T (k + 1)) (ω : Ω) :
    blockProc A Nb T N τ' ω - blockProc A Nb T N τ ω = actCLM (A k) (N τ' ω - N τ ω) := by
  have hmono := rr_mono hT hNb
  unfold blockProc
  rw [← Finset.sum_sub_distrib]
  rw [Finset.sum_eq_single k]
  · rw [min_eq_left h3, min_eq_left (h2.trans h3), min_eq_right (h1.trans h2), min_eq_right h1,
      ← map_sub]
    congr 1
    abel
  · intro j hj hjk
    rcases lt_or_gt_of_ne hjk with hlt | hgt
    · have a1 : rr Nb T (j + 1) ≤ τ := (hmono (Nat.succ_le_of_lt hlt)).trans h1
      have a2 : rr Nb T j ≤ τ := (hmono (Nat.le_succ j)).trans a1
      rw [min_eq_right (a1.trans h2), min_eq_right (a2.trans h2), min_eq_right a1, min_eq_right a2,
        sub_self]
    · have a1 : τ' ≤ rr Nb T j := h3.trans (hmono (Nat.succ_le_of_lt hgt))
      have a2 : τ' ≤ rr Nb T (j + 1) := a1.trans (hmono (Nat.le_succ j))
      rw [min_eq_left a1, min_eq_left a2, min_eq_left (h2.trans a1), min_eq_left (h2.trans a2)]
      simp
  · intro hk'
    exact absurd (Finset.mem_range.2 hk) hk'

lemma blk_eq {Nb : ℕ} {T : ℝ} (hT : 0 < T) (hNb : 1 ≤ Nb) {k : ℕ} (hk : k < Nb) {σ : ℝ}
    (h1 : rr Nb T k ≤ σ) (h2 : σ < rr Nb T (k + 1)) : blk Nb T σ = k := by
  have hN : (0 : ℝ) < Nb := by exact_mod_cast hNb
  have e1 : (k : ℝ) ≤ σ * Nb / T := by
    rw [le_div_iff₀ hT]
    have : (k : ℝ) * T / Nb ≤ σ := h1
    rw [div_le_iff₀ hN] at this
    linarith
  have e2 : σ * Nb / T < k + 1 := by
    rw [div_lt_iff₀ hT]
    have : σ < ((k + 1 : ℕ) : ℝ) * T / Nb := h2
    rw [lt_div_iff₀ hN] at this
    push_cast at this
    linarith
  have hfl : ⌊σ * Nb / T⌋₊ = k := by
    rw [Nat.floor_eq_iff ((Nat.cast_nonneg k).trans e1)]
    exact ⟨e1, e2⟩
  unfold blk
  rw [hfl]
  exact min_eq_left (Nat.le_sub_one_of_lt hk)

lemma measurable_blk (Nb : ℕ) (T : ℝ) : Measurable (blk Nb T) := by
  unfold blk
  exact (Nat.measurable_floor.comp ((measurable_id.mul_const _).div_const _)).min measurable_const

lemma abs_entry_le_s1 (Q : Matrix (Fin m) (Fin m) ℝ) (a b : Fin m) : |Q a b| ≤ s1Norm Q := by
  classical
  have h := trace_dual (Matrix.of fun i j => if i = a ∧ j = b then (1 : ℝ) else 0) Q 1 zero_le_one
    (fun u v => by
      have e : u ⬝ᵥ ((Matrix.of fun i j => if i = a ∧ j = b then (1 : ℝ) else 0).mulVec v) = u a * v b := by
        simp [dotProduct, Matrix.mulVec, Finset.sum_ite_eq, ite_and]
      rw [e, abs_mul]
      have s1 : |u a| ≤ Real.sqrt (u ⬝ᵥ u) := by
        rw [← Real.sqrt_sq_eq_abs]
        exact Real.sqrt_le_sqrt (by
          simp only [dotProduct]
          calc u a ^ 2 = u a * u a := sq _
            _ ≤ _ := Finset.single_le_sum (f := fun i => u i * u i) (fun i _ => mul_self_nonneg _) (Finset.mem_univ a))
      have s2 : |v b| ≤ Real.sqrt (v ⬝ᵥ v) := by
        rw [← Real.sqrt_sq_eq_abs]
        exact Real.sqrt_le_sqrt (by
          simp only [dotProduct]
          calc v b ^ 2 = v b * v b := sq _
            _ ≤ _ := Finset.single_le_sum (f := fun i => v i * v i) (fun i _ => mul_self_nonneg _) (Finset.mem_univ b))
      calc |u a| * |v b| ≤ Real.sqrt (u ⬝ᵥ u) * Real.sqrt (v ⬝ᵥ v) :=
            mul_le_mul s1 s2 (abs_nonneg _) (Real.sqrt_nonneg _)
        _ = 1 * Real.sqrt (u ⬝ᵥ u) * Real.sqrt (v ⬝ᵥ v) := by ring)
  have e : ∑ i, ∑ j, (Matrix.of fun i j => if i = a ∧ j = b then (1 : ℝ) else 0) i j * Q i j = Q a b := by
    simp [ite_and]
  rw [e] at h
  simpa using h

end HRS.Uniform.Q45
