import HRS.MS.SA16PRiesz8

/-!
# SA16P, part 9: a diagonal Arzelà-Ascoli lemma for countably many bounded equi-Lipschitz families

`sa16p_diag`: for countably many sequences `n ↦ f k n` of functions on `[0,t]`, each uniformly bounded and
uniformly Lipschitz in `n`, there is ONE subsequence along which every `f k n` converges at every point of `[0,t]`,
and the limit `A k` is Lipschitz.  (Dense sequence of times, product compactness for the pointwise diagonal limit,
equi-Lipschitz continuity for the extension to all times.)
-/

noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open MeasureTheory Filter Topology Set Function
open scoped ENNReal NNReal

namespace HRS.Whole.AppendixA.Phase2SA16P

lemma sa16p_diag {κ : Type*} [Countable κ] (t : ℝ) (f : κ → ℕ → ℝ → ℝ)
    (hb : ∀ k, ∃ M : ℝ, ∀ n, ∀ τ ∈ Icc (0 : ℝ) t, |f k n τ| ≤ M)
    (hL : ∀ k, ∃ L : ℝ≥0, ∀ n, LipschitzOnWith L (f k n) (Icc (0 : ℝ) t)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ A : κ → ℝ → ℝ,
      (∀ k, ∀ τ ∈ Icc (0 : ℝ) t, Tendsto (fun j => f k (φ j) τ) atTop (𝓝 (A k τ))) ∧
      ∀ k, ∃ L : ℝ≥0, LipschitzOnWith L (A k) (Icc (0 : ℝ) t) := by
  classical
  choose M hM using hb
  choose L hL' using hL
  rcases (Icc (0 : ℝ) t).eq_empty_or_nonempty with hemp | hne
  · refine ⟨id, strictMono_id, fun _ _ => 0, ?_, fun k => ⟨0, ?_⟩⟩
    · intro k τ hτ; rw [hemp] at hτ; exact absurd hτ (Set.notMem_empty _)
    · rw [hemp]; exact LipschitzOnWith.of_dist_le_mul fun x hx => absurd hx (Set.notMem_empty _)
  have : Nonempty (Icc (0 : ℝ) t) := hne.to_subtype
  let r : ℕ → Icc (0 : ℝ) t := TopologicalSpace.denseSeq (Icc (0 : ℝ) t)
  have hr : DenseRange r := TopologicalSpace.denseRange_denseSeq _
  -- the compact set of values
  let K : Set (κ × ℕ → ℝ) := Set.pi univ (fun kj => Icc (-(|M kj.1|)) (|M kj.1|))
  have hKc : IsCompact K := isCompact_univ_pi (fun kj => isCompact_Icc)
  let x : ℕ → (κ × ℕ → ℝ) := fun n kj => f kj.1 n (r kj.2)
  have hx : ∀ n, x n ∈ K := by
    intro n kj _
    have := hM kj.1 n (r kj.2) (r kj.2).2
    exact ⟨neg_le_of_abs_le (this.trans (le_abs_self _)), (le_abs_self _).trans' (le_of_abs_le (by exact this))⟩
  obtain ⟨a, -, φ, hφ, hlim⟩ := hKc.tendsto_subseq hx
  have hpt : ∀ k j0, Tendsto (fun j => f k (φ j) (r j0)) atTop (𝓝 (a (k, j0))) := by
    intro k j0
    exact (tendsto_pi_nhds.1 hlim (k, j0))
  -- extension to all times: Cauchy
  have hcauchy : ∀ k, ∀ τ ∈ Icc (0 : ℝ) t, CauchySeq (fun j => f k (φ j) τ) := by
    intro k τ hτ
    rw [Metric.cauchySeq_iff]
    intro ε hε
    have hδ : 0 < ε / (4 * ((L k : ℝ) + 1)) := by positivity
    obtain ⟨j0, hj0⟩ := hr.exists_dist_lt (⟨τ, hτ⟩ : Icc (0 : ℝ) t) hδ
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.1 (hpt k j0).cauchySeq (ε / 2) (by positivity)
    refine ⟨N, fun n hn m hm => ?_⟩
    have hd : |τ - (r j0 : ℝ)| < ε / (4 * ((L k : ℝ) + 1)) := by
      have := hj0
      rw [Subtype.dist_eq, Real.dist_eq] at this
      rwa [abs_sub_comm] at this
    have l1 := (hL' k (φ n)).dist_le_mul τ hτ (r j0).1 (r j0).2
    have l2 := (hL' k (φ m)).dist_le_mul τ hτ (r j0).1 (r j0).2
    simp only [Real.dist_eq] at l1 l2
    have hNN := hN n hn m hm
    rw [Real.dist_eq] at hNN ⊢
    have hLk : (L k : ℝ) * (ε / (4 * ((L k : ℝ) + 1))) ≤ ε / 4 := by
      rw [← mul_div_assoc, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [(L k).coe_nonneg, hε]
    have hLd : (L k : ℝ) * |τ - (r j0 : ℝ)| ≤ ε / 4 :=
      (mul_le_mul_of_nonneg_left hd.le (L k).coe_nonneg).trans hLk
    have e1 : |f k (φ n) τ - f k (φ m) τ| ≤ |f k (φ n) τ - f k (φ n) (r j0)| +
        |f k (φ n) (r j0) - f k (φ m) (r j0)| + |f k (φ m) (r j0) - f k (φ m) τ| := by
      have := abs_sub_le (f k (φ n) τ) (f k (φ n) (r j0)) (f k (φ m) τ)
      have h2 := abs_sub_le (f k (φ n) (r j0)) (f k (φ m) (r j0)) (f k (φ m) τ)
      linarith [abs_sub_comm (f k (φ n) τ) (f k (φ n) (r j0))]
    rw [abs_sub_comm (f k (φ m) (r j0)) (f k (φ m) τ)] at e1
    have l1' : |f k (φ n) τ - f k (φ n) (r j0)| ≤ L k * |τ - (r j0 : ℝ)| := by simpa using l1
    have l2' : |f k (φ m) τ - f k (φ m) (r j0)| ≤ L k * |τ - (r j0 : ℝ)| := by simpa using l2
    linarith
  choose A hA using fun k => fun τ : Icc (0 : ℝ) t => cauchySeq_tendsto_of_complete (hcauchy k τ.1 τ.2)
  refine ⟨φ, hφ, fun k τ => if hτ : τ ∈ Icc (0 : ℝ) t then A k ⟨τ, hτ⟩ else 0, ?_, ?_⟩
  · intro k τ hτ
    simpa [hτ] using hA k ⟨τ, hτ⟩
  · intro k
    refine ⟨L k, LipschitzOnWith.of_dist_le_mul fun τ hτ τ' hτ' => ?_⟩
    simp only [hτ, hτ', dif_pos]
    have h1 := hA k ⟨τ, hτ⟩
    have h2 := hA k ⟨τ', hτ'⟩
    have h3 : Tendsto (fun j => dist (f k (φ j) τ) (f k (φ j) τ')) atTop (𝓝 (dist (A k ⟨τ, hτ⟩) (A k ⟨τ', hτ'⟩))) :=
      h1.dist h2
    refine le_of_tendsto h3 (Eventually.of_forall fun j => ?_)
    have := (hL' k (φ j)).dist_le_mul τ hτ τ' hτ'
    simpa [Real.dist_eq] using this

end HRS.Whole.AppendixA.Phase2SA16P
