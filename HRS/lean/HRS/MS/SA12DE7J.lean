import HRS.MS.SA12DE7I

/-!
# S.A.12(c), packet E7.07 (worker S82Z2), part J: a common weakly convergent subsequence for a finite family

`sa12de7_weak_subseq_family`: finitely many sequences, each bounded by `B` in a separable real Hilbert space, have a common
subsequence along which every one converges weakly; the weighted energy of the limits is at most the weighted limit
inferior of the energies (`sa12de7_weighted_lsc`, elementary Cauchy-Schwarz with the weak limit tested against itself).
-/

set_option autoImplicit false
noncomputable section

open Filter Topology

namespace HRS.MS.SA12DE7

theorem sa12de7_weak_subseq_family {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] {ι : Type*} [Fintype ι] (J : ι → ℕ → H) {B : ℝ}
    (hB : ∀ i n, ‖J i n‖ ≤ B) :
    ∃ (φ : ℕ → ℕ) (g : ι → H), StrictMono φ ∧
      ∀ (i : ι) (v : H), Tendsto (fun n => inner ℝ (J i (φ n)) v) atTop (𝓝 (inner ℝ (g i) v)) := by
  classical
  have key : ∀ s : Finset ι, ∃ (φ : ℕ → ℕ) (g : ι → H), StrictMono φ ∧
      ∀ i ∈ s, ∀ v : H, Tendsto (fun n => inner ℝ (J i (φ n)) v) atTop (𝓝 (inner ℝ (g i) v)) := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨id, fun _ => 0, strictMono_id, fun i hi => absurd hi (Finset.notMem_empty i)⟩
    | insert a s ha ih =>
      obtain ⟨φ, g, hφ, hg⟩ := ih
      obtain ⟨ψ, ga, hψ, -, hga⟩ := sa12de7_weak_subseq (fun n => J a (φ n)) (fun n => hB a (φ n))
      refine ⟨φ ∘ ψ, Function.update g a ga, hφ.comp hψ, ?_⟩
      intro i hi v
      rcases Finset.mem_insert.1 hi with rfl | hi'
      · simpa using hga v
      · have hne : i ≠ a := fun h => ha (h ▸ hi')
        rw [Function.update_of_ne hne]
        exact (hg i hi' v).comp hψ.tendsto_atTop
  obtain ⟨φ, g, hφ, hg⟩ := key Finset.univ
  exact ⟨φ, g, hφ, fun i v => hg i (Finset.mem_univ i) v⟩

/-- Weighted lower semicontinuity of the energy under a weak limit: if `J i n → g i` weakly and
`∑ w i ‖J i n‖² ≤ B²` for all `n`, with `w i ≥ 0`, then `∑ w i ‖g i‖² ≤ B²`. -/
theorem sa12de7_weighted_lsc {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (J : ι → ℕ → H) (g : ι → H) {B : ℝ}
    (hJ : ∀ n, ∑ i, w i * ‖J i n‖ ^ 2 ≤ B ^ 2)
    (hlim : ∀ (i : ι) (v : H), Tendsto (fun n => inner ℝ (J i n) v) atTop (𝓝 (inner ℝ (g i) v))) :
    ∑ i, w i * ‖g i‖ ^ 2 ≤ B ^ 2 := by
  set S : ℝ := ∑ i, w i * ‖g i‖ ^ 2 with hS
  -- `∑ w i ⟪J i n, g i⟫ → S`
  have hconv : Tendsto (fun n => ∑ i, w i * inner ℝ (J i n) (g i)) atTop (𝓝 S) := by
    have h := tendsto_finset_sum Finset.univ fun i _ => (hlim i (g i)).const_mul (w i)
    have e : ∑ i, w i * inner ℝ (g i) (g i) = S := Finset.sum_congr rfl fun i _ => by
      rw [real_inner_self_eq_norm_sq]
    rwa [e] at h
  -- `0 ≤ ∑ w i ‖J i n - g i‖² = ∑ w i ‖J i n‖² - 2 ∑ w i ⟪J i n, g i⟫ + S`
  have hn : ∀ n, 2 * ∑ i, w i * inner ℝ (J i n) (g i) ≤ B ^ 2 + S := by
    intro n
    have h0 : 0 ≤ ∑ i, w i * ‖J i n - g i‖ ^ 2 := Finset.sum_nonneg fun i _ => mul_nonneg (hw i) (sq_nonneg _)
    have e : ∑ i, w i * ‖J i n - g i‖ ^ 2 =
        ∑ i, w i * ‖J i n‖ ^ 2 - 2 * ∑ i, w i * inner ℝ (J i n) (g i) + S := by
      rw [hS, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [norm_sub_sq_real]
      ring
    have := hJ n
    linarith
  have hlimit : 2 * S ≤ B ^ 2 + S := le_of_tendsto' (hconv.const_mul 2) hn
  linarith

end HRS.MS.SA12DE7
