import HRS.MS.TransOpAux3

/-!
# S611 packet P1d: the capped-weight energy estimate

For `A : α ↦ (t ↦ A_α(t))` with `A_α' = a_α A_{α-e_i} - b_α A_{α+e_i}` (`a_α = √α_i/√2`, `b_α = √(α_i+1)/√2`) and `∑_α A_α(t)² = P`
for all `t`, the weighted sums `∑_{|α|≤N} λ_α^m A_α(t)²` are bounded by `exp(2m3^m|t|) ∑_α λ_α^m A_α(0)²`
(`s611_energy_bound`).  Proof: with the capped weight `min(λ_α, λ_N)^m` the boundary terms of the derivative vanish, so
`E_N = W P + ∑_{|α|≤N}(w_α - W) A_α²` satisfies `|E_N'| ≤ K E_N` (`s611_deriv_sum_eq`, `s611_sum_bound`), then Gronwall.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.TransOp

open HRS.Whole
open HRS (Euc)

variable {d : ℕ}

/-- `a_α = √α_i / √2`. -/
def s611_a (i : Fin d) (α : MultiIndex d) : ℝ := Real.sqrt (α i) / Real.sqrt 2

/-- `b_α = √(α_i+1) / √2`. -/
def s611_b (i : Fin d) (α : MultiIndex d) : ℝ := Real.sqrt ((α i : ℝ) + 1) / Real.sqrt 2

/-- The weight `λ_α^m`. -/
def s611_w (d m : ℕ) (α : MultiIndex d) : ℝ := oscEigenvalue d α ^ m

theorem s611_a_nonneg (i : Fin d) (α : MultiIndex d) : 0 ≤ s611_a i α := by
  unfold s611_a; positivity

theorem s611_b_nonneg (i : Fin d) (α : MultiIndex d) : 0 ≤ s611_b i α := by
  unfold s611_b; positivity

theorem s611_a_inc (i : Fin d) (α : MultiIndex d) : s611_a i (s611_inc α i) = s611_b i α := by
  unfold s611_a s611_b
  rw [s611_inc_apply]
  push_cast
  rfl

theorem s611_a_zero (i : Fin d) (α : MultiIndex d) (h : α i = 0) : s611_a i α = 0 := by
  unfold s611_a; simp [h]

/-- Reindexing identity for the derivative of the capped energy. -/
theorem s611_deriv_sum_eq (N : ℕ) (i : Fin d) (w : MultiIndex d → ℝ) (W : ℝ)
    (hW : ∀ α : MultiIndex d, α.degree = N → w α = W) (B : MultiIndex d → ℝ) :
    ∑ α ∈ s611_D d N, (w α - W) *
        (2 * B α * (s611_a i α * B (s611_dec α i) - s611_b i α * B (s611_inc α i))) =
      2 * ∑ β ∈ (s611_D d N).filter (fun β => 1 ≤ β i),
          s611_a i β * B β * B (s611_dec β i) * (w β - w (s611_dec β i)) := by
  set F := (s611_D d N).filter (fun β => 1 ≤ β i) with hF
  set G := (s611_D d N).filter (fun α => α.degree < N) with hG
  let f : MultiIndex d → ℝ := fun α => (w α - W) * (s611_a i α * B α * B (s611_dec α i))
  let g : MultiIndex d → ℝ := fun α => (w α - W) * (s611_b i α * B α * B (s611_inc α i))
  let g2 : MultiIndex d → ℝ := fun β => (w (s611_dec β i) - W) * (s611_a i β * B β * B (s611_dec β i))
  have hterm : ∀ α ∈ s611_D d N, (w α - W) *
      (2 * B α * (s611_a i α * B (s611_dec α i) - s611_b i α * B (s611_inc α i))) =
      2 * (f α - g α) := by
    intro α _
    simp only [f, g]
    ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, Finset.sum_sub_distrib]
  have hf : ∑ α ∈ s611_D d N, f α = ∑ β ∈ F, f β := by
    rw [hF]
    symm
    refine Finset.sum_filter_of_ne fun x hx hfx => ?_
    by_contra h
    have h0 : x i = 0 := by omega
    apply hfx
    simp only [f, s611_a_zero i x h0]
    ring
  have hg : ∑ α ∈ s611_D d N, g α = ∑ α ∈ G, g α := by
    rw [hG]
    symm
    refine Finset.sum_filter_of_ne fun x hx hgx => ?_
    have hxd := s611_mem_D.1 hx
    by_contra h
    have hdeg : x.degree = N := by omega
    apply hgx
    simp only [g, hW x hdeg]
    ring
  have hg2 : ∑ α ∈ G, g α = ∑ β ∈ F, g2 β := by
    refine Finset.sum_nbij' (fun α => s611_inc α i) (fun β => s611_dec β i) ?_ ?_ ?_ ?_ ?_
    · intro α hα
      rw [hG, Finset.mem_filter] at hα
      rw [hF, Finset.mem_filter]
      refine ⟨s611_mem_D.2 ?_, ?_⟩
      · rw [s611_degree_inc]; omega
      · rw [s611_inc_apply]; omega
    · intro β hβ
      rw [hF, Finset.mem_filter] at hβ
      rw [hG, Finset.mem_filter]
      have h1 := s611_degree_dec β i hβ.2
      have h2 := s611_mem_D.1 hβ.1
      exact ⟨s611_mem_D.2 (by omega), by omega⟩
    · intro α _
      exact s611_dec_inc α i
    · intro β hβ
      rw [hF, Finset.mem_filter] at hβ
      exact s611_inc_dec β i hβ.2
    · intro α _
      simp only [g, g2, s611_dec_inc, s611_a_inc]
      ring
  rw [hf, hg, hg2, ← Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl fun β _ => ?_
  simp only [f, g2]
  ring

theorem s611_a_le (i : Fin d) (β : MultiIndex d) :
    s611_a i β ≤ oscEigenvalue d β / 2 := by
  have hl1 : 1 ≤ oscEigenvalue d β := oscEv_one_le β
  have hβi : (β i : ℝ) ≤ (β.degree : ℝ) := by
    have : β i ≤ β.degree :=
      Finset.single_le_sum (f := fun j => β j) (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
    exact_mod_cast this
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hlam : oscEigenvalue d β = 2 * (β.degree : ℝ) + d + 1 := rfl
  unfold s611_a
  rw [← Real.sqrt_div (Nat.cast_nonneg _)]
  rw [Real.sqrt_le_left (by linarith)]
  nlinarith

theorem s611_eig_dec (i : Fin d) (β : MultiIndex d) (h : 1 ≤ β i) :
    oscEigenvalue d (s611_dec β i) = oscEigenvalue d β - 2 := by
  have h1 := s611_degree_dec β i h
  have h2 : ((s611_dec β i).degree : ℝ) + 1 = (β.degree : ℝ) := by exact_mod_cast h1
  show 2 * ((s611_dec β i).degree : ℝ) + d + 1 = (2 * (β.degree : ℝ) + d + 1) - 2
  linarith

theorem s611_three_le (i : Fin d) (β : MultiIndex d) (h : 1 ≤ β i) : 3 ≤ oscEigenvalue d β := by
  have hβi : 1 ≤ β.degree := by
    have : β i ≤ β.degree :=
      Finset.single_le_sum (f := fun j => β j) (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
    omega
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have : (1 : ℝ) ≤ (β.degree : ℝ) := by exact_mod_cast hβi
  show 3 ≤ 2 * (β.degree : ℝ) + d + 1
  linarith

/-- The bound on the (reindexed) derivative of the energy. -/
theorem s611_sum_bound (m : ℕ) (hm : 1 ≤ m) (N : ℕ) (i : Fin d) (B : MultiIndex d → ℝ) :
    |∑ β ∈ (s611_D d N).filter (fun β => 1 ≤ β i),
        s611_a i β * B β * B (s611_dec β i) * (s611_w d m β - s611_w d m (s611_dec β i))| ≤
      ((m : ℝ) * 3 ^ m / 2) * (2 * ∑ α ∈ s611_D d N, s611_w d m α * B α ^ 2) := by
  set F := (s611_D d N).filter (fun β => 1 ≤ β i) with hF
  have hterm : ∀ β ∈ F, |s611_a i β * B β * B (s611_dec β i) *
      (s611_w d m β - s611_w d m (s611_dec β i))| ≤
      ((m : ℝ) * 3 ^ m / 2) * (s611_w d m β * B β ^ 2 +
        s611_w d m (s611_dec β i) * B (s611_dec β i) ^ 2) := by
    intro β hβ
    rw [hF, Finset.mem_filter] at hβ
    have h := s611_term_le m hm (oscEigenvalue d β) (s611_a i β) (B β) (B (s611_dec β i))
      (s611_a_nonneg i β) (s611_a_le i β) (s611_three_le i β hβ.2)
    unfold s611_w
    rw [s611_eig_dec i β hβ.2]
    exact h
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.mul_sum, Finset.sum_add_distrib]
  have hpos : 0 ≤ ((m : ℝ) * 3 ^ m / 2) := by positivity
  refine mul_le_mul_of_nonneg_left ?_ hpos
  have hnn : ∀ α : MultiIndex d, 0 ≤ s611_w d m α * B α ^ 2 := fun α =>
    mul_nonneg (pow_nonneg (oscEv_pos α).le m) (sq_nonneg _)
  have h1 : ∑ β ∈ F, s611_w d m β * B β ^ 2 ≤ ∑ α ∈ s611_D d N, s611_w d m α * B α ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun α _ _ => hnn α
  have h2 : ∑ β ∈ F, s611_w d m (s611_dec β i) * B (s611_dec β i) ^ 2 ≤
      ∑ α ∈ s611_D d N, s611_w d m α * B α ^ 2 := by
    have hinj : Set.InjOn (fun β => s611_dec β i) (F : Set (MultiIndex d)) := by
      intro β1 h1 β2 h2 h12
      have h1' := (Finset.mem_filter.1 h1).2
      have h2' := (Finset.mem_filter.1 h2).2
      have := congrArg (fun γ => s611_inc γ i) h12
      simp only at this
      rwa [s611_inc_dec β1 i h1', s611_inc_dec β2 i h2'] at this
    rw [← Finset.sum_image (f := fun α => s611_w d m α * B α ^ 2) hinj]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun α _ _ => hnn α
    intro α hα
    rw [Finset.mem_image] at hα
    obtain ⟨β, hβ, rfl⟩ := hα
    rw [hF, Finset.mem_filter] at hβ
    have h1 := s611_degree_dec β i hβ.2
    have h2 := s611_mem_D.1 hβ.1
    exact s611_mem_D.2 (by omega)
  linarith

end HRS.MS.TransOp

end
