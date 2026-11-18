import HRS.MS.S111TermAux4

/-!
# S11.1 terminal wave, G01 part 3: feature vectors `k ↦ (⟨F(α), e_k⟩)_α` in `ℓ²(ℕ^d)`
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.S111T

open HRS.Whole

variable {d : ℕ} {m : ℝ}
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

open Classical in
/-- The vector `(⟨f α, e k⟩)_α ∈ B_m` (`0` if it is not square summable). -/
def s111t_vec (m : ℝ) (e : HilbertBasis ℕ ℝ E) (f : MultiIndex d → E) (k : ℕ) : OscDual d m :=
  if h : Memℓp (fun α : MultiIndex d => inner ℝ (f α) (e k)) 2 then
    (⟨fun α => inner ℝ (f α) (e k), h⟩ : lp (fun _ : MultiIndex d => ℝ) 2)
  else 0

theorem s111t_oscdual_ext {u v : OscDual d m} (h : ∀ α, OscDual.coord u α = OscDual.coord v α) : u = v :=
  lp.ext (funext h)

theorem s111t_sq_inner_le (e : HilbertBasis ℕ ℝ E) (x : E) (k : ℕ) :
    (inner ℝ x (e k)) ^ 2 ≤ ‖x‖ ^ 2 := by
  have h := abs_real_inner_le_norm x (e k)
  have hn : ‖e k‖ = 1 := e.orthonormal.norm_eq_one k
  rw [hn, mul_one] at h
  calc (inner ℝ x (e k)) ^ 2 = |inner ℝ x (e k)| ^ 2 := (sq_abs _).symm
    _ ≤ ‖x‖ ^ 2 := by gcongr

theorem s111t_memell_vec (e : HilbertBasis ℕ ℝ E) (f : MultiIndex d → E)
    (hf : Summable fun α => ‖f α‖ ^ 2) (k : ℕ) :
    Memℓp (fun α : MultiIndex d => inner ℝ (f α) (e k)) 2 := by
  apply s111t_memell2
  exact Summable.of_nonneg_of_le (fun _ => sq_nonneg _) (fun α => s111t_sq_inner_le e (f α) k) hf

theorem s111t_coord_vec (e : HilbertBasis ℕ ℝ E) (f : MultiIndex d → E)
    (hf : Summable fun α => ‖f α‖ ^ 2) (k : ℕ) (α : MultiIndex d) :
    OscDual.coord (s111t_vec m e f k) α = inner ℝ (f α) (e k) := by
  simp [s111t_vec, s111t_memell_vec e f hf k, OscDual.coord]

theorem s111t_vec_sub (e : HilbertBasis ℕ ℝ E) (f f' : MultiIndex d → E)
    (hf : Summable fun α => ‖f α‖ ^ 2) (hf' : Summable fun α => ‖f' α‖ ^ 2) (k : ℕ) :
    s111t_vec m e (fun α => f α - f' α) k = s111t_vec m e f k - s111t_vec m e f' k := by
  have hff : Summable fun α => ‖f α - f' α‖ ^ 2 := by
    refine Summable.of_nonneg_of_le (fun _ => sq_nonneg _) (fun α => ?_)
      ((hf.add hf').mul_left 2)
    have := norm_sub_le (f α) (f' α)
    nlinarith [norm_nonneg (f α), norm_nonneg (f' α), norm_nonneg (f α - f' α),
      sq_nonneg (‖f α‖ - ‖f' α‖)]
  refine s111t_oscdual_ext fun α => ?_
  have h1 := s111t_coord_vec (m := m) e _ hff k α
  have h2 := s111t_coord_vec (m := m) e _ hf k α
  have h3 := s111t_coord_vec (m := m) e _ hf' k α
  have h4 : OscDual.coord (s111t_vec m e f k - s111t_vec m e f' k) α =
      OscDual.coord (s111t_vec m e f k) α - OscDual.coord (s111t_vec m e f' k) α := by
    have := OscDual.coord_add (s111t_vec m e f k) (-(s111t_vec m e f' k)) α
    have h5 := OscDual.coord_smul (-1 : ℝ) (s111t_vec m e f' k) α
    simp only [neg_smul, one_smul] at h5
    rw [sub_eq_add_neg, this, h5]; ring
  rw [h4, h1, h2, h3, inner_sub_left]

/-- Parseval: the `k`-vectors have total squared norm `Σ_α ‖f α‖²`. -/
theorem s111t_vec_norm_sq_summable (e : HilbertBasis ℕ ℝ E) (f : MultiIndex d → E)
    (hf : Summable fun α => ‖f α‖ ^ 2) :
    Summable (fun k => ‖s111t_vec m e f k‖ ^ 2) ∧
      ∑' k, ‖s111t_vec m e f k‖ ^ 2 = ∑' α, ‖f α‖ ^ 2 := by
  have hnorm : ∀ k, ‖s111t_vec m e f k‖ ^ 2 = ∑' α, (inner ℝ (f α) (e k)) ^ 2 := by
    intro k
    have h := lp_two_norm_sq (ι := MultiIndex d) (show lp (fun _ : MultiIndex d => ℝ) 2 from s111t_vec m e f k)
    have hn : ‖s111t_vec m e f k‖ = ‖(show lp (fun _ : MultiIndex d => ℝ) 2 from s111t_vec m e f k)‖ := rfl
    rw [hn, h]
    refine tsum_congr fun α => ?_
    have := s111t_coord_vec (m := m) e f hf k α
    simp only [OscDual.coord] at this
    rw [this]
  have hpar : ∀ α, ∑' k, (inner ℝ (f α) (e k)) ^ 2 = ‖f α‖ ^ 2 := by
    intro α
    have := e.tsum_inner_mul_inner (f α) (f α)
    rw [real_inner_self_eq_norm_sq] at this
    rw [← this]
    refine tsum_congr fun k => ?_
    rw [real_inner_comm, sq]
  have hsum : ∀ α, Summable fun k => (inner ℝ (f α) (e k)) ^ 2 := by
    intro α
    have := e.summable_inner_mul_inner (f α) (f α)
    refine this.congr fun k => ?_
    rw [real_inner_comm, sq]
  have hnn : (0 : MultiIndex d × ℕ → ℝ) ≤ fun p => (inner ℝ (f p.1) (e p.2)) ^ 2 :=
    fun p => sq_nonneg _
  have hprod : Summable (fun p : MultiIndex d × ℕ => (inner ℝ (f p.1) (e p.2)) ^ 2) := by
    refine (summable_prod_of_nonneg hnn).2 ⟨hsum, ?_⟩
    simpa [hpar] using hf
  have hnn' : (0 : ℕ × MultiIndex d → ℝ) ≤ fun p => (inner ℝ (f p.2) (e p.1)) ^ 2 :=
    fun p => sq_nonneg _
  have hprod' : Summable (fun p : ℕ × MultiIndex d => (inner ℝ (f p.2) (e p.1)) ^ 2) :=
    (Equiv.prodComm ℕ (MultiIndex d)).summable_iff.2 hprod
  simp_rw [hnorm]
  have h1 : Summable fun k : ℕ => ∑' α, (inner ℝ (f α) (e k)) ^ 2 := by
    have := ((summable_prod_of_nonneg hnn').1 hprod').2
    simp only at this
    exact this
  refine ⟨h1, ?_⟩
  have h2 : ∑' (k : ℕ) (α : MultiIndex d), (inner ℝ (f α) (e k)) ^ 2 =
      ∑' (α : MultiIndex d) (k : ℕ), (inner ℝ (f α) (e k)) ^ 2 :=
    Summable.tsum_comm (f := fun (α : MultiIndex d) (k : ℕ) => (inner ℝ (f α) (e k)) ^ 2) hprod
  rw [h2]
  exact tsum_congr hpar

end HRS.MS.S111T
