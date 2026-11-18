import HRS.MS.SpecAux6

/-!
# S8P: entries of the root difference `X = S - E` (generic, for the PSD-root lemma of S8.7)

Namespace `HRS.MS.Spec`, helper prefix `s8p_`.  `S` symmetric on a real Hilbert space with Hilbert basis `b`, `E b_i = e_i b_i`.
`ξ_j = S b_j - e_j b_j`, `x_{ij} = ⟨b_i, ξ_j⟩`; Parseval identities and `⟨S b_i, S b_j⟩ - e_i² δ_{ij} = ⟨ξ_i, ξ_j⟩ + (e_i+e_j) x_{ij}`.
-/

noncomputable section

open Filter Topology
open scoped RealInnerProductSpace ENNReal

namespace HRS.MS.Spec

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  {ι : Type*}

/-- `ξ_j = (S - E) b_j`. -/
def s8p_xi (S : H →L[ℝ] H) (e : ι → ℝ) (b : HilbertBasis ι ℝ H) (j : ι) : H :=
  S (b j) - e j • b j

/-- `x_{ij} = ⟨b_i, (S-E) b_j⟩`. -/
def s8p_x (S : H →L[ℝ] H) (e : ι → ℝ) (b : HilbertBasis ι ℝ H) (i j : ι) : ℝ :=
  ⟪b i, s8p_xi S e b j⟫

theorem s8p_binner [DecidableEq ι] (b : HilbertBasis ι ℝ H) (i j : ι) :
    ⟪b i, b j⟫ = if i = j then 1 else 0 :=
  orthonormal_iff_ite.1 b.orthonormal i j

theorem s8p_x_eq [DecidableEq ι] (S : H →L[ℝ] H) (e : ι → ℝ) (b : HilbertBasis ι ℝ H) (i j : ι) :
    s8p_x S e b i j = ⟪b i, S (b j)⟫ - (if i = j then e j else 0) := by
  unfold s8p_x s8p_xi
  rw [inner_sub_right, inner_smul_right, s8p_binner]
  split_ifs <;> simp

theorem s8p_x_symm [DecidableEq ι] (S : H →L[ℝ] H) (hSs : ∀ x y, ⟪S x, y⟫ = ⟪x, S y⟫) (e : ι → ℝ)
    (b : HilbertBasis ι ℝ H) (i j : ι) : s8p_x S e b i j = s8p_x S e b j i := by
  rw [s8p_x_eq, s8p_x_eq, ← hSs, real_inner_comm]
  by_cases h : i = j
  · subst h; rfl
  · simp [h, Ne.symm h]

theorem s8p_x_col (S : H →L[ℝ] H) (e : ι → ℝ) (b : HilbertBasis ι ℝ H) (j : ι) :
    HasSum (fun i => s8p_x S e b i j ^ 2) (‖s8p_xi S e b j‖ ^ 2) := by
  have h := b.hasSum_inner_mul_inner (s8p_xi S e b j) (s8p_xi S e b j)
  rw [real_inner_self_eq_norm_sq] at h
  have : (fun i => s8p_x S e b i j ^ 2) =
      fun i => ⟪s8p_xi S e b j, b i⟫ * ⟪b i, s8p_xi S e b j⟫ := by
    funext i
    unfold s8p_x
    rw [real_inner_comm (b i) (s8p_xi S e b j)]; ring
  rw [this]; exact h

theorem s8p_x_inner (S : H →L[ℝ] H) (e : ι → ℝ) (b : HilbertBasis ι ℝ H) (i j : ι) :
    HasSum (fun k => s8p_x S e b k i * s8p_x S e b k j) ⟪s8p_xi S e b i, s8p_xi S e b j⟫ := by
  have h := b.hasSum_inner_mul_inner (s8p_xi S e b i) (s8p_xi S e b j)
  have : (fun k => s8p_x S e b k i * s8p_x S e b k j) =
      fun k => ⟪s8p_xi S e b i, b k⟫ * ⟪b k, s8p_xi S e b j⟫ := by
    funext k
    unfold s8p_x
    rw [real_inner_comm (b k) (s8p_xi S e b i)]
  rw [this]; exact h

theorem s8p_delta_eq [DecidableEq ι] (S : H →L[ℝ] H) (hSs : ∀ x y, ⟪S x, y⟫ = ⟪x, S y⟫)
    (e : ι → ℝ) (b : HilbertBasis ι ℝ H) (i j : ι) :
    ⟪S (b i), S (b j)⟫ - (if i = j then e i ^ 2 else 0) =
      ⟪s8p_xi S e b i, s8p_xi S e b j⟫ + (e i + e j) * s8p_x S e b i j := by
  have h1 : S (b i) = s8p_xi S e b i + e i • b i := by unfold s8p_xi; abel
  have h2 : S (b j) = s8p_xi S e b j + e j • b j := by unfold s8p_xi; abel
  have h3 : ⟪s8p_xi S e b i, b j⟫ = s8p_x S e b i j := by
    have := s8p_x_symm S hSs e b j i
    unfold s8p_x at this ⊢
    rw [real_inner_comm (b j) (s8p_xi S e b i)]
    exact this
  have h4 : ⟪S (b i), S (b j)⟫ = ⟪s8p_xi S e b i + e i • b i, s8p_xi S e b j + e j • b j⟫ := by
    rw [← h1, ← h2]
  rw [h4]
  simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
    RCLike.conj_to_real, s8p_binner, h3]
  unfold s8p_x
  by_cases hij : i = j
  · subst hij; simp; ring
  · simp [hij]; ring

end HRS.MS.Spec
