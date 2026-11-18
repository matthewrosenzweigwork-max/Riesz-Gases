import HRS.MC.S7PIDDefs
import HRS.MC.S7PIDGCore

/-!
# Packet PI-D: proof of the finite Gaussian vectors (`s7_PID_gauss_vector`)

`s7_PID_gauss_vector_proof` is the proof of `HRS.MC.Sec7.PIDPlan.s7_PID_gauss_vector` (`HRS/MC/S7PIDPlan.lean`).
Route: the scalar family `F (inl (i,a)) = (w i)_a`, `F (inr (i,a)) = (w' i)_a` is indexed by `κ = (ι × Fin r) ⊕ (ι × Fin r)`;
the Gaussian vector is `P = multivariateGaussian 0 (S7PIDG_gram I F)` (see `HRS/MC/S7PIDGCore.lean`), and `Y i`, `Y' i` are
its coordinate blocks.  The identities are then:

* `E B(Y_i, Y'_j) = ∫_I B(w_i, w'_j)` by expanding `B` in the standard basis of `ℝ^r` and using the cross moments `G`;
* `E ‖Y_i - Y_j‖⁴ ≤ 3 (∫_I ‖w_i - w_j‖²)²`: `‖Y_i - Y_j‖² = ∑_a D_a²` with `D_a` linear forms of `P`, and
  `E D_a⁴ = 3 s_a²`, `E D_a² D_b² ≤ 3 s_a s_b` (`S7PIDG_cross_le`), `∑_a s_a = ∫_I ‖w_i - w_j‖²`;
* `E ‖Y_i‖² = ∫_I ‖w_i‖²` from the cross moments on the diagonal.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7PIDG

open HRS HRS.Sec7 HRS.MC.Sec7.PID
open Matrix

variable {d : ℕ}

lemma S7PIDG_norm_sq {r : ℕ} (x : EuclideanSpace ℝ (Fin r)) : ‖x‖ ^ 2 = ∑ a, x a * x a := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [Real.norm_eq_abs, sq]

/-- Expansion of a continuous bilinear form on `ℝ^r` in the standard basis. -/
lemma S7PIDG_bilin_expand {r : ℕ}
    (B : EuclideanSpace ℝ (Fin r) →L[ℝ] EuclideanSpace ℝ (Fin r) →L[ℝ] ℝ)
    (x y : EuclideanSpace ℝ (Fin r)) :
    B x y = ∑ a, ∑ b, x a * y b * B (EuclideanSpace.single a 1) (EuclideanSpace.single b 1) := by
  have hx : x = ∑ a, x a • EuclideanSpace.single a (1 : ℝ) := by
    ext c
    simp [Finset.sum_apply, Pi.single_apply]
  have hy : y = ∑ b, y b • EuclideanSpace.single b (1 : ℝ) := by
    ext c
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hx, hy]
  simp only [map_sum, _root_.sum_apply, ContinuousLinearMap.map_smul, _root_.smul_apply, smul_eq_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

/-- Expectation of a bilinear form of two coordinate blocks of the Gaussian family. -/
lemma S7PIDG_cross_expect {r : ℕ} {κ : Type} [Fintype κ] [DecidableEq κ] (I : Set ℝ)
    (F : κ → ℝ → ℝ) (hF : ∀ α, MemLp (F α) 2 (volume.restrict I))
    (A A' : Fin r → κ)
    (B : EuclideanSpace ℝ (Fin r) →L[ℝ] EuclideanSpace ℝ (Fin r) →L[ℝ] ℝ) :
    ∫ ω, B (WithLp.toLp 2 (fun a => ω (A a))) (WithLp.toLp 2 (fun a => ω (A' a)))
        ∂(ProbabilityTheory.multivariateGaussian (0 : EuclideanSpace ℝ κ) (S7PIDG_gram I F))
      = ∫ u in I, B (WithLp.toLp 2 (fun a => F (A a) u)) (WithLp.toLp 2 (fun a => F (A' a) u)) := by
  have hG := S7PIDG_gram_psd I F hF
  obtain ⟨-, hcross⟩ := S7PIDG_build (S7PIDG_gram I F) hG
  set P := ProbabilityTheory.multivariateGaussian (0 : EuclideanSpace ℝ κ) (S7PIDG_gram I F) with hP
  have hcoord : ∀ α, MemLp (fun ω : EuclideanSpace ℝ κ => ω α) 2 P :=
    fun α => S7PIDG_coord_memLp (S7PIDG_gram I F) α
  have hL : ∀ ω : EuclideanSpace ℝ κ, B (WithLp.toLp 2 (fun a => ω (A a)))
      (WithLp.toLp 2 (fun a => ω (A' a)))
      = ∑ a, ∑ b, ω (A a) * ω (A' b) * B (EuclideanSpace.single a 1) (EuclideanSpace.single b 1) := by
    intro ω
    rw [S7PIDG_bilin_expand]
  have hR : ∀ u, B (WithLp.toLp 2 (fun a => F (A a) u)) (WithLp.toLp 2 (fun a => F (A' a) u))
      = ∑ a, ∑ b, F (A a) u * F (A' b) u * B (EuclideanSpace.single a 1) (EuclideanSpace.single b 1) := by
    intro u
    rw [S7PIDG_bilin_expand]
  simp_rw [hL, hR]
  have hint : ∀ a b, Integrable (fun ω => ω (A a) * ω (A' b)) P :=
    fun a b => (hcoord (A a)).integrable_mul (hcoord (A' b))
  have hintI : ∀ a b, Integrable (fun u => F (A a) u * F (A' b) u) (volume.restrict I) :=
    fun a b => (hF (A a)).integrable_mul (hF (A' b))
  rw [integral_finsetSum _ (fun a _ => integrable_finsetSum _ fun b _ =>
    ((hint a b).mul_const _))]
  rw [integral_finsetSum _ (fun a _ => integrable_finsetSum _ fun b _ =>
    ((hintI a b).mul_const _))]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [integral_finsetSum _ (fun b _ => ((hint a b).mul_const _)),
    integral_finsetSum _ (fun b _ => ((hintI a b).mul_const _))]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [integral_mul_const, integral_mul_const]
  congr 1
  exact hcross (A a) (A' b)

/-- Expectation of the squared norm of a coordinate block of the Gaussian family. -/
lemma S7PIDG_norm2_expect {r : ℕ} {κ : Type} [Fintype κ] [DecidableEq κ] (I : Set ℝ)
    (F : κ → ℝ → ℝ) (hF : ∀ α, MemLp (F α) 2 (volume.restrict I)) (A : Fin r → κ) :
    ∫ ω, ‖WithLp.toLp 2 (fun a => ω (A a))‖ ^ 2
        ∂(ProbabilityTheory.multivariateGaussian (0 : EuclideanSpace ℝ κ) (S7PIDG_gram I F))
      = ∫ u in I, ‖WithLp.toLp 2 (fun a => F (A a) u)‖ ^ 2 := by
  have hG := S7PIDG_gram_psd I F hF
  obtain ⟨-, hcross⟩ := S7PIDG_build (S7PIDG_gram I F) hG
  set P := ProbabilityTheory.multivariateGaussian (0 : EuclideanSpace ℝ κ) (S7PIDG_gram I F) with hP
  have hcoord : ∀ α, MemLp (fun ω : EuclideanSpace ℝ κ => ω α) 2 P :=
    fun α => S7PIDG_coord_memLp (S7PIDG_gram I F) α
  simp only [S7PIDG_norm_sq]
  have hi : ∀ a, Integrable (fun ω : EuclideanSpace ℝ κ => ω (A a) * ω (A a)) P :=
    fun a => (hcoord (A a)).integrable_mul (hcoord (A a))
  have hiI : ∀ a, Integrable (fun u => F (A a) u * F (A a) u) (volume.restrict I) :=
    fun a => (hF (A a)).integrable_mul (hF (A a))
  rw [integral_finsetSum _ (fun a _ => hi a)]
  rw [integral_finsetSum _ (fun a _ => hiI a)]
  refine Finset.sum_congr rfl fun a _ => ?_
  exact hcross (A a) (A a)

/-- Fourth moment bound for the squared distance of two coordinate blocks of the Gaussian family. -/
lemma S7PIDG_norm4_expect {r : ℕ} {κ : Type} [Fintype κ] [DecidableEq κ] (I : Set ℝ)
    (F : κ → ℝ → ℝ) (hF : ∀ α, MemLp (F α) 2 (volume.restrict I)) (A A' : Fin r → κ) :
    ∫ ω, ‖WithLp.toLp 2 (fun a => ω (A a)) - WithLp.toLp 2 (fun a => ω (A' a))‖ ^ 4
        ∂(ProbabilityTheory.multivariateGaussian (0 : EuclideanSpace ℝ κ) (S7PIDG_gram I F))
      ≤ 3 * (∫ u in I, ‖WithLp.toLp 2 (fun a => F (A a) u)
          - WithLp.toLp 2 (fun a => F (A' a) u)‖ ^ 2) ^ 2 := by
  have hG := S7PIDG_gram_psd I F hF
  set P := ProbabilityTheory.multivariateGaussian (0 : EuclideanSpace ℝ κ) (S7PIDG_gram I F) with hP
  let cv : Fin r → κ → ℝ := fun a α => (if α = A a then 1 else 0) - (if α = A' a then 1 else 0)
  have hlin : ∀ a (ω : EuclideanSpace ℝ κ), ∑ α, cv a α * ω α = ω (A a) - ω (A' a) := by
    intro a ω
    simp [cv, sub_mul, Finset.sum_sub_distrib, ite_mul]
  have hquad : ∀ a, cv a ⬝ᵥ (S7PIDG_gram I F *ᵥ cv a)
      = ∫ u in I, (F (A a) u - F (A' a) u) ^ 2 := by
    intro a
    rw [S7PIDG_gram_quad I F hF]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    simp [cv, sub_mul, Finset.sum_sub_distrib, ite_mul]
  have hm4 : ∀ a, ∫ ω, (∑ α, cv a α * ω α) ^ 4 ∂P
      = 3 * (∫ u in I, (F (A a) u - F (A' a) u) ^ 2) ^ 2 := by
    intro a
    rw [← hquad a]
    exact (S7PIDG_lin_law_moments (S7PIDG_gram I F) hG (cv a)).1.2
  have hs : ∀ a, 0 ≤ ∫ u in I, (F (A a) u - F (A' a) u) ^ 2 :=
    fun a => integral_nonneg fun u => sq_nonneg _
  have key : ∫ ω, (∑ a, (∑ α, cv a α * ω α) ^ 2) ^ 2 ∂P
      ≤ 3 * (∑ a, ∫ u in I, (F (A a) u - F (A' a) u) ^ 2) ^ 2 :=
    S7PIDG_sum_sq_le (P := P) (fun a ω => ∑ α, cv a α * ω α)
      (fun a => ∫ u in I, (F (A a) u - F (A' a) u) ^ 2) hs
      (fun a => S7PIDG_lin_measurable (cv a))
      (fun a => (S7PIDG_lin_law_moments (S7PIDG_gram I F) hG (cv a)).1.1) hm4
  have hpt : ∀ ω : EuclideanSpace ℝ κ,
      ‖WithLp.toLp 2 (fun a => ω (A a)) - WithLp.toLp 2 (fun a => ω (A' a))‖ ^ 4
        = (∑ a, (∑ α, cv a α * ω α) ^ 2) ^ 2 := by
    intro ω
    have h2 : ‖WithLp.toLp 2 (fun a => ω (A a)) - WithLp.toLp 2 (fun a => ω (A' a))‖ ^ 2
        = ∑ a, (∑ α, cv a α * ω α) ^ 2 := by
      rw [S7PIDG_norm_sq]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [hlin a ω]
      simp only [PiLp.sub_apply]
      ring
    rw [show ‖WithLp.toLp 2 (fun a => ω (A a)) - WithLp.toLp 2 (fun a => ω (A' a))‖ ^ 4
      = (‖WithLp.toLp 2 (fun a => ω (A a)) - WithLp.toLp 2 (fun a => ω (A' a))‖ ^ 2) ^ 2 by ring, h2]
  have hR : ∑ a, ∫ u in I, (F (A a) u - F (A' a) u) ^ 2
      = ∫ u in I, ‖WithLp.toLp 2 (fun a => F (A a) u)
          - WithLp.toLp 2 (fun a => F (A' a) u)‖ ^ 2 := by
    have hiD : ∀ a, Integrable (fun u => (F (A a) u - F (A' a) u) ^ 2) (volume.restrict I) :=
      fun a => ((hF (A a)).sub (hF (A' a))).integrable_sq
    rw [← integral_finsetSum _ (fun a _ => hiD a)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    dsimp only
    rw [S7PIDG_norm_sq]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [PiLp.sub_apply]
    ring
  rw [← hR]
  simp_rw [hpt]
  exact key

/-- The two-family Gaussian vector of `s7_PID_gauss_vector`: the coordinate functions of `F` on
`κ = (ι × Fin r) ⊕ (ι × Fin r)`. -/
lemma S7PIDG_vec_family {r : ℕ} {ι : Type} [Fintype ι] (I : Set ℝ)
    (w w' : ι → ℝ → EuclideanSpace ℝ (Fin r))
    (hw : ∀ i, MemLp (w i) 2 (volume.restrict I)) (hw' : ∀ i, MemLp (w' i) 2 (volume.restrict I)) :
    ∀ α, MemLp (Sum.elim (fun p : ι × Fin r => fun u => w p.1 u p.2)
        (fun p : ι × Fin r => fun u => w' p.1 u p.2) α) 2 (volume.restrict I) := by
  rintro (⟨i, a⟩ | ⟨i, a⟩)
  · exact (EuclideanSpace.proj a : EuclideanSpace ℝ (Fin r) →L[ℝ] ℝ).comp_memLp' (hw i)
  · exact (EuclideanSpace.proj a : EuclideanSpace ℝ (Fin r) →L[ℝ] ℝ).comp_memLp' (hw' i)

theorem s7_PID_gauss_vector_proof {r : ℕ} {ι : Type} [Fintype ι] (I : Set ℝ)
    (w w' : ι → ℝ → EuclideanSpace ℝ (Fin r))
    (hw : ∀ i, MemLp (w i) 2 (volume.restrict I)) (hw' : ∀ i, MemLp (w' i) 2 (volume.restrict I)) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (Y Y' : ι → Ω → EuclideanSpace ℝ (Fin r)),
      (∀ i, Measurable (Y i)) ∧ (∀ i, Measurable (Y' i)) ∧
      (∀ (B : EuclideanSpace ℝ (Fin r) →L[ℝ] EuclideanSpace ℝ (Fin r) →L[ℝ] ℝ) (i j : ι),
        ∫ ω, B (Y i ω) (Y' j ω) ∂P = ∫ u in I, B (w i u) (w' j u)) ∧
      (∀ i j, ∫ ω, ‖Y i ω - Y j ω‖ ^ 4 ∂P ≤ 3 * (∫ u in I, ‖w i u - w j u‖ ^ 2) ^ 2) ∧
      (∀ i j, ∫ ω, ‖Y' i ω - Y' j ω‖ ^ 4 ∂P ≤ 3 * (∫ u in I, ‖w' i u - w' j u‖ ^ 2) ^ 2) ∧
      (∀ i, ∫ ω, ‖Y i ω‖ ^ 2 ∂P = ∫ u in I, ‖w i u‖ ^ 2) ∧
      (∀ i, ∫ ω, ‖Y' i ω‖ ^ 2 ∂P = ∫ u in I, ‖w' i u‖ ^ 2) := by
  classical
  set F : (ι × Fin r) ⊕ (ι × Fin r) → ℝ → ℝ :=
    Sum.elim (fun p : ι × Fin r => fun u => w p.1 u p.2)
      (fun p : ι × Fin r => fun u => w' p.1 u p.2) with hFdef
  have hF : ∀ α, MemLp (F α) 2 (volume.restrict I) := S7PIDG_vec_family I w w' hw hw'
  refine ⟨EuclideanSpace ℝ ((ι × Fin r) ⊕ (ι × Fin r)), inferInstance,
    ProbabilityTheory.multivariateGaussian (0 : EuclideanSpace ℝ ((ι × Fin r) ⊕ (ι × Fin r)))
      (S7PIDG_gram I F), inferInstance,
    fun i ω => WithLp.toLp 2 (fun a => ω (Sum.inl (i, a))),
    fun i ω => WithLp.toLp 2 (fun a => ω (Sum.inr (i, a))), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    fun_prop
  · intro i
    fun_prop
  · intro B i j
    exact S7PIDG_cross_expect I F hF (fun a => Sum.inl (i, a)) (fun a => Sum.inr (j, a)) B
  · intro i j
    exact S7PIDG_norm4_expect I F hF (fun a => Sum.inl (i, a)) (fun a => Sum.inl (j, a))
  · intro i j
    exact S7PIDG_norm4_expect I F hF (fun a => Sum.inr (i, a)) (fun a => Sum.inr (j, a))
  · intro i
    exact S7PIDG_norm2_expect I F hF (fun a => Sum.inl (i, a))
  · intro i
    exact S7PIDG_norm2_expect I F hF (fun a => Sum.inr (i, a))

end HRS.MC.Sec7.S7PIDG

end
