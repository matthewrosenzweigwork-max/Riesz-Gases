import HRS.MC.SEdgeB8bAux3

/-!
# Packet B8b, helper file 4: the characteristic function of the truncated linear statistics
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.SEdge.B8b

section Law

variable {Ω : Type*} [MeasurableSpace Ω] {p : ℕ}

/-- truncated linear statistic `(∑_{k<L} α_{a k} G_k)_a` -/
def b8b_XL (α : Fin p → ℕ → ℝ) (G : ℕ → Ω → ℝ) (L : ℕ) (ω : Ω) : EuclideanSpace ℝ (Fin p) :=
  WithLp.toLp 2 fun a => ∑ k ∈ Finset.range L, α a k * G k ω

/-- covariance of the truncated statistics -/
def b8b_CL (α : Fin p → ℕ → ℝ) (S : ℕ → ℕ → ℝ) (L : ℕ) (a b : Fin p) : ℝ :=
  ∑ k ∈ Finset.range L, ∑ l ∈ Finset.range L, α a k * α b l * S k l

theorem b8b_sum_comm3 {ι κ μ : Type*} [Fintype ι] [Fintype κ] [Fintype μ] (f : ι → κ → μ → ℝ) :
    ∑ i, ∑ j, ∑ k, f i j k = ∑ k, ∑ i, ∑ j, f i j k := by
  calc ∑ i, ∑ j, ∑ k, f i j k = ∑ i, ∑ k, ∑ j, f i j k :=
        Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = _ := Finset.sum_comm

theorem b8b_quad (α : Fin p → ℕ → ℝ) (S : ℕ → ℕ → ℝ) (L : ℕ) (t : Fin p → ℝ) :
    (fun k : Fin L => ∑ a, t a * α a k) ⬝ᵥ
        (Matrix.of fun i j : Fin L => S i j).mulVec (fun k : Fin L => ∑ a, t a * α a k) =
      ∑ a, ∑ b, t a * t b * b8b_CL α S L a b := by
  simp only [dotProduct, Matrix.mulVec, Matrix.of_apply, b8b_CL]
  have e1 : ∀ i : Fin L, (∑ a, t a * α a i) * ∑ j : Fin L, S i j * ∑ b, t b * α b j =
      ∑ a, ∑ j : Fin L, ∑ b, t a * t b * (α a i * α b j * S i j) := by
    intro i
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    ring
  simp_rw [e1]
  rw [Finset.sum_comm]
  have e2 : ∀ a : Fin p, ∑ i : Fin L, ∑ j : Fin L, ∑ b, t a * t b * (α a i * α b j * S i j) =
      ∑ b, t a * t b * ∑ i ∈ Finset.range L, ∑ j ∈ Finset.range L, α a i * α b j * S i j := by
    intro a
    rw [b8b_sum_comm3]
    refine Finset.sum_congr rfl fun b _ => ?_
    calc ∑ i : Fin L, ∑ j : Fin L, t a * t b * (α a i * α b j * S i j)
        = ∑ i : Fin L, t a * t b * ∑ j ∈ Finset.range L, α a i * α b j * S i j :=
          Finset.sum_congr rfl fun i _ => by
            rw [Finset.mul_sum]
            exact Fin.sum_univ_eq_sum_range (fun j => t a * t b * (α a i * α b j * S i j)) L
      _ = ∑ i ∈ Finset.range L, t a * t b * ∑ j ∈ Finset.range L, α a i * α b j * S i j :=
          Fin.sum_univ_eq_sum_range (fun i => t a * t b *
            ∑ j ∈ Finset.range L, α a i * α b j * S i j) L
      _ = _ := by rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => e2 a

theorem b8b_charFun_law {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] (P : Measure Ω)
    {X : Ω → E} (hX : Measurable X) (t : E) :
    charFun (P.map X) t = ∫ ω, Complex.exp (↑(inner ℝ (X ω) t) * Complex.I) ∂P := by
  rw [charFun_apply, integral_map hX.aemeasurable]
  exact (by fun_prop : Continuous fun x : E => Complex.exp (↑(inner ℝ x t) * Complex.I)).aestronglyMeasurable

theorem b8b_charFun_XL (P : Measure Ω) [IsProbabilityMeasure P] (G : ℕ → Ω → ℝ)
    (hGm : ∀ i, Measurable (G i)) (S : ℕ → ℕ → ℝ)
    (hSpsd : ∀ n, (Matrix.of fun i j : Fin n => S i j).PosSemidef)
    (hlaw : ∀ n, law P (fun ω => (WithLp.toLp 2 fun i : Fin n => G i ω :
        EuclideanSpace ℝ (Fin n))) = multivariateGaussian 0 (Matrix.of fun i j : Fin n => S i j))
    (α : Fin p → ℕ → ℝ) (L : ℕ) (t : EuclideanSpace ℝ (Fin p)) :
    charFun (P.map (b8b_XL α G L)) t =
      Complex.exp (↑(-(∑ a, ∑ b, t a * t b * b8b_CL α S L a b) / 2)) := by
  set V : Ω → EuclideanSpace ℝ (Fin L) := fun ω => WithLp.toLp 2 fun i : Fin L => G i ω with hV
  have hVm : Measurable V := by rw [hV]; fun_prop
  have hXm : Measurable (b8b_XL α G L) := by
    unfold b8b_XL
    fun_prop
  set s : EuclideanSpace ℝ (Fin L) := WithLp.toLp 2 fun k : Fin L => ∑ a, t a * α a k with hs
  have h1 : charFun (P.map (b8b_XL α G L)) t = charFun (P.map V) s := by
    rw [b8b_charFun_law P hXm, b8b_charFun_law P hVm]
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    have hin : inner ℝ (b8b_XL α G L ω) t = inner ℝ (V ω) s := by
      simp only [b8b_XL, hV, hs, PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
      have h5 : ∀ a, ∑ x_1 ∈ Finset.range L, α a x_1 * G x_1 ω = ∑ k : Fin L, α a k * G k ω :=
        fun a => (Fin.sum_univ_eq_sum_range (fun k => α a k * G k ω) L).symm
      simp_rw [h5]
      simp only [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun a _ => ?_
      ring
    show Complex.exp (↑(inner ℝ (b8b_XL α G L ω) t) * Complex.I) =
      Complex.exp (↑(inner ℝ (V ω) s) * Complex.I)
    rw [hin]
  rw [h1]
  have h2 := hlaw L
  change P.map V = _ at h2
  rw [h2, charFun_multivariateGaussian (hSpsd L)]
  have h3 := b8b_quad α S L t
  congr 1
  simp only [inner_zero_right, Complex.ofReal_zero, zero_mul, zero_sub]
  rw [show s.ofLp = fun k : Fin L => ∑ a, t a * α a k from rfl, h3]
  push_cast
  ring

end Law

end HRS.MC.SEdge.B8b
