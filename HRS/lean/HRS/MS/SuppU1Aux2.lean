import Mathlib

/-!
# U1 aux 2: finite-rank (sum of products of smooth functions) approximation of a continuous
kernel, uniformly on `closedBall R × closedBall R` (Stone-Weierstrass).
-/

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal NNReal ContDiff

namespace HRS.Whole.U1

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- functions `(x,y) ↦ ∑_i F_i(x) H_i(y)` with smooth `F_i, H_i`. -/
def U1ProdSet (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] : Set (E × E → ℝ) :=
  {f | ∃ (ι : Type) (_ : Fintype ι) (F H : ι → E → ℝ), (∀ i, ContDiff ℝ ∞ (F i)) ∧
      (∀ i, ContDiff ℝ ∞ (H i)) ∧ ∀ p : E × E, f p = ∑ i, F i p.1 * H i p.2}

lemma u1ProdSet_const (c : ℝ) : (fun _ : E × E => c) ∈ U1ProdSet E := by
  refine ⟨Unit, inferInstance, fun _ _ => c, fun _ _ => 1, fun _ => contDiff_const,
    fun _ => contDiff_const, fun p => by simp⟩

lemma u1ProdSet_add {f g : E × E → ℝ} (hf : f ∈ U1ProdSet E) (hg : g ∈ U1ProdSet E) :
    (fun p => f p + g p) ∈ U1ProdSet E := by
  obtain ⟨ι, _, F, H, hF, hH, hfp⟩ := hf
  obtain ⟨ι', _, F', H', hF', hH', hgp⟩ := hg
  refine ⟨ι ⊕ ι', inferInstance, Sum.elim F F', Sum.elim H H', ?_, ?_, fun p => ?_⟩
  · rintro (i | i) <;> simp [hF, hF']
  · rintro (i | i) <;> simp [hH, hH']
  · simp [Fintype.sum_sum_type, hfp, hgp]

lemma u1ProdSet_mul {f g : E × E → ℝ} (hf : f ∈ U1ProdSet E) (hg : g ∈ U1ProdSet E) :
    (fun p => f p * g p) ∈ U1ProdSet E := by
  obtain ⟨ι, _, F, H, hF, hH, hfp⟩ := hf
  obtain ⟨ι', _, F', H', hF', hH', hgp⟩ := hg
  refine ⟨ι × ι', inferInstance, fun i x => F i.1 x * F' i.2 x, fun i y => H i.1 y * H' i.2 y,
    fun i => (hF i.1).mul (hF' i.2), fun i => (hH i.1).mul (hH' i.2), fun p => ?_⟩
  show f p * g p = _
  rw [hfp, hgp, Finset.sum_mul_sum, ← Finset.univ_product_univ, Finset.sum_product]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

lemma u1ProdSet_continuous {f : E × E → ℝ} (hf : f ∈ U1ProdSet E) : Continuous f := by
  obtain ⟨ι, _, F, H, hF, hH, hfp⟩ := hf
  have : f = fun p => ∑ i, F i p.1 * H i p.2 := funext hfp
  rw [this]
  refine continuous_finset_sum _ fun i _ => ?_
  exact ((hF i).continuous.comp continuous_fst).mul ((hH i).continuous.comp continuous_snd)

/-- the subalgebra of `C(E × E, ℝ)` of finite sums of products of smooth functions. -/
def u1ProdAlg (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] :
    Subalgebra ℝ C(E × E, ℝ) where
  carrier := {f | (f : E × E → ℝ) ∈ U1ProdSet E}
  mul_mem' := fun {f g} hf hg => by
    have := u1ProdSet_mul hf hg
    exact this
  add_mem' := fun {f g} hf hg => by
    have := u1ProdSet_add hf hg
    exact this
  algebraMap_mem' := fun c => u1ProdSet_const c

lemma u1ProdAlg_separates : (u1ProdAlg E).SeparatesPoints := by
  intro p q hpq
  have key : ∀ f : C(E × E, ℝ), f ∈ u1ProdAlg E → (f : E × E → ℝ) ∈ U1ProdSet E := fun f hf => hf
  by_cases h1 : p.1 = q.1
  · have h2 : p.2 ≠ q.2 := fun h2 => hpq (Prod.ext h1 h2)
    let v := p.2 - q.2
    have hv : v ≠ 0 := sub_ne_zero.mpr h2
    let f : C(E × E, ℝ) := ⟨fun z => inner ℝ v z.2, by fun_prop⟩
    refine ⟨f, ⟨f, ?_, rfl⟩, ?_⟩
    · show (f : E × E → ℝ) ∈ U1ProdSet E
      refine ⟨Unit, inferInstance, fun _ _ => 1, fun _ y => inner ℝ v y, fun _ => contDiff_const,
        fun _ => contDiff_const.inner ℝ contDiff_id, fun z => by simp [f]⟩
    · show inner ℝ v p.2 ≠ inner ℝ v q.2
      intro h
      have : inner ℝ v (p.2 - q.2) = 0 := by rw [inner_sub_right, h, sub_self]
      exact hv (inner_self_eq_zero.mp this)
  · let v := p.1 - q.1
    have hv : v ≠ 0 := sub_ne_zero.mpr h1
    let f : C(E × E, ℝ) := ⟨fun z => inner ℝ v z.1, by fun_prop⟩
    refine ⟨f, ⟨f, ?_, rfl⟩, ?_⟩
    · show (f : E × E → ℝ) ∈ U1ProdSet E
      refine ⟨Unit, inferInstance, fun _ x => inner ℝ v x, fun _ _ => 1,
        fun _ => contDiff_const.inner ℝ contDiff_id, fun _ => contDiff_const, fun z => by simp [f]⟩
    · show inner ℝ v p.1 ≠ inner ℝ v q.1
      intro h
      have : inner ℝ v (p.1 - q.1) = 0 := by rw [inner_sub_right, h, sub_self]
      exact hv (inner_self_eq_zero.mp this)

/-- Stone-Weierstrass: a continuous kernel is uniformly approximated on `closedBall R × closedBall R`
by a finite sum of products of smooth functions. -/
lemma u1_sw_approx [FiniteDimensional ℝ E] (G : E × E → ℝ) (hG : Continuous G) (R η : ℝ) (hη : 0 < η) :
    ∃ (ι : Type) (_ : Fintype ι) (F H : ι → E → ℝ), (∀ i, ContDiff ℝ ∞ (F i)) ∧
      (∀ i, ContDiff ℝ ∞ (H i)) ∧
      ∀ x y : E, ‖x‖ ≤ R → ‖y‖ ≤ R → |G (x, y) - ∑ i, F i x * H i y| < η := by
  have hK : IsCompact (closedBall (0:E) R ×ˢ closedBall (0:E) R) :=
    (isCompact_closedBall _ _).prod (isCompact_closedBall _ _)
  obtain ⟨g, hgA, hg⟩ :=
    ContinuousMap.exists_mem_subalgebra_near_continuous_of_isCompact_of_separatesPoints
      u1ProdAlg_separates ⟨G, hG⟩ hK hη
  obtain ⟨ι, hι, F, H, hF, hH, hgp⟩ := (hgA : (g : E × E → ℝ) ∈ U1ProdSet E)
  refine ⟨ι, hι, F, H, hF, hH, fun x y hx hy => ?_⟩
  have := hg (x, y) ⟨by simpa using hx, by simpa using hy⟩
  have h2 : (g : E × E → ℝ) (x, y) = ∑ i, F i x * H i y := hgp (x, y)
  rw [Real.norm_eq_abs, h2] at this
  simpa [abs_sub_comm] using this

end HRS.Whole.U1
