import HRS.MH.FeatureMap1

/-!
# Relocated proofs for `HRS/Energy/FeatureMap.lean`, part 2

The coordinates of `featureMap` on the positive half-lattice: `⟨Ψ(x),Ψ(y)⟩ = g(x-y)`, and the
consequences `‖Ψ(x)‖² = g(0)`, continuity, boundedness and integrability.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators RealInnerProductSpace

namespace HRS.MH.FeatureMap

open HRS HRS.StaticLimitAux

variable {d : ℕ}

theorem fm2_inner_coord {a : Lattice d → ℝ} (ha0 : ∀ k, 0 ≤ a k) (has : Summable a) (x y : Torus d) :
    inner ℝ (featureMap ha0 has x) (featureMap ha0 has y) =
      ∑' i : HalfIdx d, featCoord a i x * featCoord a i y := by
  rw [lp.inner_eq_tsum]
  refine tsum_congr fun i => ?_
  rw [RCLike.inner_apply, conj_trivial]
  exact mul_comm _ _

theorem fm2_summable_half {a : Lattice d → ℝ} (ha0 : ∀ k, 0 ≤ a k) (has : Summable a) (x y : Torus d) :
    Summable fun i : HalfIdx d => featCoord a i x * featCoord a i y := by
  refine (lp.summable_inner (featureMap ha0 has x) (featureMap ha0 has y)).congr fun i => ?_
  rw [RCLike.inner_apply, conj_trivial]
  exact mul_comm _ _

/-- The two halves of the coordinate sum, each over the positive half-lattice. -/
theorem fm2_inner_split {a : Lattice d → ℝ} (ha0 : ∀ k, 0 ≤ a k) (has : Summable a) (x y : Torus d) :
    inner ℝ (featureMap ha0 has x) (featureMap ha0 has y) =
      ∑' k : {k : Lattice d // Lattice.IsPosHalf k}, featCoord a (Sum.inl k) x * featCoord a (Sum.inl k) y
        + ∑' k : {k : Lattice d // Lattice.IsPosHalf k}, featCoord a (Sum.inr k) x * featCoord a (Sum.inr k) y := by
  rw [fm2_inner_coord ha0 has x y]
  exact Summable.tsum_sum (f := fun i : HalfIdx d => featCoord a i x * featCoord a i y)
    ((fm2_summable_half ha0 has x y).comp_injective Sum.inl_injective)
    ((fm2_summable_half ha0 has x y).comp_injective Sum.inr_injective)

/-- Per-frequency identity: the cos and sin coordinates of `k` contribute `2 a_k cos_k(x - y)`. -/
theorem fm2_term {a : Lattice d → ℝ} (ha0 : ∀ k, 0 ≤ a k) (x y : Torus d)
    (k : {k : Lattice d // Lattice.IsPosHalf k}) :
    featCoord a (Sum.inl k) x * featCoord a (Sum.inl k) y
        + featCoord a (Sum.inr k) x * featCoord a (Sum.inr k) y =
      2 * (a k.1 * Torus.cosMode k.1 (x - y)) := by
  have hsq : Real.sqrt (2 * a k.1) * Real.sqrt (2 * a k.1) = 2 * a k.1 :=
    Real.mul_self_sqrt (mul_nonneg zero_le_two (ha0 k.1))
  simp only [featCoord]
  rw [StaticLimitAux.cosMode_sub']
  linear_combination (Torus.cosMode k.1 x * Torus.cosMode k.1 y
    + Torus.sinMode k.1 x * Torus.sinMode k.1 y) * hsq

/-- The inner product of the feature map is the spectral kernel at `x - y`. -/
theorem fm2_inner_spec {a : Lattice d → ℝ} (hsym : IsSpectralSymbol a) (x y : Torus d) :
    inner ℝ (featureMap hsym.nonneg hsym.summable x) (featureMap hsym.nonneg hsym.summable y) =
      StaticLimitAux.specKernel a (x - y) := by
  have ha0 := hsym.nonneg
  have has := hsym.summable
  have hL : Summable fun k : Lattice d => a k * Torus.cosMode k (x - y) :=
    Summable.of_norm_bounded has fun k => norm_mul_cos_le ha0 k (x - y)
  have hh : Summable fun k : {k : Lattice d // Lattice.IsPosHalf k} => a k.1 * Torus.cosMode k.1 (x - y) :=
    fm1_summable_pos ha0 has (fun k => Torus.cosMode k (x - y)) (fun k => by
      have := Torus.norm_cosMode_le k (x - y)
      rwa [Real.norm_eq_abs] at this)
  have h0 : (fun k : Lattice d => a k * Torus.cosMode k (x - y)) 0 = 0 := by
    simp [hsym.zero]
  have hev : ∀ k : Lattice d, (fun k : Lattice d => a k * Torus.cosMode k (x - y)) (-k) =
      (fun k : Lattice d => a k * Torus.cosMode k (x - y)) k := by
    intro k
    show a (-k) * Torus.cosMode (-k) (x - y) = a k * Torus.cosMode k (x - y)
    rw [hsym.even k, Torus.cosMode_neg]
  have hl : Summable fun k : {k : Lattice d // Lattice.IsPosHalf k} =>
      featCoord a (Sum.inl k) x * featCoord a (Sum.inl k) y :=
    (fm2_summable_half ha0 has x y).comp_injective Sum.inl_injective
  have hr : Summable fun k : {k : Lattice d // Lattice.IsPosHalf k} =>
      featCoord a (Sum.inr k) x * featCoord a (Sum.inr k) y :=
    (fm2_summable_half ha0 has x y).comp_injective Sum.inr_injective
  have e1 : ∑' k : {k : Lattice d // Lattice.IsPosHalf k}, featCoord a (Sum.inl k) x * featCoord a (Sum.inl k) y
      + ∑' k : {k : Lattice d // Lattice.IsPosHalf k}, featCoord a (Sum.inr k) x * featCoord a (Sum.inr k) y
      = ∑' k : {k : Lattice d // Lattice.IsPosHalf k}, 2 * (a k.1 * Torus.cosMode k.1 (x - y)) := by
    rw [← Summable.tsum_add hl hr]
    exact tsum_congr fun k => fm2_term ha0 x y k
  calc _ = _ := fm2_inner_split ha0 has x y
    _ = _ := e1
    _ = 2 * ∑' k : {k : Lattice d // Lattice.IsPosHalf k}, a k.1 * Torus.cosMode k.1 (x - y) :=
        hh.tsum_mul_left 2
    _ = ∑' k, a k * Torus.cosMode k (x - y) :=
        (fm1_tsum_pair (fun k => a k * Torus.cosMode k (x - y)) hL h0 hev).symm

theorem featureMap_inner_proof : type_of% @HRS.featureMap_inner := by
  intro d a hsym x y
  exact fm2_inner_spec hsym x y

theorem featureMap_norm_sq_proof : type_of% @HRS.featureMap_norm_sq := by
  intro d a hsym x
  rw [← real_inner_self_eq_norm_sq, featureMap_inner_proof hsym x x, sub_self]

theorem continuous_featureMap_proof : type_of% @HRS.continuous_featureMap := by
  intro d a hsym
  refine StaticLimitAux.continuous_mkLp (fun x i => featCoord a i x) (featWeight a)
    (summable_featWeight hsym.summable) (fun z i => featCoord_sq_le hsym.nonneg i z) fun i => ?_
  rcases i with k | k
  · show Continuous fun z => Real.sqrt (2 * a k.1) * Torus.cosMode k.1 z
    exact continuous_const.mul (Torus.continuous_cosMode k.1)
  · show Continuous fun z => Real.sqrt (2 * a k.1) * Torus.sinMode k.1 z
    exact continuous_const.mul (Torus.continuous_sinMode k.1)

/-- `‖Ψ(x)‖ = √(g(0))` for every `x`. -/
theorem fm2_norm_eq (a : Lattice d → ℝ) (hsym : IsSpectralSymbol a) (x : Torus d) :
    ‖featureMap hsym.nonneg hsym.summable x‖ = Real.sqrt (StaticLimitAux.specKernel a 0) := by
  calc ‖featureMap hsym.nonneg hsym.summable x‖
      = Real.sqrt (‖featureMap hsym.nonneg hsym.summable x‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
    _ = Real.sqrt (StaticLimitAux.specKernel a 0) := by rw [featureMap_norm_sq_proof hsym x]

theorem bounded_featureMap_proof : type_of% @HRS.bounded_featureMap := by
  intro d a hsym
  exact ⟨Real.sqrt (StaticLimitAux.specKernel a 0), fun x => le_of_eq (fm2_norm_eq a hsym x)⟩

theorem integrable_featureMap_proof : type_of% @HRS.integrable_featureMap := by
  intro d a hsym μ _
  exact MeasureTheory.Integrable.of_bound (continuous_featureMap_proof hsym).aestronglyMeasurable
    (Real.sqrt (StaticLimitAux.specKernel a 0))
    (Filter.Eventually.of_forall fun x => le_of_eq (fm2_norm_eq a hsym x))

end HRS.MH.FeatureMap
