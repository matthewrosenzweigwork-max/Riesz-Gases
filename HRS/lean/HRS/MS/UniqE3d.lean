import HRS.MS.UniqE3c

/-!
# E3 of `UniqPlan.md`, part 4: the transport term (T), algebra and splitting

* `DriftFacts b Cb`: coordinates of `b` are `C²`, `b_i` and `∂_i b_i` are `Cb`-Lipschitz, `|∂_i b_i| ≤ Cb`
  (`driftFacts_of_advecting` from `IsAdvectingDrift`, `1 ≤ m`).
* `e3_transport_exact`: for `ς ∈ C¹_c`, `z ∈ C¹`, `P = ς z`:
  `2 ∫ z ∑_i ∂_i(b_i P) = ∫ (div b · ς + b·∇ς) z²`  (one integration by parts).
* `e3_trans_split`: `fpTrans b u (η_ε * P) = ∫ z_ε ∑_i ∂_i(b_i P) - ∑_i ∫ u Rem_i`, with
  `Rem_i = [η_ε*, ∂_i b_i] P + [η_ε*, b_i] ∂_i P`.
-/

noncomputable section

open MeasureTheory Filter Topology Metric Set
open scoped ENNReal NNReal ContDiff

namespace HRS.MS.UniqE3

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MS.UniqM1 HRS.MS.UniqM2
  HRS.MS.UniqM3 HRS.MS.UniqT3 HRS.MS.UniqC3

variable {d : ℕ}

/-! ### Drift facts -/

/-- The facts about a drift `b` at a fixed time used for the transport term. -/
structure DriftFacts (b : Euc d → Euc d) (Cb : ℝ) : Prop where
  smooth : ∀ i, ContDiff ℝ 2 (fun y => b y i)
  lip0 : ∀ i x y, |b x i - b y i| ≤ Cb * ‖x - y‖
  lip1 : ∀ i x y, |D1 i (fun y => b y i) x - D1 i (fun y => b y i) y| ≤ Cb * ‖x - y‖
  d1 : ∀ i x, |D1 i (fun y => b y i) x| ≤ Cb

theorem driftFacts_of_bounds {m : ℕ} (hm : 1 ≤ m) {Cb : ℝ} {f : Euc d → Euc d}
    (hs : ContDiff ℝ ((m + 1 : ℕ) : WithTop ℕ∞) f)
    (hbdd : ∀ j : ℕ, 1 ≤ j → j ≤ m + 1 → ∀ x, ‖iteratedFDeriv ℝ j f x‖ ≤ Cb) :
    DriftFacts f Cb := by
  have hf2 : ContDiff ℝ 2 f := hs.of_le (by exact_mod_cast (by omega : 2 ≤ m + 1))
  have hf1 : ContDiff ℝ 1 f := hs.of_le (by exact_mod_cast (by omega : 1 ≤ m + 1))
  have hfd : Differentiable ℝ f := hf1.differentiable (by simp)
  have hb1 : ∀ x, ‖fderiv ℝ f x‖ ≤ Cb := fun x => by
    have := hbdd 1 le_rfl (by omega) x
    rwa [norm_iteratedFDeriv_one] at this
  have hCb0 : 0 ≤ Cb := (norm_nonneg _).trans (hb1 0)
  have hlip : ∀ x y, ‖f x - f y‖ ≤ Cb * ‖x - y‖ := fun x y => by
    have := Convex.norm_image_sub_le_of_norm_fderiv_le (f := f) (s := Set.univ) (C := Cb)
      (fun z _ => hfd z) (fun z _ => hb1 z) convex_univ (mem_univ y) (mem_univ x)
    simpa [norm_sub_rev] using this
  have hg1 : ContDiff ℝ 1 (fderiv ℝ f) := hf2.fderiv_right (m := 1) (by norm_num)
  have hgd : Differentiable ℝ (fderiv ℝ f) := hg1.differentiable (by simp)
  have hb2 : ∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ Cb := fun x => by
    have := hbdd 2 (by norm_num) (by omega) x
    rw [← norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_one] at this
    exact this
  have hlip2 : ∀ x y, ‖fderiv ℝ f x - fderiv ℝ f y‖ ≤ Cb * ‖x - y‖ := fun x y => by
    have := Convex.norm_image_sub_le_of_norm_fderiv_le (f := fderiv ℝ f) (s := Set.univ) (C := Cb)
      (fun z _ => hgd z) (fun z _ => hb2 z) convex_univ (mem_univ y) (mem_univ x)
    simpa [norm_sub_rev] using this
  have hcoord : ∀ i x, D1 i (fun y => f y i) x = (fderiv ℝ f x (EuclideanSpace.single i 1)) i := by
    intro i x
    have h1 : fderiv ℝ (fun y => f y i) x =
        (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).comp (fderiv ℝ f x) :=
      ((EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).hasFDerivAt.comp x (hfd x).hasFDerivAt).fderiv
    unfold D1
    rw [h1]
    rfl
  have hcomp : ∀ (v : Euc d) (i : Fin d), |v i| ≤ ‖v‖ := fun v i => by
    simpa [Real.norm_eq_abs] using PiLp.norm_apply_le v i
  refine ⟨fun i => (contDiff_euclidean.1 hf2) i, fun i x y => ?_, fun i x y => ?_, fun i x => ?_⟩
  · exact (hcomp _ i).trans (hlip x y)
  · rw [hcoord, hcoord, ← PiLp.sub_apply, ← sub_apply]
    refine (hcomp _ i).trans ?_
    refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
    calc ‖fderiv ℝ f x - fderiv ℝ f y‖ * ‖(EuclideanSpace.single i (1 : ℝ) : Euc d)‖
        ≤ Cb * ‖x - y‖ * 1 :=
          mul_le_mul (hlip2 x y) (by simp) (norm_nonneg _) (mul_nonneg hCb0 (norm_nonneg _))
      _ = _ := mul_one _
  · rw [hcoord]
    refine (hcomp _ i).trans ?_
    refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
    calc ‖fderiv ℝ f x‖ * ‖(EuclideanSpace.single i (1 : ℝ) : Euc d)‖ ≤ Cb * 1 :=
          mul_le_mul (hb1 x) (by simp) (norm_nonneg _) hCb0
      _ = Cb := mul_one _

theorem driftFacts_of_advecting {m : ℕ} (hm : 1 ≤ m) {Cb t : ℝ} {b : ℝ → Euc d → Euc d}
    (hb : IsAdvectingDrift m Cb t b) {σ : ℝ} (hσ : σ ∈ Icc (0 : ℝ) t) : DriftFacts (b σ) Cb := by
  refine driftFacts_of_bounds hm ?_ (fun j hj1 hjm x => hb.deriv_bdd σ hσ j hj1 hjm x)
  exact_mod_cast hb.smooth σ hσ

/-! ### The exact transport identity -/

theorem e3_zero_off {ς : Euc d → ℝ} {x : Euc d} (hx : x ∉ tsupport ς) (i : Fin d) :
    ς x = 0 ∧ D1 i ς x = 0 := by
  refine ⟨image_eq_zero_of_notMem_tsupport hx, ?_⟩
  simp [D1, e3_fderiv_eq_zero_of_notMem hx]

theorem e3_integrable_cs {ς f : Euc d → ℝ} (hςc : HasCompactSupport ς) (hf : Continuous f)
    (h0 : ∀ x, x ∉ tsupport ς → f x = 0) : Integrable f volume :=
  hf.integrable_of_hasCompactSupport (e3_hasCompactSupport_of_zero hςc.isCompact h0)

/-- One integration by parts: `∫ z ∂_i(b_i ς z) = ½ ∫ ∂_i(b_i ς) z²`. -/
theorem e3_transport_ibp {bi ς z : Euc d → ℝ} (hb : ContDiff ℝ 1 bi) (hς : ContDiff ℝ 1 ς)
    (hςc : HasCompactSupport ς) (hz : ContDiff ℝ 1 z) (i : Fin d) :
    ∫ x, z x * (D1 i bi x * (ς x * z x) + bi x * D1 i (fun y => ς y * z y) x) =
      (1 / 2) * ∫ x, (D1 i bi x * ς x + bi x * D1 i ς x) * z x ^ 2 := by
  have hbd := hb.differentiable (by simp)
  have hςd := hς.differentiable (by simp)
  have hzd := hz.differentiable (by simp)
  have cb := hb.continuous
  have cς := hς.continuous
  have cz := hz.continuous
  have cDb := e3_continuous_D1 hb i
  have cDς := e3_continuous_D1 hς i
  have cDz := e3_continuous_D1 hz i
  set Q : Euc d → ℝ := fun x => D1 i bi x * ς x + bi x * D1 i ς x with hQ
  have hQc : Continuous Q := (cDb.mul cς).add (cb.mul cDς)
  -- the IBP
  have hf1 : ContDiff ℝ 1 (fun x => bi x * ς x) := hb.mul hς
  have hg1 : ContDiff ℝ 1 (fun x => z x * z x) := hz.mul hz
  have hibp := e3_ibp hf1 hg1 (Or.inl (hςc.mul_left)) i
  have hDf : ∀ x, D1 i (fun x => bi x * ς x) x = Q x := fun x => by
    rw [e3_D1_mul hbd hςd]; simp only [hQ]; ring
  have hDg : ∀ x, D1 i (fun x => z x * z x) x = 2 * (z x * D1 i z x) := fun x => by
    rw [e3_D1_mul hzd hzd]; ring
  simp_rw [hDf, hDg] at hibp
  -- pointwise decomposition
  have hpt : ∀ x, z x * (D1 i bi x * (ς x * z x) + bi x * D1 i (fun y => ς y * z y) x) =
      Q x * z x ^ 2 + (1 / 2) * ((bi x * ς x) * (2 * (z x * D1 i z x))) := by
    intro x
    rw [e3_D1_mul hςd hzd]
    simp only [hQ]
    ring
  have i1 : Integrable (fun x => Q x * z x ^ 2) volume :=
    e3_integrable_cs hςc (hQc.mul (cz.pow 2)) (fun x hx => by
      obtain ⟨h1, h2⟩ := e3_zero_off hx i; simp [hQ, h1, h2])
  have i2 : Integrable (fun x => (bi x * ς x) * (2 * (z x * D1 i z x))) volume :=
    e3_integrable_cs hςc ((cb.mul cς).mul (continuous_const.mul (cz.mul cDz))) (fun x hx => by
      simp [(e3_zero_off hx i).1])
  simp_rw [hpt]
  rw [integral_add i1 (i2.const_mul _), integral_const_mul, hibp]
  have : ∫ x, Q x * z x ^ 2 = ∫ x, Q x * (z x * z x) := by
    refine integral_congr_ae (Eventually.of_forall fun x => ?_); simp only; ring
  rw [this]
  ring

theorem e3_transport_exact (b : Euc d → Euc d) (hbs : ∀ i, ContDiff ℝ 1 (fun y => b y i))
    {ς z : Euc d → ℝ} (hς : ContDiff ℝ 1 ς) (hςc : HasCompactSupport ς) (hz : ContDiff ℝ 1 z) :
    ∫ x, z x * ∑ i, (D1 i (fun y => b y i) x * (ς x * z x) +
        b x i * D1 i (fun y => ς y * z y) x) =
      (1 / 2) * ∫ x, ((∑ i, D1 i (fun y => b y i) x) * ς x + ∑ i, b x i * D1 i ς x) * z x ^ 2 := by
  have hint : ∀ i, Integrable (fun x => z x * (D1 i (fun y => b y i) x * (ς x * z x) +
        b x i * D1 i (fun y => ς y * z y) x)) volume := fun i => by
    refine e3_integrable_cs hςc ?_ (fun x hx => ?_)
    · have cDz := e3_continuous_D1 (hς.mul hz) i
      exact hz.continuous.mul (((e3_continuous_D1 (hbs i) i).mul (hς.continuous.mul hz.continuous)).add
        ((hbs i).continuous.mul cDz))
    · obtain ⟨h1, h2⟩ := e3_zero_off hx i
      have h3 : D1 i (fun y => ς y * z y) x = 0 := by
        rw [e3_D1_mul (hς.differentiable (by simp)) (hz.differentiable (by simp))]
        simp [h1, h2]
      simp [h1, h3]
  rw [e3_integral_mul_sum hint]
  simp_rw [e3_transport_ibp (hbs _) hς hςc hz]
  rw [← Finset.mul_sum]
  congr 1
  rw [← integral_finsetSum]
  · refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [add_mul, Finset.sum_add_distrib, Finset.sum_mul]
  · intro i _
    refine e3_integrable_cs hςc ?_ (fun x hx => ?_)
    · exact (((e3_continuous_D1 (hbs i) i).mul hς.continuous).add
        ((hbs i).continuous.mul (e3_continuous_D1 hς i))).mul (hz.continuous.pow 2)
    · obtain ⟨h1, h2⟩ := e3_zero_off hx i
      simp [h1, h2]

end HRS.MS.UniqE3
