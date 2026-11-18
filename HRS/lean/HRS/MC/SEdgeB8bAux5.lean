import HRS.MC.SEdgeB8bAux4

/-!
# Packet B8b, helper file 5: the law of the limiting linear statistic is Gaussian
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.SEdge.B8b

section Law2

variable {Ω : Type*} [MeasurableSpace Ω] {p : ℕ}

theorem b8b_bcf_tendsto {𝕜 : Type*} [RCLike 𝕜] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → EuclideanSpace ℝ (Fin p)} {Y : Ω → EuclideanSpace ℝ (Fin p)}
    (hX : ∀ L, Measurable (X L)) (hY : Measurable Y) (h : TendstoInMeasure P X atTop Y)
    (f : BoundedContinuousFunction (EuclideanSpace ℝ (Fin p)) 𝕜) :
    Tendsto (fun L => ∫ ω, f (X L ω) ∂P) atTop (𝓝 (∫ ω, f (Y ω) ∂P)) :=
  (tendstoInDistribution_iff_forall_integral_rclike_tendsto 𝕜 (fun L => (hX L).aemeasurable)
    hY.aemeasurable).1 (h.tendstoInDistribution (fun L => (hX L).aemeasurable)) f

/-- the bounded continuous function `x ↦ exp(i ⟨x, t⟩)` -/
def b8b_expBCF (t : EuclideanSpace ℝ (Fin p)) :
    BoundedContinuousFunction (EuclideanSpace ℝ (Fin p)) ℂ :=
  BoundedContinuousFunction.mkOfBound
    ⟨fun x => Complex.exp (↑(inner ℝ x t) * Complex.I), by fun_prop⟩ 2 (by
      intro x y
      refine (dist_le_norm_add_norm _ _).trans ?_
      simp only [ContinuousMap.coe_mk, Complex.norm_exp_ofReal_mul_I]
      norm_num)

theorem b8b_expBCF_apply (t x : EuclideanSpace ℝ (Fin p)) :
    b8b_expBCF t x = Complex.exp (↑(inner ℝ x t) * Complex.I) := rfl

theorem b8b_inMeasure_XL (P : Measure Ω) (G : ℕ → Ω → ℝ) (α : Fin p → ℕ → ℝ)
    (Lin : Fin p → Ω → ℝ) (hGm : ∀ i, Measurable (G i)) (hLinm : ∀ a, Measurable (Lin a))
    (hLin : ∀ a, Tendsto (fun L => ∫⁻ ω, ‖Lin a ω - ∑ i ∈ Finset.range L, α a i * G i ω‖ₑ ^ 2 ∂P)
      atTop (𝓝 0)) :
    TendstoInMeasure P (b8b_XL α G) atTop (fun ω => (WithLp.toLp 2 fun a => Lin a ω :
      EuclideanSpace ℝ (Fin p))) := by
  refine b8b_inMeasure_euclid fun a => ?_
  have hm : ∀ L, AEStronglyMeasurable (fun ω => Lin a ω - ∑ i ∈ Finset.range L, α a i * G i ω) P :=
    fun L => ((hLinm a).sub (Finset.measurable_sum _ fun i _ => (hGm i).const_mul _)).aestronglyMeasurable
  have h1 := b8b_eLp_tendsto hm (hLin a)
  refine tendstoInMeasure_of_tendsto_eLpNorm_of_ne_top (p := 2) (by norm_num) (by norm_num) ?_
  refine h1.congr fun L => ?_
  rw [← eLpNorm_neg]
  congr 1
  ext ω
  simp [b8b_XL]


theorem b8b_dot_eq (C : Matrix (Fin p) (Fin p) ℝ) (t : Fin p → ℝ) :
    t ⬝ᵥ C.mulVec t = ∑ a, ∑ b, t a * t b * C a b := by
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

theorem b8b_S_symm (S : ℕ → ℕ → ℝ) (hSpsd : ∀ n, (Matrix.of fun i j : Fin n => S i j).PosSemidef)
    (i j : ℕ) : S i j = S j i := by
  have h := (hSpsd (max i j + 1)).isHermitian.apply ⟨j, by omega⟩ ⟨i, by omega⟩
  simpa using h

theorem b8b_law (P : Measure Ω) [IsProbabilityMeasure P] (G : ℕ → Ω → ℝ)
    (hGm : ∀ i, Measurable (G i)) (S : ℕ → ℕ → ℝ)
    (hSpsd : ∀ n, (Matrix.of fun i j : Fin n => S i j).PosSemidef)
    (hlaw : ∀ n, law P (fun ω => (WithLp.toLp 2 fun i : Fin n => G i ω :
        EuclideanSpace ℝ (Fin n))) = multivariateGaussian 0 (Matrix.of fun i j : Fin n => S i j))
    (α : Fin p → ℕ → ℝ) (Lin : Fin p → Ω → ℝ) (hLinm : ∀ a, Measurable (Lin a))
    (hLin : ∀ a, Tendsto (fun L => ∫⁻ ω, ‖Lin a ω - ∑ i ∈ Finset.range L, α a i * G i ω‖ₑ ^ 2 ∂P)
      atTop (𝓝 0))
    (C : Matrix (Fin p) (Fin p) ℝ)
    (hC : ∀ a b, Tendsto (fun L => b8b_CL α S L a b) atTop (𝓝 (C a b))) :
    C.PosSemidef ∧ P.map (fun ω => (WithLp.toLp 2 fun a => Lin a ω : EuclideanSpace ℝ (Fin p))) =
      multivariateGaussian 0 C := by
  have hCsymmL : ∀ L a b, b8b_CL α S L a b = b8b_CL α S L b a := by
    intro L a b
    unfold b8b_CL
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    rw [b8b_S_symm S hSpsd k l]; ring
  have hCsymm : ∀ a b, C a b = C b a := by
    intro a b
    refine tendsto_nhds_unique (hC a b) ?_
    simpa [hCsymmL] using hC b a
  have hq : ∀ t : Fin p → ℝ, Tendsto (fun L => ∑ a, ∑ b, t a * t b * b8b_CL α S L a b) atTop
      (𝓝 (∑ a, ∑ b, t a * t b * C a b)) := fun t =>
    tendsto_finsetSum _ fun a _ => tendsto_finsetSum _ fun b _ => (hC a b).const_mul _
  have hqnn : ∀ t : Fin p → ℝ, 0 ≤ ∑ a, ∑ b, t a * t b * C a b := by
    intro t
    refine ge_of_tendsto (hq t) (Eventually.of_forall fun L => ?_)
    rw [← b8b_quad α S L t]
    have := (hSpsd L).dotProduct_mulVec_nonneg (fun k : Fin L => ∑ a, t a * α a k)
    simpa using this
  have hpsd : C.PosSemidef := by
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
    · ext a b
      simp [hCsymm a b]
    · simpa [b8b_dot_eq] using hqnn x
  refine ⟨hpsd, ?_⟩
  have hXm : ∀ L, Measurable (b8b_XL α G L) := fun L => by
    unfold b8b_XL
    fun_prop
  have hYm : Measurable (fun ω => (WithLp.toLp 2 fun a => Lin a ω : EuclideanSpace ℝ (Fin p))) := by
    fun_prop
  have hmeas := b8b_inMeasure_XL P G α Lin hGm hLinm hLin
  have : IsProbabilityMeasure (P.map (fun ω => (WithLp.toLp 2 fun a => Lin a ω :
      EuclideanSpace ℝ (Fin p)))) := (Measure.isProbabilityMeasure_map_iff hYm.aemeasurable).2 inferInstance
  refine Measure.ext_of_charFun (funext fun t => ?_)
  rw [charFun_multivariateGaussian hpsd, b8b_charFun_law P hYm]
  have hlim := b8b_bcf_tendsto (P := P) hXm hYm hmeas (b8b_expBCF t)
  have hlim2 : Tendsto (fun L => ∫ ω, b8b_expBCF t (b8b_XL α G L ω) ∂P) atTop
      (𝓝 (Complex.exp (↑(-(∑ a, ∑ b, t a * t b * C a b) / 2)))) := by
    have e : ∀ L, ∫ ω, b8b_expBCF t (b8b_XL α G L ω) ∂P =
        Complex.exp (↑(-(∑ a, ∑ b, t a * t b * b8b_CL α S L a b) / 2)) := fun L => by
      rw [← b8b_charFun_XL P G hGm S hSpsd hlaw α L t, b8b_charFun_law P (hXm L)]
      rfl
    simp_rw [e]
    exact (Complex.continuous_exp.tendsto _).comp
      (Complex.continuous_ofReal.tendsto _ |>.comp (((hq t).neg).div_const 2))
  have := tendsto_nhds_unique hlim hlim2
  change ∫ ω, b8b_expBCF t (WithLp.toLp 2 fun a => Lin a ω) ∂P = _
  rw [this]
  congr 1
  simp only [inner_zero_right, Complex.ofReal_zero, zero_mul, zero_sub]
  rw [b8b_dot_eq]
  push_cast
  ring

end Law2

end HRS.MC.SEdge.B8b
