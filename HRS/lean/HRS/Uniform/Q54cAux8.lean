import HRS.Uniform.Q54cAux7

/-!
# Q54c, part 8: Gaussianity of the Itô sums, and of their limit

* `isum_comb_law`: every real combination `∑_a x_a · isum_a` is a centered Gaussian (it is one of the
  combinations `∑_i ⟨G_{τ_i}, y_i⟩` of `HRS.Uniform.Q07c.law_comb`).
* `isum_charFun`: the joint characteristic function of the Itô sums is `exp(-½ ∑_{ab} x_a x_b E[S_a S_b])`.
-/

noncomputable section

open MeasureTheory Filter Topology Finset ProbabilityTheory Complex
open scoped ENNReal NNReal BigOperators Matrix RealInnerProductSpace

namespace HRS.Uniform.Q54c

open HRS HRS.Uniform.Q07c

section Gauss

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {ℱ : Filtration ℝ mΩ}
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
variable {G : ℝ → Ω → H} {C : ℝ → H →L[ℝ] H →L[ℝ] ℝ} {T : ℝ}

theorem isum_comb_law (hG : IsHilbertMartingaleWithCovariation P ℱ T G (fun r _ => C r))
    (hGc : ∀ ω, Continuous fun s => G s ω) (hGz : ∀ ω, G 0 ω = 0) (hT : 0 ≤ T)
    {p : ℕ} (ts : Fin p → ℝ) (hts : ∀ a, ts a ∈ Set.Icc 0 T) (ys : Fin p → ℝ → H) (N : ℕ)
    (x : Fin p → ℝ) :
    ∃ v : ℝ, P.map (fun ω => ∑ a, x a * isum (fun σ => G σ ω) (ys a) T (ts a) N) = gaussianLaw v := by
  classical
  let ι := Fin p × Fin (N + 1) × Bool
  let τ' : ι → ℝ := fun m => if m.2.2 then min (gridPt T N ((m.2.1 : ℕ) + 1)) (ts m.1)
    else min (gridPt T N (m.2.1 : ℕ)) (ts m.1)
  let y' : ι → H := fun m => if m.2.2 then x m.1 • ys m.1 (min (gridPt T N (m.2.1 : ℕ)) (ts m.1))
    else -(x m.1 • ys m.1 (min (gridPt T N (m.2.1 : ℕ)) (ts m.1)))
  have hτ : ∀ m : ι, 0 ≤ τ' m ∧ τ' m ≤ T := by
    intro m
    have hi : (m.2.1 : ℕ) + 1 ≤ N + 1 := Nat.succ_le_succ (Nat.lt_succ_iff.1 m.2.1.2)
    have hi' : (m.2.1 : ℕ) ≤ N + 1 := (Nat.lt_succ_iff.1 m.2.1.2).trans (Nat.le_succ N)
    simp only [τ']
    split_ifs
    · exact ⟨le_min (gridPt_nonneg hT N _) (hts m.1).1, (min_le_left _ _).trans (gridPt_le hT N hi)⟩
    · exact ⟨le_min (gridPt_nonneg hT N _) (hts m.1).1, (min_le_left _ _).trans (gridPt_le hT N hi')⟩
  have heq : (fun ω => ∑ a, x a * isum (fun σ => G σ ω) (ys a) T (ts a) N) =
      comb G τ' y' T := by
    funext ω
    unfold comb
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Fintype.sum_prod_type]
    unfold isum
    rw [Finset.mul_sum, ← Fin.sum_univ_eq_sum_range (fun i => x a * inner ℝ _ _) (N + 1)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Fintype.sum_bool]
    have hi : (i : ℕ) + 1 ≤ N + 1 := Nat.succ_le_succ (Nat.lt_succ_iff.1 i.2)
    have hi' : (i : ℕ) ≤ N + 1 := (Nat.lt_succ_iff.1 i.2).trans (Nat.le_succ N)
    have h1 : min T (min (gridPt T N ((i : ℕ) + 1)) (ts a)) = min (gridPt T N ((i : ℕ) + 1)) (ts a) :=
      min_eq_right ((min_le_left _ _).trans (gridPt_le hT N hi))
    have h2 : min T (min (gridPt T N (i : ℕ)) (ts a)) = min (gridPt T N (i : ℕ)) (ts a) :=
      min_eq_right ((min_le_left _ _).trans (gridPt_le hT N hi'))
    simp only [τ', y', Bool.false_eq_true, eq_self_iff_true, ↓reduceIte, h1, h2, inner_smul_right,
      inner_neg_right, inner_sub_left]
    ring
  rw [heq]
  have hlaw := law_comb (P := P) (ℱ := ℱ) hG hT hGc hGz τ' hτ y' (A := Set.univ)
    MeasurableSet.univ (by simp)
  rw [ProbabilityTheory.cond_univ] at hlaw
  exact ⟨_, hlaw⟩

theorem isum_memLp (hG : IsHilbertMartingaleWithCovariation P ℱ T G (fun r _ => C r)) (hT : 0 ≤ T)
    {t : ℝ} (ht : t ∈ Set.Icc 0 T) (y : ℝ → H) (N : ℕ) :
    MemLp (fun ω => isum (fun σ => G σ ω) y T t N) 2 P := by
  simp_rw [isum_eq_sum]
  refine memLp_finset_sum _ fun i hi => ?_
  have hi' : i ≤ N := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
  exact memLp_incr hG hT ((min_le_left _ _).trans (gridPt_le hT N (hi'.trans (Nat.le_succ N))))
    ((min_le_left _ _).trans (gridPt_le hT N (Nat.succ_le_succ hi'))) _

theorem measurable_isum (hG : IsHilbertMartingaleWithCovariation P ℱ T G (fun r _ => C r)) (y : ℝ → H)
    (t : ℝ) (N : ℕ) : Measurable (fun ω => isum (fun σ => G σ ω) y T t N) := by
  simp_rw [isum_eq_sum]
  refine Finset.measurable_sum _ fun i _ => ?_
  unfold incrTerm
  exact (((measurable_of_isHM hG _).sub (measurable_of_isHM hG _)).inner measurable_const)

end Gauss

/-! ### Gaussian laws from characteristic functions -/

section CharFun

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P] {p : ℕ}

theorem charFun_limit {XN : ℕ → Ω → EuclideanSpace ℝ (Fin p)} {X : Ω → EuclideanSpace ℝ (Fin p)}
    (hXN : ∀ N, Measurable (XN N)) (hlim : ∀ ω, Tendsto (fun N => XN N ω) atTop (𝓝 (X ω)))
    (Q : EuclideanSpace ℝ (Fin p) → ℝ) (QN : ℕ → EuclideanSpace ℝ (Fin p) → ℝ)
    (hQ : ∀ x, Tendsto (fun N => QN N x) atTop (𝓝 (Q x)))
    (hchar : ∀ N x, charFun (P.map (XN N)) x = Complex.exp (-(QN N x : ℂ) / 2)) (x : EuclideanSpace ℝ (Fin p)) :
    charFun (P.map X) x = Complex.exp (-(Q x : ℂ) / 2) := by
  have hXm : Measurable X := measurable_of_tendsto_metrizable hXN (tendsto_pi_nhds.2 hlim)
  have e1 : charFun (P.map X) x = ∫ ω, Complex.exp (inner ℝ (X ω) (x) * Complex.I) ∂P := by
    rw [charFun_apply, integral_map hXm.aemeasurable]
    exact (by fun_prop : Continuous fun y : EuclideanSpace ℝ (Fin p) =>
      Complex.exp (inner ℝ (y) (x) * Complex.I)).aestronglyMeasurable
  have e2 : ∀ N, charFun (P.map (XN N)) x = ∫ ω, Complex.exp (inner ℝ (XN N ω) (x) * Complex.I) ∂P := by
    intro N
    rw [charFun_apply, integral_map (hXN N).aemeasurable]
    exact (by fun_prop : Continuous fun y : EuclideanSpace ℝ (Fin p) =>
      Complex.exp (inner ℝ (y) (x) * Complex.I)).aestronglyMeasurable
  have hT1 : Tendsto (fun N => ∫ ω, Complex.exp (inner ℝ (XN N ω) (x) * Complex.I) ∂P) atTop
      (𝓝 (∫ ω, Complex.exp (inner ℝ (X ω) (x) * Complex.I) ∂P)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ)) (fun N => ?_)
      (integrable_const _) (fun N => Filter.Eventually.of_forall fun ω => ?_)
      (Filter.Eventually.of_forall fun ω => ?_)
    · exact (by fun_prop : Continuous fun y : EuclideanSpace ℝ (Fin p) =>
        Complex.exp (inner ℝ (y) (x) * Complex.I)).measurable.comp (hXN N) |>.aestronglyMeasurable
    · rw [Complex.norm_exp_ofReal_mul_I]
    · exact ((by fun_prop : Continuous fun y : EuclideanSpace ℝ (Fin p) =>
        Complex.exp (inner ℝ (y) (x) * Complex.I)).tendsto (X ω)).comp (hlim ω)
  have hT2 : Tendsto (fun N => Complex.exp (-(QN N x : ℂ) / 2)) atTop (𝓝 (Complex.exp (-(Q x : ℂ) / 2))) := by
    have := (Complex.continuous_ofReal.tendsto _).comp (hQ x)
    exact ((Complex.continuous_exp.tendsto _).comp ((this.neg).div_const 2))
  rw [e1]
  refine tendsto_nhds_unique hT1 ?_
  refine hT2.congr fun N => ?_
  rw [← hchar N x, e2 N]

theorem eq_multivariateGaussian {X : Ω → EuclideanSpace ℝ (Fin p)} (hX : Measurable X)
    {S : Matrix (Fin p) (Fin p) ℝ} (hS : S.PosSemidef)
    (h : ∀ x, charFun (P.map X) x = Complex.exp (-((x ⬝ᵥ S *ᵥ x : ℝ) : ℂ) / 2)) :
    P.map X = multivariateGaussian 0 S := by
  haveI : IsProbabilityMeasure (P.map X) := (Measure.isProbabilityMeasure_map_iff hX.aemeasurable).2 inferInstance
  refine Measure.ext_of_charFun (funext fun x => ?_)
  rw [h x, charFun_multivariateGaussian hS]
  simp only [inner_zero_right, Complex.ofReal_zero, zero_mul, zero_sub, neg_div]

end CharFun

end HRS.Uniform.Q54c
