import HRS.MC.S7E1Aux1

/-!
# Packet `s7_E1_variance_sandwich`, file 2: Parseval for doubly centred kernels

For an orthonormal basis `e` of `L^2_0(mu)` and a measurable doubly centred kernel `k in L^2(mu x mu)`,
`sum_{i,j} (iint k e_i e_j)^2 = ||k||^2_{L^2(mu x mu)}`.  Route: one-variable Parseval
(`HilbertBasis` on `span{1, e_i}`), applied slice by slice in `y`, then to the `L^2_0` functions
`F_j(x) = int k(x,y) e_j(y) dmu(y)`, with monotone convergence to exchange sum and integral.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace

noncomputable section

namespace HRS.MC.Sec7.E1Aux2

open HRS HRS.Sec7

variable {d : ℕ} {μ : Measure (Torus d)} [IsProbabilityMeasure μ] {e : ℕ → Torus d → ℝ}

theorem e1b_inner_toLp {f g : Torus d → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    ⟪hf.toLp f, hg.toLp g⟫ = ∫ x, f x * g x ∂μ := by
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [MemLp.coeFn_toLp hf, MemLp.coeFn_toLp hg] with x h1 h2
  rw [h1, h2]
  simp [mul_comm]

theorem e1b_sq_int_le {f : Torus d → ℝ} (hf : MemLp f 2 μ) : (∫ x, f x ∂μ) ^ 2 ≤ ∫ x, f x ^ 2 ∂μ := by
  have h := ProbabilityTheory.variance_eq_sub hf
  have h0 := ProbabilityTheory.variance_nonneg f μ
  simp only [Pi.pow_apply] at h
  linarith

/-- one-variable Parseval on `L^2_0(mu)` -/
theorem e1b_parseval1 (he : IsONBL2Zero μ e) {f : Torus d → ℝ} (hf : MemLp f 2 μ)
    (h0 : ∫ x, f x ∂μ = 0) :
    HasSum (fun i => (∫ x, f x * e i x ∂μ) ^ 2) (∫ x, f x ^ 2 ∂μ) := by
  classical
  have h1 : MemLp (fun _ : Torus d => (1 : ℝ)) 2 μ := memLp_const 1
  set v : Option ℕ → Lp ℝ 2 μ := fun o => o.elim (h1.toLp _) (fun i => (he.memLp i).toLp (e i)) with hv
  have hon : Orthonormal ℝ v := by
    rw [orthonormal_iff_ite]
    intro i j
    rcases i with _ | i <;> rcases j with _ | j
    · simp only [hv, Option.elim, e1b_inner_toLp h1 h1]; simp
    · simp only [hv, Option.elim, e1b_inner_toLp h1 (he.memLp j)]
      simp [he.centered j]
    · simp only [hv, Option.elim, e1b_inner_toLp (he.memLp i) h1]
      simp [he.centered i]
    · simp only [hv, Option.elim, Option.some.injEq, e1b_inner_toLp (he.memLp i) (he.memLp j)]
      have := he.orthonormal i j
      unfold l2Inner at this
      rw [this]
  have hsp : (Submodule.span ℝ (Set.range v))ᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro y hy
    rw [Submodule.mem_orthogonal] at hy
    have hy1 := hy (v none) (Submodule.subset_span ⟨none, rfl⟩)
    have hye : ∀ i, ⟪(he.memLp i).toLp (e i), y⟫ = 0 := fun i =>
      hy (v (some i)) (Submodule.subset_span ⟨some i, rfl⟩)
    have hyy : MemLp (fun x => (y : Torus d → ℝ) x) 2 μ := Lp.memLp y
    have hyeq : hyy.toLp _ = y := Lp.toLp_coeFn y hyy
    have hyc : ∫ x, (y : Torus d → ℝ) x ∂μ = 0 := by
      have h3 := e1b_inner_toLp h1 hyy
      rw [hyeq] at h3
      have hy1' : ⟪h1.toLp _, y⟫ = 0 := hy1
      rw [hy1'] at h3
      simpa using h3.symm
    have hz := he.complete _ hyy hyc (fun i => by
      have := hye i
      rw [← hyeq, e1b_inner_toLp (he.memLp i) hyy] at this
      unfold l2Inner
      simpa [mul_comm] using this)
    exact Lp.eq_zero_iff_ae_eq_zero.2 hz
  set b := HilbertBasis.mkOfOrthogonalEqBot hon hsp with hb
  have hbv : ⇑b = v := HilbertBasis.coe_mkOfOrthogonalEqBot hon hsp
  set F : Lp ℝ 2 μ := hf.toLp f with hF
  have h1' := b.hasSum_inner_mul_inner F F
  simp only [hbv] at h1'
  have hinj : Function.Injective (some : ℕ → Option ℕ) := Option.some_injective ℕ
  have hff : ⟪F, F⟫ = ∫ x, f x ^ 2 ∂μ := by
    rw [hF, e1b_inner_toLp hf hf]; simp [sq]
  rw [hff] at h1'
  have h2 := (hinj.hasSum_iff (f := fun o => ⟪F, v o⟫ * ⟪v o, F⟫) (a := ∫ x, f x ^ 2 ∂μ) ?_).2 h1'
  · convert h2 using 2 with i
    simp only [Function.comp_apply, hv, Option.elim, hF, e1b_inner_toLp hf (he.memLp i),
      e1b_inner_toLp (he.memLp i) hf]
    rw [sq]; congr 1
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => mul_comm _ _)
  · intro o ho
    rcases o with _ | o
    · simp only [hv, Option.elim, hF, e1b_inner_toLp hf h1, e1b_inner_toLp h1 hf]; simp [h0]
    · exact absurd ⟨o, rfl⟩ ho

/-- Parseval for a doubly centred `L^2` kernel in the product basis. -/
theorem e1b_parseval2 (he : IsONBL2Zero μ e) {k : Torus d → Torus d → ℝ}
    (hm : Measurable (Function.uncurry k)) (hL2 : MemLp (Function.uncurry k) 2 (μ.prod μ))
    (hx : ∀ᵐ x ∂μ, ∫ y, k x y ∂μ = 0) (hy : ∀ᵐ y ∂μ, ∫ x, k x y ∂μ = 0) :
    HasSum (fun p : ℕ × ℕ => (∫ x, ∫ y, k x y * e p.1 x * e p.2 y ∂μ ∂μ) ^ 2)
      (∫ z : Torus d × Torus d, k z.1 z.2 ^ 2 ∂(μ.prod μ)) := by
  have Ksq : Integrable (fun z : Torus d × Torus d => k z.1 z.2 ^ 2) (μ.prod μ) := hL2.integrable_sq
  have hrow : ∀ᵐ x ∂μ, MemLp (k x) 2 μ := by
    filter_upwards [Ksq.prod_right_ae] with x hx
    exact (memLp_two_iff_integrable_sq (hm.comp measurable_prodMk_left).aestronglyMeasurable).2 hx
  set g : Torus d → ℝ := fun x => ∫ y, k x y ^ 2 ∂μ with hg
  have gint : Integrable g μ := Ksq.integral_prod_left
  have gsum : ∫ x, g x ∂μ = ∫ z : Torus d × Torus d, k z.1 z.2 ^ 2 ∂(μ.prod μ) :=
    (integral_prod _ Ksq).symm
  set F : ℕ → Torus d → ℝ := fun j x => ∫ y, k x y * e j y ∂μ with hF
  have hprodint : ∀ j, Integrable (fun z : Torus d × Torus d => k z.1 z.2 * e j z.2) (μ.prod μ) := by
    intro j
    have hej : MemLp (fun z : Torus d × Torus d => e j z.2) 2 (μ.prod μ) :=
      (he.memLp j).comp_snd μ
    exact hL2.integrable_mul hej
  have Fint : ∀ j, Integrable (F j) μ := fun j => (hprodint j).integral_prod_left
  have s1 : ∀ᵐ x ∂μ, HasSum (fun j => (F j x) ^ 2) (g x) := by
    filter_upwards [hrow, hx] with x h1 h2
    exact e1b_parseval1 he h1 h2
  have Fle : ∀ j, ∀ᵐ x ∂μ, (F j x) ^ 2 ≤ g x := by
    intro j
    filter_upwards [s1] with x hx
    exact le_hasSum hx j (fun k _ => sq_nonneg _)
  have Fmem : ∀ j, MemLp (F j) 2 μ := by
    intro j
    refine (memLp_two_iff_integrable_sq (Fint j).1).2 ?_
    refine gint.mono' ((Fint j).1.pow 2) ?_
    filter_upwards [Fle j] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact hx
  have Fcen : ∀ j, ∫ x, F j x ∂μ = 0 := by
    intro j
    have hsw : ∫ x, F j x ∂μ = ∫ y, ∫ x, k x y * e j y ∂μ ∂μ :=
      integral_integral_swap (f := fun x y => k x y * e j y) (hprodint j)
    rw [hsw]
    have : ∀ᵐ y ∂μ, ∫ x, k x y * e j y ∂μ = 0 := by
      filter_upwards [hy] with y hy
      rw [integral_mul_const, hy, zero_mul]
    rw [integral_congr_ae this]; simp
  have hFc : ∀ j, HasSum (fun i => (∫ x, F j x * e i x ∂μ) ^ 2) (∫ x, F j x ^ 2 ∂μ) :=
    fun j => e1b_parseval1 he (Fmem j) (Fcen j)
  -- sum over j
  have hsumj : HasSum (fun j => ∫ x, F j x ^ 2 ∂μ) (∫ x, g x ∂μ) := by
    have hnn : ∀ j, 0 ≤ ∫ x, F j x ^ 2 ∂μ := fun j => integral_nonneg fun x => sq_nonneg _
    rw [hasSum_iff_tendsto_nat_of_nonneg hnn]
    have hint : ∀ n : ℕ, Integrable (fun x => ∑ j ∈ Finset.range n, F j x ^ 2) μ := fun n =>
      integrable_finsetSum _ fun j _ => (Fmem j).integrable_sq
    have := integral_tendsto_of_tendsto_of_monotone hint gint
      (by
        filter_upwards with x
        intro a b hab
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hab)
          (fun j _ _ => sq_nonneg _))
      (by
        filter_upwards [s1] with x hx
        exact hx.tendsto_sum_nat)
    refine this.congr fun n => ?_
    rw [integral_finsetSum _ fun j _ => (Fmem j).integrable_sq]
  -- assemble over pairs
  set a : ℕ × ℕ → ℝ := fun p => (∫ x, F p.1 x * e p.2 x ∂μ) ^ 2 with ha
  have hsum : Summable a := by
    rw [summable_prod_of_nonneg (fun p => sq_nonneg _)]
    refine ⟨fun j => (hFc j).summable, ?_⟩
    have : (fun j => ∑' i, a (j, i)) = fun j => ∫ x, F j x ^ 2 ∂μ := by
      funext j; exact (hFc j).tsum_eq
    rw [this]; exact hsumj.summable
  have hHS : HasSum a (∫ x, g x ∂μ) := by
    have h1 := hsum.hasSum
    have h2 : HasSum (fun j => ∫ x, F j x ^ 2 ∂μ) (∑' p, a p) :=
      h1.prod_fiberwise fun j => by simpa [ha] using hFc j
    rw [hsumj.unique h2]; exact h1
  have hcoef : ∀ i j, ∫ x, F j x * e i x ∂μ = ∫ x, ∫ y, k x y * e i x * e j y ∂μ ∂μ := by
    intro i j
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [hF]
    rw [← integral_mul_const]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    ring
  rw [← gsum]
  have := (Equiv.prodComm ℕ ℕ).hasSum_iff.2 hHS
  convert this using 2 with p
  simp only [Function.comp_apply, Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap, ha, hcoef]



end HRS.MC.Sec7.E1Aux2

end
