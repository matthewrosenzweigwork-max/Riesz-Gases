import HRS.MS.SA12V4

/-!
# S.A.12 C17, the time direction

* joint continuity of the pointwise right-hand side `R(σ,x) = νΔF + ⟨b,∇F⟩ + G` of a classical solution;
* the fundamental theorem of calculus in time and a Fubini exchange against a compactly supported test.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12Construction

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MH.AdjointRd

variable {d : ℕ}

theorem sa12v_pd0 (idx : Fin 0 → Fin d) (f : Euc d → ℝ) (x : Euc d) : partialDeriv idx f x = f x := by
  unfold partialDeriv
  rw [iteratedFDeriv_zero_apply]

theorem sa12v_pd1 (f : Euc d → ℝ) (x : Euc d) (i : Fin d) :
    gradient f x i = partialDeriv (fun _ : Fin 1 => i) f x := by
  rw [sa12v_grad_coord, sa12v_partialDeriv_one]

theorem sa12v_pd2 (f : Euc d → ℝ) (x : Euc d) :
    Laplacian.laplacian f x = ∑ i : Fin d, partialDeriv (fun _ : Fin 2 => i) f x := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis f (EuclideanSpace.basisFun (Fin d) ℝ)]
  refine Finset.sum_congr rfl fun i _ => ?_
  unfold partialDeriv
  congr 1
  funext l
  fin_cases l <;> simp [EuclideanSpace.basisFun_apply]

/-- Joint continuity of the pointwise right-hand side of a classical solution. -/
theorem sa12v_R_cont {ν : ℝ} {b : ℝ → Euc d → Euc d} {G : ℝ → Euc d → ℝ} {t : ℝ}
    {F : ℝ → Euc d → ℝ} (hsol : IsClassicalSol 2 ν b G t F)
    (hbc : ContinuousOn (fun p : ℝ × Euc d => b p.1 p.2) (Icc (0 : ℝ) t ×ˢ univ)) :
    ContinuousOn (fun p : ℝ × Euc d => ν * Laplacian.laplacian (F p.1) p.2 +
      inner ℝ (b p.1 p.2) (gradient (F p.1) p.2) + G p.1 p.2) (Icc (0 : ℝ) t ×ˢ univ) := by
  have hLap : ContinuousOn (fun p : ℝ × Euc d => Laplacian.laplacian (F p.1) p.2)
      (Icc (0 : ℝ) t ×ˢ univ) := by
    simp_rw [sa12v_pd2]
    exact continuousOn_finsetSum _ fun i _ => hsol.contF 2 (fun _ => i)
  have hGrad : ∀ i : Fin d, ContinuousOn (fun p : ℝ × Euc d => gradient (F p.1) p.2 i)
      (Icc (0 : ℝ) t ×ˢ univ) := by
    intro i
    simp_rw [sa12v_pd1]
    exact hsol.contF 1 (fun _ => i)
  have hG : ContinuousOn (fun p : ℝ × Euc d => G p.1 p.2) (Icc (0 : ℝ) t ×ˢ univ) := by
    have := hsol.contG 0 (fun i => i.elim0)
    simpa [sa12v_pd0] using this
  have hInner : ContinuousOn (fun p : ℝ × Euc d => inner ℝ (b p.1 p.2) (gradient (F p.1) p.2))
      (Icc (0 : ℝ) t ×ˢ univ) := by
    have : ∀ p : ℝ × Euc d, inner ℝ (b p.1 p.2) (gradient (F p.1) p.2) =
        ∑ i : Fin d, b p.1 p.2 i * gradient (F p.1) p.2 i := by
      intro p
      rw [PiLp.inner_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp [mul_comm]
    simp_rw [this]
    refine continuousOn_finsetSum _ fun i _ => ?_
    exact (((EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).continuous.comp_continuousOn hbc)).mul (hGrad i)
  exact ((continuousOn_const.mul hLap).add hInner).add hG

/-- The fundamental theorem of calculus for a scalar function with right-continuous derivative. -/
theorem sa12v_ftc {t : ℝ} {φ r : ℝ → ℝ} (hφ : ContinuousOn φ (Icc (0 : ℝ) t))
    (hr : ContinuousOn r (Icc (0 : ℝ) t))
    (hder : ∀ τ ∈ Icc (0 : ℝ) t, HasDerivWithinAt φ (r τ) (Icc (0 : ℝ) t) τ) :
    ∀ τ ∈ Icc (0 : ℝ) t, φ τ - φ 0 = ∫ σ in (0 : ℝ)..τ, r σ := by
  intro τ hτ
  have hsub : Icc (0 : ℝ) τ ⊆ Icc (0 : ℝ) t := Icc_subset_Icc_right hτ.2
  symm
  refine intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hτ.1 (hφ.mono hsub) ?_
    ((hr.mono hsub).intervalIntegrable_of_Icc hτ.1)
  intro σ hσ
  have hσt : σ ∈ Icc (0 : ℝ) t := ⟨hσ.1.le, hσ.2.le.trans hτ.2⟩
  have hnhds : Icc (0 : ℝ) t ∈ 𝓝 σ := Icc_mem_nhds hσ.1 (lt_of_lt_of_le hσ.2 hτ.2)
  exact ((hder σ hσt).hasDerivAt hnhds).hasDerivWithinAt

/-- Slice continuity: `x ↦ R σ x` is continuous. -/
theorem sa12v_slice_cont {R : ℝ → Euc d → ℝ} {t : ℝ}
    (hRc : ContinuousOn (fun p : ℝ × Euc d => R p.1 p.2) (Icc (0 : ℝ) t ×ˢ univ)) {σ : ℝ}
    (hσ : σ ∈ Icc (0 : ℝ) t) : Continuous (R σ) := by
  have : ContinuousOn (R σ) univ := by
    have h := hRc.comp (continuous_const.prodMk continuous_id).continuousOn
      (s := (univ : Set (Euc d))) (t := Icc (0 : ℝ) t ×ˢ univ) (f := fun x : Euc d => (σ, x))
      (fun x _ => ⟨hσ, mem_univ _⟩)
    exact h
  exact continuousOn_univ.1 this

/-- Continuity of the time integrand of the weak form. -/
theorem sa12v_J_cont {R : ℝ → Euc d → ℝ} {t : ℝ}
    (hRc : ContinuousOn (fun p : ℝ × Euc d => R p.1 p.2) (Icc (0 : ℝ) t ×ˢ univ))
    {ψ : Euc d → ℝ} (hψ : IsCcInfty ψ) :
    ContinuousOn (fun σ => ∫ x, ψ x * R σ x) (Icc (0 : ℝ) t) := by
  have hK : IsCompact (tsupport ψ) := hψ.2
  obtain ⟨Bψ, hBψ⟩ := hψ.2.exists_bound_of_continuous hψ.1.continuous
  have hBψ0 : 0 ≤ Bψ := (norm_nonneg _).trans (hBψ 0)
  have hKt : IsCompact (Icc (0 : ℝ) t ×ˢ tsupport ψ) := isCompact_Icc.prod hK
  obtain ⟨BR, hBR⟩ := hKt.exists_bound_of_continuousOn
    (hRc.mono (prod_mono subset_rfl (subset_univ _)))
  have hBR0 : ∀ σ ∈ Icc (0 : ℝ) t, ∀ x ∈ tsupport ψ, ‖R σ x‖ ≤ BR := fun σ hσ x hx => hBR (σ, x) ⟨hσ, hx⟩
  refine continuousOn_of_dominated (μ := (volume : Measure (Euc d)))
    (F := fun (σ : ℝ) (x : Euc d) => ψ x * R σ x)
    (bound := (tsupport ψ).indicator (fun _ => Bψ * BR)) ?_ ?_ ?_ ?_
  · intro σ hσ
    exact (hψ.1.continuous.mul (sa12v_slice_cont hRc hσ)).aestronglyMeasurable
  · intro σ hσ
    refine Filter.Eventually.of_forall fun x => ?_
    by_cases hx : x ∈ tsupport ψ
    · rw [Set.indicator_of_mem hx, norm_mul]
      exact mul_le_mul (hBψ x) (hBR0 σ hσ x hx) (norm_nonneg _) hBψ0
    · rw [Set.indicator_of_notMem hx, image_eq_zero_of_notMem_tsupport hx, zero_mul, norm_zero]
  · exact (integrable_indicator_iff hK.measurableSet).2 (integrableOn_const hK.measure_lt_top.ne)
  · refine Filter.Eventually.of_forall fun x => ?_
    have h := hRc.comp (continuous_id.prodMk continuous_const).continuousOn
      (s := Icc (0 : ℝ) t) (t := Icc (0 : ℝ) t ×ˢ univ) (f := fun σ : ℝ => (σ, x))
      (fun σ hσ => ⟨hσ, mem_univ _⟩)
    exact continuousOn_const.mul h

/-- Fubini in space and time against a compactly supported test. -/
theorem sa12v_time_fubini {R : ℝ → Euc d → ℝ} {t : ℝ}
    (hRc : ContinuousOn (fun p : ℝ × Euc d => R p.1 p.2) (Icc (0 : ℝ) t ×ˢ univ))
    {ψ : Euc d → ℝ} (hψ : IsCcInfty ψ) {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) t) :
    ∫ x, ψ x * ∫ σ in (0 : ℝ)..τ, R σ x = ∫ σ in Icc (0 : ℝ) τ, ∫ x, ψ x * R σ x := by
  have hK : IsCompact (tsupport ψ) := hψ.2
  have hsub : Icc (0 : ℝ) τ ⊆ Icc (0 : ℝ) t := Icc_subset_Icc_right hτ.2
  set h : Euc d × ℝ → ℝ := fun q => ψ q.1 * R q.2 q.1 with hh
  have hcont : ContinuousOn h (univ ×ˢ Icc (0 : ℝ) τ) := by
    have h1 : ContinuousOn (fun q : Euc d × ℝ => R q.2 q.1) (univ ×ˢ Icc (0 : ℝ) τ) := by
      have := hRc.comp (continuous_snd.prodMk continuous_fst).continuousOn
        (s := univ ×ˢ Icc (0 : ℝ) τ) (t := Icc (0 : ℝ) t ×ˢ univ)
        (f := fun q : Euc d × ℝ => (q.2, q.1)) (fun q hq => ⟨hsub hq.2, mem_univ _⟩)
      exact this
    exact (hψ.1.continuous.comp continuous_fst).continuousOn.mul h1
  have hWc : IsCompact (tsupport ψ ×ˢ Icc (0 : ℝ) τ) := hK.prod isCompact_Icc
  have hWint : IntegrableOn h (tsupport ψ ×ˢ Icc (0 : ℝ) τ) (volume.prod volume) :=
    (hcont.mono (prod_mono (subset_univ _) subset_rfl)).integrableOn_compact hWc
  have hint : Integrable (Function.uncurry fun (x : Euc d) (σ : ℝ) => ψ x * R σ x)
      ((volume : Measure (Euc d)).prod (volume.restrict (Ioc (0 : ℝ) τ))) := by
    have e : (volume : Measure (Euc d)).prod (volume.restrict (Ioc (0 : ℝ) τ)) =
        (volume.prod volume).restrict (univ ×ˢ Ioc (0 : ℝ) τ) := by
      rw [← Measure.prod_restrict, Measure.restrict_univ]
    rw [e]
    have hsupp : ∀ q : Euc d × ℝ, q ∈ univ ×ˢ Ioc (0 : ℝ) τ → q ∉ tsupport ψ ×ˢ Icc (0 : ℝ) τ →
        h q = 0 := by
      intro q hq hq'
      have hx : q.1 ∉ tsupport ψ := fun hx => hq' ⟨hx, Ioc_subset_Icc_self hq.2⟩
      simp only [hh, image_eq_zero_of_notMem_tsupport hx, zero_mul]
    have hmeas : MeasurableSet ((univ : Set (Euc d)) ×ˢ Ioc (0 : ℝ) τ) :=
      MeasurableSet.univ.prod measurableSet_Ioc
    exact hWint.of_forall_diff_eq_zero hmeas (fun q hq => hsupp q hq.1 hq.2)
  have e1 : ∀ x, ψ x * ∫ σ in (0 : ℝ)..τ, R σ x = ∫ σ in Ioc (0 : ℝ) τ, ψ x * R σ x := by
    intro x
    rw [intervalIntegral.integral_of_le hτ.1, integral_const_mul]
  simp_rw [e1]
  rw [integral_integral_swap hint, integral_Icc_eq_integral_Ioc]

end HRS.MH.AdjointRd.Phase2SA12Construction
